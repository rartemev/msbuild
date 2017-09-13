// Copyright (c) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE file in the project root for full license information.
//-----------------------------------------------------------------------
// </copyright>
// <summary>Determines if a type is in a given assembly and loads that type. 
// This version is CLR 3.5-compatible.</summary>
//-----------------------------------------------------------------------

using System;
using System.IO;
using System.Reflection;
using System.Collections;
using System.Globalization;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Threading;

namespace Microsoft.Build.Shared
{
    /// <summary>
    /// This class is used to load types from their assemblies.
    /// </summary>
    internal class TypeLoader
    {
        #region ConcurrentDictionary
        // The following class is back-ported from .NET 4.X CoreFX library because
        // MSBuildTaskHost requires 3.5 .NET Framework. Only GetOrAdd method kept.
        internal class ConcurrentDictionary<TKey, TValue>
        {
            /// <summary>
            /// Tables that hold the internal state of the ConcurrentDictionary
            ///
            /// Wrapping the three tables in a single object allows us to atomically
            /// replace all tables at once.
            /// </summary>
            private sealed class Tables
            {
                internal readonly Node[] _buckets; // A singly-linked list for each bucket.
                internal readonly object[] _locks; // A set of locks, each guarding a section of the table.
                internal volatile int[] _countPerLock; // The number of elements guarded by each lock.

                internal Tables(Node[] buckets, object[] locks, int[] countPerLock)
                {
                    _buckets = buckets;
                    _locks = locks;
                    _countPerLock = countPerLock;
                }
            }

            private volatile Tables _tables; // Internal tables of the dictionary
            private IEqualityComparer<TKey> _comparer; // Key equality comparer
            private readonly bool _growLockArray; // Whether to dynamically increase the size of the striped lock
            private int _budget; // The maximum number of elements per lock before a resize operation is triggered

            // The default capacity, i.e. the initial # of buckets. When choosing this value, we are making
            // a trade-off between the size of a very small dictionary, and the number of resizes when
            // constructing a large dictionary. Also, the capacity should not be divisible by a small prime.
            private const int DefaultCapacity = 31;

            // The maximum size of the striped lock that will not be exceeded when locks are automatically
            // added as the dictionary grows. However, the user is allowed to exceed this limit by passing
            // a concurrency level larger than MaxLockNumber into the constructor.
            private const int MaxLockNumber = 1024;

            // Whether TValue is a type that can be written atomically (i.e., with no danger of torn reads)
            private static readonly bool s_isValueWriteAtomic = IsValueWriteAtomic();

            /// <summary>
            /// Determines whether type TValue can be written atomically
            /// </summary>
            private static bool IsValueWriteAtomic()
            {
                //
                // Section 12.6.6 of ECMA CLI explains which types can be read and written atomically without
                // the risk of tearing.
                //
                // See http://www.ecma-international.org/publications/files/ECMA-ST/Ecma-335.pdf
                //
                Type valueType = typeof(TValue);
                if (!valueType.IsValueType)
                {
                    return true;
                }

                switch (Type.GetTypeCode(valueType))
                {
                    case TypeCode.Boolean:
                    case TypeCode.Byte:
                    case TypeCode.Char:
                    case TypeCode.Int16:
                    case TypeCode.Int32:
                    case TypeCode.SByte:
                    case TypeCode.Single:
                    case TypeCode.UInt16:
                    case TypeCode.UInt32:
                        return true;
                    case TypeCode.Int64:
                    case TypeCode.Double:
                    case TypeCode.UInt64:
                        return IntPtr.Size == 8;
                    default:
                        return false;
                }
            }

            /// <summary>
            /// Initializes a new instance of the <see
            /// cref="ConcurrentDictionary{TKey,TValue}"/>
            /// class that is empty, has the default concurrency level, has the default initial capacity, and
            /// uses the default comparer for the key type.
            /// </summary>
            public  ConcurrentDictionary(IEqualityComparer<TKey> comparer = null)
            {

                int concurrencyLevel = Environment.ProcessorCount;
                int capacity = DefaultCapacity;

                // The capacity should be at least as large as the concurrency level. Otherwise, we would have locks that don't guard
                // any buckets.
                if (capacity < concurrencyLevel)
                {
                    capacity = concurrencyLevel;
                }

                object[] locks = new object[concurrencyLevel];
                for (int i = 0; i < locks.Length; i++)
                {
                    locks[i] = new object();
                }

                int[] countPerLock = new int[locks.Length];
                Node[] buckets = new Node[capacity];
                _tables = new Tables(buckets, locks, countPerLock);

                _comparer = comparer ?? EqualityComparer<TKey>.Default;
                _growLockArray = true;
                _budget = buckets.Length / locks.Length;
            }

            private bool TryGetValueInternal(TKey key, int hashcode, out TValue value)
            {
                Debug.Assert(_comparer.GetHashCode(key) == hashcode);

                // We must capture the _buckets field in a local variable. It is set to a new table on each table resize.
                Tables tables = _tables;

                int bucketNo = GetBucket(hashcode, tables._buckets.Length);

                // We can get away w/out a lock here.
                // The Volatile.Read ensures that we have a copy of the reference to tables._buckets[bucketNo].
                // This protects us from reading fields ('_hashcode', '_key', '_value' and '_next') of different instances.
                Thread.MemoryBarrier();
                Node n = tables._buckets[bucketNo];

                while (n != null)
                {
                    if (hashcode == n._hashcode && _comparer.Equals(n._key, key))
                    {
                        value = n._value;
                        return true;
                    }
                    n = n._next;
                }

                value = default(TValue);
                return false;
            }

            /// <summary>
            /// Shared internal implementation for inserts and updates.
            /// If key exists, we always return false; and if updateIfExists == true we force update with value;
            /// If key doesn't exist, we always add value and return true;
            /// </summary>
            private bool TryAddInternal(TKey key, int hashcode, TValue value, bool updateIfExists, bool acquireLock, out TValue resultingValue)
            {
                Debug.Assert(_comparer.GetHashCode(key) == hashcode);

                while (true)
                {
                    int bucketNo, lockNo;

                    Tables tables = _tables;
                    GetBucketAndLockNo(hashcode, out bucketNo, out lockNo, tables._buckets.Length, tables._locks.Length);

                    bool resizeDesired = false;
                    bool lockTaken = false;
                    try
                    {
                        if (acquireLock)
                            lockTaken = Monitor.TryEnter(tables._locks[lockNo]);

                        // If the table just got resized, we may not be holding the right lock, and must retry.
                        // This should be a rare occurrence.
                        if (tables != _tables)
                        {
                            continue;
                        }

                        // Try to find this key in the bucket
                        Node prev = null;
                        for (Node node = tables._buckets[bucketNo]; node != null; node = node._next)
                        {
                            Debug.Assert((prev == null && node == tables._buckets[bucketNo]) || prev._next == node);
                            if (hashcode == node._hashcode && _comparer.Equals(node._key, key))
                            {
                                // The key was found in the dictionary. If updates are allowed, update the value for that key.
                                // We need to create a new node for the update, in order to support TValue types that cannot
                                // be written atomically, since lock-free reads may be happening concurrently.
                                if (updateIfExists)
                                {
                                    if (s_isValueWriteAtomic)
                                    {
                                        node._value = value;
                                    }
                                    else
                                    {
                                        Node newNode = new Node(node._key, value, hashcode, node._next);
                                        if (prev == null)
                                        {
                                            Interlocked.Exchange(ref tables._buckets[bucketNo], newNode);
                                        }
                                        else
                                        {
                                            prev._next = newNode;
                                        }
                                    }
                                    resultingValue = value;
                                }
                                else
                                {
                                    resultingValue = node._value;
                                }
                                return false;
                            }
                            prev = node;
                        }

                        // The key was not found in the bucket. Insert the key-value pair.
                        Interlocked.Exchange(ref tables._buckets[bucketNo], new Node(key, value, hashcode, tables._buckets[bucketNo]));
                        checked
                        {
                            tables._countPerLock[lockNo]++;
                        }

                        //
                        // If the number of elements guarded by this lock has exceeded the budget, resize the bucket table.
                        // It is also possible that GrowTable will increase the budget but won't resize the bucket table.
                        // That happens if the bucket table is found to be poorly utilized due to a bad hash function.
                        //
                        if (tables._countPerLock[lockNo] > _budget)
                        {
                            resizeDesired = true;
                        }
                    }
                    finally
                    {
                        if (lockTaken)
                            Monitor.Exit(tables._locks[lockNo]);
                    }

                    //
                    // The fact that we got here means that we just performed an insertion. If necessary, we will grow the table.
                    //
                    // Concurrency notes:
                    // - Notice that we are not holding any locks at when calling GrowTable. This is necessary to prevent deadlocks.
                    // - As a result, it is possible that GrowTable will be called unnecessarily. But, GrowTable will obtain lock 0
                    //   and then verify that the table we passed to it as the argument is still the current table.
                    //
                    if (resizeDesired)
                    {
                        GrowTable(tables);
                    }

                    resultingValue = value;
                    return true;
                }
            }

            private static void ThrowKeyNullException()
            {
                throw new ArgumentNullException("key");
            }

            /// <summary>
            /// Adds a key/value pair to the <see cref="ConcurrentDictionary{TKey,TValue}"/>
            /// if the key does not already exist.
            /// </summary>
            /// <param name="key">The key of the element to add.</param>
            /// <param name="valueFactory">The function used to generate a value for the key</param>
            /// <exception cref="T:System.ArgumentNullException"><paramref name="key"/> is a null reference
            /// (Nothing in Visual Basic).</exception>
            /// <exception cref="T:System.ArgumentNullException"><paramref name="valueFactory"/> is a null reference
            /// (Nothing in Visual Basic).</exception>
            /// <exception cref="T:System.OverflowException">The dictionary contains too many
            /// elements.</exception>
            /// <returns>The value for the key.  This will be either the existing value for the key if the
            /// key is already in the dictionary, or the new value for the key as returned by valueFactory
            /// if the key was not in the dictionary.</returns>
            public TValue GetOrAdd(TKey key, Func<TKey, TValue> valueFactory)
            {
                if (key == null) ThrowKeyNullException();
                if (valueFactory == null) throw new ArgumentNullException(nameof(valueFactory));

                int hashcode = _comparer.GetHashCode(key);

                TValue resultingValue;
                if (!TryGetValueInternal(key, hashcode, out resultingValue))
                {
                    TryAddInternal(key, hashcode, valueFactory(key), false, true, out resultingValue);
                }
                return resultingValue;
            }

            /// <summary>
            /// Replaces the bucket table with a larger one. To prevent multiple threads from resizing the
            /// table as a result of races, the Tables instance that holds the table of buckets deemed too
            /// small is passed in as an argument to GrowTable(). GrowTable() obtains a lock, and then checks
            /// the Tables instance has been replaced in the meantime or not.
            /// </summary>
            private void GrowTable(Tables tables)
            {
                const int MaxArrayLength = 0X7FEFFFFF;
                int locksAcquired = 0;
                try
                {
                    // The thread that first obtains _locks[0] will be the one doing the resize operation
                    AcquireLocks(0, 1, ref locksAcquired);

                    // Make sure nobody resized the table while we were waiting for lock 0:
                    if (tables != _tables)
                    {
                        // We assume that since the table reference is different, it was already resized (or the budget
                        // was adjusted). If we ever decide to do table shrinking, or replace the table for other reasons,
                        // we will have to revisit this logic.
                        return;
                    }

                    // Compute the (approx.) total size. Use an Int64 accumulation variable to avoid an overflow.
                    long approxCount = 0;
                    for (int i = 0; i < tables._countPerLock.Length; i++)
                    {
                        approxCount += tables._countPerLock[i];
                    }

                    //
                    // If the bucket array is too empty, double the budget instead of resizing the table
                    //
                    if (approxCount < tables._buckets.Length / 4)
                    {
                        _budget = 2 * _budget;
                        if (_budget < 0)
                        {
                            _budget = int.MaxValue;
                        }
                        return;
                    }


                    // Compute the new table size. We find the smallest integer larger than twice the previous table size, and not divisible by
                    // 2,3,5 or 7. We can consider a different table-sizing policy in the future.
                    int newLength = 0;
                    bool maximizeTableSize = false;
                    try
                    {
                        checked
                        {
                            // Double the size of the buckets table and add one, so that we have an odd integer.
                            newLength = tables._buckets.Length * 2 + 1;

                            // Now, we only need to check odd integers, and find the first that is not divisible
                            // by 3, 5 or 7.
                            while (newLength % 3 == 0 || newLength % 5 == 0 || newLength % 7 == 0)
                            {
                                newLength += 2;
                            }

                            Debug.Assert(newLength % 2 != 0);

                            if (newLength > MaxArrayLength)
                            {
                                maximizeTableSize = true;
                            }
                        }
                    }
                    catch (OverflowException)
                    {
                        maximizeTableSize = true;
                    }

                    if (maximizeTableSize)
                    {
                        newLength = MaxArrayLength;

                        // We want to make sure that GrowTable will not be called again, since table is at the maximum size.
                        // To achieve that, we set the budget to int.MaxValue.
                        //
                        // (There is one special case that would allow GrowTable() to be called in the future:
                        // calling Clear() on the ConcurrentDictionary will shrink the table and lower the budget.)
                        _budget = int.MaxValue;
                    }

                    // Now acquire all other locks for the table
                    AcquireLocks(1, tables._locks.Length, ref locksAcquired);

                    object[] newLocks = tables._locks;

                    // Add more locks
                    if (_growLockArray && tables._locks.Length < MaxLockNumber)
                    {
                        newLocks = new object[tables._locks.Length * 2];
                        Array.Copy(tables._locks, 0, newLocks, 0, tables._locks.Length);
                        for (int i = tables._locks.Length; i < newLocks.Length; i++)
                        {
                            newLocks[i] = new object();
                        }
                    }

                    Node[] newBuckets = new Node[newLength];
                    int[] newCountPerLock = new int[newLocks.Length];

                    // Copy all data into a new table, creating new nodes for all elements
                    for (int i = 0; i < tables._buckets.Length; i++)
                    {
                        Node current = tables._buckets[i];
                        while (current != null)
                        {
                            Node next = current._next;
                            int newBucketNo, newLockNo;
                            GetBucketAndLockNo(current._hashcode, out newBucketNo, out newLockNo, newBuckets.Length, newLocks.Length);

                            newBuckets[newBucketNo] = new Node(current._key, current._value, current._hashcode, newBuckets[newBucketNo]);

                            checked
                            {
                                newCountPerLock[newLockNo]++;
                            }

                            current = next;
                        }
                    }

                    // Adjust the budget
                    _budget = Math.Max(1, newBuckets.Length / newLocks.Length);

                    // Replace tables with the new versions
                    _tables = new Tables(newBuckets, newLocks, newCountPerLock);
                }
                finally
                {
                    // Release all locks that we took earlier
                    ReleaseLocks(0, locksAcquired);
                }
            }

            /// <summary>
            /// Computes the bucket for a particular key.
            /// </summary>
            private static int GetBucket(int hashcode, int bucketCount)
            {
                int bucketNo = (hashcode & 0x7fffffff) % bucketCount;
                Debug.Assert(bucketNo >= 0 && bucketNo < bucketCount);
                return bucketNo;
            }

            /// <summary>
            /// Computes the bucket and lock number for a particular key.
            /// </summary>
            private static void GetBucketAndLockNo(int hashcode, out int bucketNo, out int lockNo, int bucketCount, int lockCount)
            {
                bucketNo = (hashcode & 0x7fffffff) % bucketCount;
                lockNo = bucketNo % lockCount;

                Debug.Assert(bucketNo >= 0 && bucketNo < bucketCount);
                Debug.Assert(lockNo >= 0 && lockNo < lockCount);
            }

            /// <summary>
            /// Acquires all locks for this hash table, and increments locksAcquired by the number
            /// of locks that were successfully acquired. The locks are acquired in an increasing
            /// order.
            /// </summary>
            private void AcquireAllLocks(ref int locksAcquired)
            {
                // First, acquire lock 0
                AcquireLocks(0, 1, ref locksAcquired);

                // Now that we have lock 0, the _locks array will not change (i.e., grow),
                // and so we can safely read _locks.Length.
                AcquireLocks(1, _tables._locks.Length, ref locksAcquired);
                Debug.Assert(locksAcquired == _tables._locks.Length);
            }

            /// <summary>
            /// Acquires a contiguous range of locks for this hash table, and increments locksAcquired
            /// by the number of locks that were successfully acquired. The locks are acquired in an
            /// increasing order.
            /// </summary>
            private void AcquireLocks(int fromInclusive, int toExclusive, ref int locksAcquired)
            {
                Debug.Assert(fromInclusive <= toExclusive);
                object[] locks = _tables._locks;

                for (int i = fromInclusive; i < toExclusive; i++)
                {
                    bool lockTaken = false;
                    try
                    {
                        lockTaken = Monitor.TryEnter(locks[i]);
                    }
                    finally
                    {
                        if (lockTaken)
                        {
                            locksAcquired++;
                        }
                    }
                }
            }

            /// <summary>
            /// Releases a contiguous range of locks.
            /// </summary>
            private void ReleaseLocks(int fromInclusive, int toExclusive)
            {
                Debug.Assert(fromInclusive <= toExclusive);

                for (int i = fromInclusive; i < toExclusive; i++)
                {
                    Monitor.Exit(_tables._locks[i]);
                }
            }

            /// <summary>
            /// A node in a singly-linked list representing a particular hash table bucket.
            /// </summary>
            private sealed class Node
            {
                internal readonly TKey _key;
                internal TValue _value;
                internal volatile Node _next;
                internal readonly int _hashcode;

                internal Node(TKey key, TValue value, int hashcode, Node next)
                {
                    _key = key;
                    _value = value;
                    _next = next;
                    _hashcode = hashcode;
                }
            }
        }
        #endregion
        /// <summary>
        /// Cache to keep track of the assemblyLoadInfos based on a given typeFilter.
        /// </summary>
        private static ConcurrentDictionary<TypeFilter, ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes>> s_cacheOfLoadedTypesByFilter = new ConcurrentDictionary<TypeFilter, ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes>>();

        /// <summary>
        /// Cache to keep track of the assemblyLoadInfos based on a given type filter for assemblies which are to be loaded for reflectionOnlyLoads.
        /// </summary>
        private static ConcurrentDictionary<TypeFilter, ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes>> s_cacheOfReflectionOnlyLoadedTypesByFilter = new ConcurrentDictionary<TypeFilter, ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes>>();

        /// <summary>
        /// Typefilter for this typeloader
        /// </summary>
        private TypeFilter _isDesiredType;

        /// <summary>
        /// Constructor.
        /// </summary>
        internal TypeLoader(TypeFilter isDesiredType)
        {
            ErrorUtilities.VerifyThrow(isDesiredType != null, "need a type filter");

            _isDesiredType = isDesiredType;
        }

        /// <summary>
        /// Given two type names, looks for a partial match between them. A partial match is considered valid only if it occurs on
        /// the right side (tail end) of the name strings, and at the start of a class or namespace name.
        /// </summary>
        /// <remarks>
        /// 1) Matches are case-insensitive.
        /// 2) .NET conventions regarding namespaces and nested classes are respected, including escaping of reserved characters.
        /// </remarks>
        /// <example>
        /// "Csc" and "csc"                                                 ==> exact match
        /// "Microsoft.Build.Tasks.Csc" and "Microsoft.Build.Tasks.Csc"     ==> exact match
        /// "Microsoft.Build.Tasks.Csc" and "Csc"                           ==> partial match
        /// "Microsoft.Build.Tasks.Csc" and "Tasks.Csc"                     ==> partial match
        /// "MyTasks.ATask+NestedTask" and "NestedTask"                     ==> partial match
        /// "MyTasks.ATask\\+NestedTask" and "NestedTask"                   ==> partial match
        /// "MyTasks.CscTask" and "Csc"                                     ==> no match
        /// "MyTasks.MyCsc" and "Csc"                                       ==> no match
        /// "MyTasks.ATask\.Csc" and "Csc"                                  ==> no match
        /// "MyTasks.ATask\\\.Csc" and "Csc"                                ==> no match
        /// </example>
        /// <returns>true, if the type names match exactly or partially; false, if there is no match at all</returns>
        internal static bool IsPartialTypeNameMatch(string typeName1, string typeName2)
        {
            bool isPartialMatch = false;

            // if the type names are the same length, a partial match is impossible
            if (typeName1.Length != typeName2.Length)
            {
                string longerTypeName;
                string shorterTypeName;

                // figure out which type name is longer
                if (typeName1.Length > typeName2.Length)
                {
                    longerTypeName = typeName1;
                    shorterTypeName = typeName2;
                }
                else
                {
                    longerTypeName = typeName2;
                    shorterTypeName = typeName1;
                }

                // if the shorter type name matches the end of the longer one
                if (longerTypeName.EndsWith(shorterTypeName, StringComparison.OrdinalIgnoreCase))
                {
                    int matchIndex = longerTypeName.Length - shorterTypeName.Length;

                    // if the matched sub-string looks like the start of a namespace or class name
                    if ((longerTypeName[matchIndex - 1] == '.') || (longerTypeName[matchIndex - 1] == '+'))
                    {
                        int precedingBackslashes = 0;

                        // confirm there are zero, or an even number of \'s preceding it...
                        for (int i = matchIndex - 2; i >= 0; i--)
                        {
                            if (longerTypeName[i] == '\\')
                            {
                                precedingBackslashes++;
                            }
                            else
                            {
                                break;
                            }
                        }

                        if ((precedingBackslashes % 2) == 0)
                        {
                            isPartialMatch = true;
                        }
                    }
                }
            }
            else
            {
                isPartialMatch = (String.Compare(typeName1, typeName2, StringComparison.OrdinalIgnoreCase) == 0);
            }

            return isPartialMatch;
        }

        /// <summary>
        /// Loads the specified type if it exists in the given assembly. If the type name is fully qualified, then a match (if
        /// any) is unambiguous; otherwise, if there are multiple types with the same name in different namespaces, the first type
        /// found will be returned.
        /// </summary>
        internal LoadedType Load
        (
            string typeName,
            AssemblyLoadInfo assembly
        )
        {
            return GetLoadedType(s_cacheOfLoadedTypesByFilter, typeName, assembly);
        }

        /// <summary>
        /// Loads the specified type if it exists in the given assembly. If the type name is fully qualified, then a match (if
        /// any) is unambiguous; otherwise, if there are multiple types with the same name in different namespaces, the first type
        /// found will be returned.
        /// </summary>
        /// <returns>The loaded type, or null if the type was not found.</returns>
        internal LoadedType ReflectionOnlyLoad
        (
            string typeName,
            AssemblyLoadInfo assembly
        )
        {
            return GetLoadedType(s_cacheOfReflectionOnlyLoadedTypesByFilter, typeName, assembly);
        }

        /// <summary>
        /// Loads the specified type if it exists in the given assembly. If the type name is fully qualified, then a match (if
        /// any) is unambiguous; otherwise, if there are multiple types with the same name in different namespaces, the first type
        /// found will be returned.
        /// </summary>
        private LoadedType GetLoadedType(ConcurrentDictionary<TypeFilter, ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes>> cache, string typeName, AssemblyLoadInfo assembly)
        {
            // A given type filter have been used on a number of assemblies, Based on the type filter we will get another dictionary which 
            // will map a specific AssemblyLoadInfo to a AssemblyInfoToLoadedTypes class which knows how to find a typeName in a given assembly.
            ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes> loadInfoToType =
                cache.GetOrAdd(_isDesiredType, (_) => new ConcurrentDictionary<AssemblyLoadInfo, AssemblyInfoToLoadedTypes>());

            // Get an object which is able to take a typename and determine if it is in the assembly pointed to by the AssemblyInfo.
            AssemblyInfoToLoadedTypes typeNameToType =
                loadInfoToType.GetOrAdd(assembly, (_) => new AssemblyInfoToLoadedTypes(_isDesiredType, _));

            return typeNameToType.GetLoadedTypeByTypeName(typeName);
        }

        /// <summary>
        /// Given a type filter and an asssemblyInfo object keep track of what types in a given assembly which match the typefilter.
        /// Also, use this information to determine if a given TypeName is in the assembly which is pointed to by the AssemblyLoadInfo object.
        /// 
        /// This type represents a combination of a type filter and an assemblyInfo object.
        /// </summary>
        private class AssemblyInfoToLoadedTypes
        {
            /// <summary>
            /// Lock to prevent two threads from using this object at the same time.
            /// Since we fill up internal structures with what is in the assembly 
            /// </summary>
            private readonly Object _lockObject = new Object();

            /// <summary>
            /// Type filter to pick the correct types out of an assembly
            /// </summary>
            private TypeFilter _isDesiredType;

            /// <summary>
            /// Assembly load information so we can load an assembly
            /// </summary>
            private AssemblyLoadInfo _assemblyLoadInfo;

            /// <summary>
            /// What is the type for the given type name, this may be null if the typeName does not map to a type.
            /// </summary>
            private ConcurrentDictionary<string, Type> _typeNameToType;

            /// <summary>
            /// List of public types in the assembly which match the typefilter and their corresponding types
            /// </summary>
            private Dictionary<string, Type> _publicTypeNameToType;

            /// <summary>
            /// Have we scanned the public types for this assembly yet.
            /// </summary>
            private long _haveScannedPublicTypes;

            /// <summary>
            /// If we loaded an assembly for this type.
            /// We use this information to set the LoadedType.LoadedAssembly so that this object can be used
            /// to help created AppDomains to resolve those that it could not load successfuly
            /// </summary>
            private Assembly _loadedAssembly;

            /// <summary>
            /// Given a type filter, and an assembly to load the type information from determine if a given type name is in the assembly or not.
            /// </summary>
            internal AssemblyInfoToLoadedTypes(TypeFilter typeFilter, AssemblyLoadInfo loadInfo)
            {
                ErrorUtilities.VerifyThrowArgumentNull(typeFilter, "typefilter");
                ErrorUtilities.VerifyThrowArgumentNull(loadInfo, "loadInfo");

                _isDesiredType = typeFilter;
                _assemblyLoadInfo = loadInfo;
                _typeNameToType = new ConcurrentDictionary<string, Type>(StringComparer.OrdinalIgnoreCase);
                _publicTypeNameToType = new Dictionary<string, Type>(StringComparer.OrdinalIgnoreCase);
            }

            /// <summary>
            /// Determine if a given type name is in the assembly or not. Return null if the type is not in the assembly
            /// </summary>
            internal LoadedType GetLoadedTypeByTypeName(string typeName)
            {
                ErrorUtilities.VerifyThrowArgumentNull(typeName, "typeName");

                if (Interlocked.Read(ref _haveScannedPublicTypes) == 0)
                {
                    lock (_lockObject)
                    {
                        if (Interlocked.Read(ref _haveScannedPublicTypes) == 0)
                        {
                            ScanAssemblyForPublicTypes();
                            _haveScannedPublicTypes = ~0;
                        }
                    }
                }

                // Only one thread should be doing operations on this instance of the object at a time.

                Type type = _typeNameToType.GetOrAdd(typeName, (key) =>
                {
                    if ((_assemblyLoadInfo.AssemblyName != null) && (typeName.Length > 0))
                    {
                        try
                        {
                            // try to load the type using its assembly qualified name
                            Type t2 = Type.GetType(typeName + "," + _assemblyLoadInfo.AssemblyName, false /* don't throw on error */, true /* case-insensitive */);
                            if (t2 != null)
                            {
                                return !_isDesiredType(t2, null) ? null : t2;
                            }
                        }
                        catch (ArgumentException)
                        {
                            // Type.GetType() will throw this exception if the type name is invalid -- but we have no idea if it's the
                            // type or the assembly name that's the problem -- so just ignore the exception, because we're going to
                            // check the existence/validity of the assembly and type respectively, below anyway
                        }
                    }

                    foreach (KeyValuePair<string, Type> desiredTypeInAssembly in _publicTypeNameToType)
                    {
                        // if type matches partially on its name
                        if (typeName.Length == 0 || TypeLoader.IsPartialTypeNameMatch(desiredTypeInAssembly.Key, typeName))
                        {
                            return desiredTypeInAssembly.Value;
                        }
                    }

                    return null;
                });

                return type != null ? new LoadedType(type, _assemblyLoadInfo, _loadedAssembly) : null;
            }

            /// <summary>
            /// Scan the assembly pointed to by the assemblyLoadInfo for public types. We will use these public types to do partial name matching on 
            /// to find tasks, loggers, and task factories.
            /// </summary>
            private void ScanAssemblyForPublicTypes()
            {
                // we need to search the assembly for the type...
                try
                {
                    if (_assemblyLoadInfo.AssemblyName != null)
                    {
                        _loadedAssembly = Assembly.Load(_assemblyLoadInfo.AssemblyName);
                    }
                    else
                    {
                        _loadedAssembly = Assembly.LoadFrom(_assemblyLoadInfo.AssemblyFile);
                    }
                }
                catch (ArgumentException e)
                {
                    // Assembly.Load() and Assembly.LoadFrom() will throw an ArgumentException if the assembly name is invalid
                    // convert to a FileNotFoundException because it's more meaningful
                    // NOTE: don't use ErrorUtilities.VerifyThrowFileExists() here because that will hit the disk again
                    throw new FileNotFoundException(null, _assemblyLoadInfo.AssemblyLocation, e);
                }

                // only look at public types
                Type[] allPublicTypesInAssembly = _loadedAssembly.GetExportedTypes();
                foreach (Type publicType in allPublicTypesInAssembly)
                {
                    if (_isDesiredType(publicType, null))
                    {
                        _publicTypeNameToType.Add(publicType.FullName, publicType);
                    }
                }
            }
        }
    }
}
