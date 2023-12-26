---
layout: post
title:  "Containers"
categories: [C++]
description: Abstract Interface and Data Structure
tags: [C++]
---

* TOC
{:toc}

A *container* is a special data structure provided in the *standard template library (STL)*. There are three kinds of containers:
- *Sequential* containers store elements consecutively in the memory. 
- *Associative* containers store sorted elements by their keys
- *Unordered associative* containers store hashed object by their keys

## Sequential Containers
### Arrays
The STL provides `std:array` in the `<array>` header. The underlying storage model of `std:array` is just fixed-length array, thus, the `std:array` is virtually a wrapper for the C-style arrays. 

```cpp
TEST(Array, DefaultInitialize) {
    std::array<int, 10> local_array;
    EXPECT_TRUE(local_array[0] != 0);
}

TEST(Array, Initialize) {
    std::array<int, 10> local_array{ 1, 1, 2, 3 };
    EXPECT_TRUE(local_array[0] == 1);
    EXPECT_TRUE(local_array[1] == 1);
    EXPECT_TRUE(local_array[2] == 2);
    EXPECT_TRUE(local_array[3] == 3);
    EXPECT_TRUE(local_array[4] == 0);
}
```

it's a good practice to use `array` instead of C-style array virtually all situations for two reasons:
- It supports virtually all the same usage patterns as operator `[]`, plus some useful helper methods. e.g. `array.size()` returns the size of the array; `array.empty()` tells if the array's size is zero. 
- For some situations that require data to be in C-style arrays - for example, functions that declare a pointer to array as a parameter - it's convenient to use `array.data()` to get the pointers.

```cpp
std::array<char, 9> color{ 'o', 'c', 't', 'a', 'r', 'i', 'n', 'e' };
const auto* color_ptr = color.data();

EXPECT_TRUE(*color_ptr == 'o')
```

An `array` does not allocate dynamic memory, rather, it keeps all its elements. The copy and move operation would generally be expensive. 

#### Iterators
**All** STL containers have built-in *iterators*, including `array`s. It is a great advantages to conventional C-style arrays. Iterators allow algorithms to explore the container from the beginning to the end, without considering the data structure and implementation of the container.

To be more specific, an iterator supports at least the following operations:
- Get the current element by operator `*`
- Go to the next element by operator `++`
- Assign an iterator to another one by operator `=`

The uniforms way to get iterators from all STL containers:
- `begin()` gets the iterator pointing to the beginning of the data.
- `end()` gets the iterator pointing **after** the last element. The design is called a *half-open range*.

The design of half-open range has some advantages. For example, one can always check if the container is empty by test if `begin()` returns the same value as `end()` 

```cpp
std::array<int, 0> fib{};
EXPECT_TRUE(fib.begin() == fib.end());
```

Another advantage of half-open range is that it fits into C++'s range expression

```cpp
std::array<int, 5> fib{ 1, 1, 2, 3, 5 };
int sum{};
for(auto element : fib) {
	sum += element;
}
EXPECT_TRUE(sum == 12);
```

### Vectors
The `std::vector` is a sequential container with dynamic size, or it is a *dynamic array*[^1]. In many programming languages like JavaScript and Python, this is the basic case of sequential data structures. In practices, the vector is the most commonly used container in STL.

If you have fixed number of elements, it is recommended to use `array`. Otherwise, The `vector` is your choice.

```cpp
std::vector<const char*> codebreakers; // default constructor

std::vector<int> fib{ 1, 1, 2, 3, 5 }; // braced constructor

// contructed by iterators
std::array<int, 5> fib_arr{ 1, 1, 2, 3, 5 };
std::vector<int> fib_vec(fib_arr.begin(), fib_arr.end()); 
```

The vector stores element in dynamic memory. It supports an allocator type as an optional template parameter. By default, it uses the `std::allocator<T>`, which manages memory by the operators `new` and `delete`.

Since the vector is implemented as a dynamic array, the copy operation can be very expensive, but the move operation is usually very fast.

Allocations are expensive. As the size of the vector grows, the vector will request additional memory and move all current elements to the new space when the capacity cannot handle all the elements. Luckily, there is a way to optimize it: If you know ahead of time how many elements could be there, you can use the `reserve` method to allocate the capacity.

Inserting at any position except the tail of a vector could be expensive, for it need to move elements around to make space.

### Niche Sequential Containers
The `std::deque` serves as a double-end queue. It doesn't guarantees that all elements are sequential in memory. Instead, it is usually scattered about. 

The `std::list` is a doubly linked list. Insertions are way cheaper than that of vectors. You should consider using `list` if there're frequent insertions. 

The `std::stack` and `std::queue` serve as the classical data structures stack and queue respectively. 

The `std::priority_queue` is a heap that keeps elements sorted. 

## Associative Containers
Associative containers, in general, are designed for fast element search. On the other hand, sequential containers are used for consecutive access. Three properties can be used to describe associative containers:
- Whether elements contain only keys or key-value pairs
- Whether they are *ordered*
- Whether the container allows non-*unique* keys

You use these two properties to select which container is appropriate.
### Sets
The `std::set` contains *ordered*, *unique* keys. The class template `set<T, Comparator, Allocator>` accepts three parameters: a key type, a comparator, and an allocator.

```cpp
std::set<int> emp;
std::set<int> fib{ 1, 1, 2, 3, 5 };

EXPECT_TRUE(emp.empty());
EXPECT_TRUE(fib.size() == 4);
```

The most common way to access an element is to use `set.find()`. Besides that, since the set is ordered, it is acceptable to use `lower_bound` or `upper_bound` to find elements in a specific range. All of these access methods return an iterator.

```cpp
std::set<int> fib{ 1, 1, 2, 3, 5 };

EXPECT_TRUE(fib.count(3) == 1);
EXPECT_TRUE(fib.count(100) == 0);

auto itr = fib.lower_bound(3);
EXPECT_TRUE(*itr == 3);
```

To add elements into the set, you could use `insert`, `emplace` or `emplace_hint`. The `emplace_hint` accepts an iterator which indicates the search start point (a hint). A notable speedup would be gained if you can give the right hint.

The underlying data structure for the set is the red-black tree, which support incredibly fast searching and inserting[^2].  

### Multisets and Unordered Sets
As the name suggests, the `std::multiset` contains *sorted, non-unique* keys. It supports almost the same operation as a set. You might want to use a multiset if it is important to record the times that a element is inserted. The multiset is also implemented as a red-black tree.

The `std::unordered_set` is available for *unsorted, unique* keys. The methods it supports are similar to those of a set, but the implementation is usually a hash table, rather than a red-black tree. It is even faster than a set in the aspect of searching on average, but with a extremely small possibilities to case a hash collision [^3].  

The STL provides a hasher class template `std::hash<T>`.

### Maps
The `std::map` represents another family of commonly used associative containers that store key-value pairs.  

The class template `map<Key, Value, Comparator, Allocator>` suggests that there are four parameters available, in which only first two are required.

```cpp
std::map<const char*, int> emp;
EXPECT_TRUE(emp.empty());

std::map<const char*, int> pub_year{
      { colour_of_magic, 1983 },
      { the_light_fantastic, 1986 },
      { equal_rites, 1987 },
      { mort, 1987 },
    };
EXPECT_TRUE(pub_year.size() == 4);
```

The common practice for maps is to use it as a *associative array*, or a *dictionary*, which is a collection of key-value pairs with each key can appear at most once in the collection. An associative array supports three elementary operations: 'lookup', 'remove' and 'insert'.

The implementation of a map is usually a red-black tree.

### Multimaps and Unordered Maps

Like the set, there are also corresponding variants for maps to support non-unique and unordered keys. They are the `std::multimap` and `std::unordered_map`. There is not really much to say about them.

## Niche Containers

### Graphs
The Boost Graph Library (BGL) provides a set of containers for storing and manipulating graphs. Worth mentioning that the abstract interface of BGL is not the same with that of STL, for the intrinsic complexity of traversing a graph is much harder. 

![Graph Example](https://www.boost.org/doc/libs/1_75_0/libs/graph/doc/figs/quick_start.gif)

For more information about BGL, visit [A Quick Tour of the Boost Graph Library](https://www.boost.org/doc/libs/1_75_0/libs/graph/doc/quick_tour.html)

### Property Trees
A property tree is a tree structure with each leave storing a piece of associated data. It is often used to represent tree-like data including JSON and XML.

The `boost::property_tree` provides an implementation of property trees. Besides, it also includes some parsing and transformation methods. For example, the methods `read_json` and `write_json` in `<boost/property_tree/json_parser>` can be handy when you try to manipulate JSON in C++. 

For more information, visit [Boost.PropertyTree](https://www.boost.org/doc/libs/1_61_0/doc/html/property_tree.html)

## Reference
[^1]: Dynamic array. (2023). Retrieved from https://en.wikipedia.org/wiki/Dynamic_array
[^2]: Red–black tree. (2023). Retrieved from https://en.wikipedia.org/wiki/Red%E2%80%93black_tree
[^3]: Hash table. (2023). Retrieved from https://en.wikipedia.org/wiki/Hash_table
