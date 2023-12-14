---
layout: post
title:  "Smart Pointers"
categories: [C++]
description: With great flexibility comes great responsibility.
---

* TOC
{:toc}

## Motivation
> With great flexibility comes great responsibility.

Dynamic objects are the key feature of C++ that makes the language distinct with almost no lifetime rules are applied. That is to say, programs can achieve the most flexibility. But it is the programmers' responsibilities to make sure each dynamic object gets destructed **exactly** once. This might be daunting with large programs. Smart pointers, if they are used appropriately, can be a remedy for this problem. 

## Ownership Models
Each smart pointer has it's *ownership* model, which specifies the relationship with a dynamic allocated object. Informally, ownerships are, by the principle of RAII [^1], one can rest assured that the point-to objects are alive if there is an owner (a smart pointer pointing to that object). 

## Scoped Pointers
A *scoped pointer* expresses an *non-transferable*, *exclusive ownership* model. In addition, the lifetime of the a pointer is *within the nearest scope*. 
- non-transferable: The move and copy operations are not supported.
- exclusive ownership: For a dynamic object, there is at most one pointer pointing to it.
- scoped lifetime: destructed when the runtime is outside the scope.

Notice that there is no scoped pointers in *stdlib*. Until now we can find it in *boost* only. To use it, one needs to include the header of boost.

```cpp
#include <boost/smart_ptr/scoped_ptr.hpp>
```

To illustrate, it's better to have a sample class, which tracks the number of instantiated objects.

```cpp
struct Kingdom {
    Kingdom(const char* m = "")
        : message{ m } {
        number_of_kindom++;
    }
    ~Kingdom() {
        number_of_kindom--;
    }
    const char* message;
    static int number_of_kindom;
};
int Kingdom::number_of_kindom{};
using ScopedKingdom = boost::scoped_ptr<Kingdom>;
```

The unit test expresses the main features of a scoped pointer.
- The scoped pointer provides a constructor taking a raw pointer. 
- A kingdom `legolas` is destructed immediately after the scoped code block is finished.

```cpp
using ScopedKindom = boost::scoped_ptr<Kingdom>;

TEST_METHOD(Scope_Pointer)
{
    Assert::IsTrue(Kingdom::number_of_kindom == 0);
    ScopedKingdom aragorn{ new Kingdom };
    Assert::IsTrue(Kingdom::number_of_kindom == 1);
    {
        ScopedKingdom legolas{ new Kingdom };
        Assert::IsTrue(Kingdom::number_of_kindom == 2);
    }
    Assert::IsTrue(Kingdom::number_of_kindom == 1);
}
```

This example illustrates the ownership model:

```cpp
void by_ref(const ScopedKingdom&) {}
void by_val(ScopedKingdom) {}

TEST_METHOD(Scope_Pointer_Nontransferable) {
   ScopedKingdom aragorn{ new Kingdom("aragorn") };

   by_ref(aragorn);
   Assert::IsTrue(Kingdom::number_of_kindom == 1);

   // DOES NOT COMPILE
   by_val(aragorn);
   by_val(std::move(aragorn));
   auto son_of_arathorn = std::move(aragorn);
}
```

{:.note}
>The unit test framework using in this post is MS CppUnitTestFramework [^2]

All smart pointers, including scoped pointers, have two states: *empty* and *full*. A smart pointer owning no object is said to be empty, and can be converted to `false`. Conversely, a smart pointer can be converted to `true` if it owns something.

```cpp
Assert::IsTrue(aragorn.operator bool());
```

Most pointers,  including scoped pointers, have implemented the dereference `operator*` and the member dereference `operator->`

```cpp
ScopedKingdom aragorn{ new Kingdom("aragorn")};
Assert::AreEqual(aragorn->message, "aragorn");
```

The scoped pointers support compare with `nullptr`, which is yet another way to know whether it is empty.

Although move and copy are not supported, it does support a `swap` operation. By the name, it swaps the point-to objects of two scoped pointers. 

```cpp
TEST_METHOD(Scope_Pointer_Supports_Swap) {
    ScopedKingdom aragorn{ new Kingdom("aragorn") };
    Assert::AreEqual(aragorn->message, "aragorn");

    ScopedKingdom legolas{ new Kingdom("legolas") };
    Assert::AreEqual(legolas->message, "legolas");

    aragorn.swap(legolas);
    Assert::AreEqual(aragorn->message, "legolas"); 
    Assert::AreEqual(legolas->message, "aragorn");
}
```

Rarely used, operation `reset` can immediately destroy the owned objects.

Finally, for some historical reasons, it is required to use `boost::scoped_array` for dynamic arrays.

## Unique Pointers
A unique pointer has transferable, exclusive ownership over a single dynamic object. In other words, you can move unique pointers, which makes them transferable. But you cannot copy a unique pointer as well. The stdlib has a `unique_ptr` available in the `<memory>` header. Unique pointers are arguably the most commonly used smart pointers in the family.

In addition to constructors, the unique pointer has a factory function, which is more recommended:
```cpp
auto int_ptr = std::make_unique<int>(808);
```

The `make_unique` function forwards all the arguments to the appropriate constructors specified by the template parameter. I like this approach because it avoids explicitly using `new`.

```cpp
#include <memory>

using UniqueKingdom = std::unique_ptr<Kingdom>;

TEST_METHOD(Unique_Ptrs_Can_Move) {
	auto aragorn = std::make_unique<Kingdom>("aragorn");
	Assert::IsTrue(Kingdom::number_of_kindom == 1);

	auto son_of_arathorn{ std::move(aragorn) };
	Assert::IsTrue(Kingdom::number_of_kindom == 1);
	
	by_val(std::move(son_of_arathorn));
	Assert::IsTrue(Kingdom::number_of_kindom == 0);
}
```

The unique pointers have built-in support for dynamic arrays, so you can

```cpp
std::unique_ptr<int[]> unique_array { new int[5] {1, 2, 3, 4, 5} };
```

But it is very important that you don't initialize a `std::unique_ptr<T>` with a dynamic array `T[]`. Doing so will lead to undefined behavior.

### Deleters 
The `std::unique_ptr` has an optional template parameter called deleter, which get called when the pointer needs to destroy its owned object. 

```cpp
auto my_deleter = [](int* x) { delete x; };
std::unique_ptr<int, decltype(my_deleter)> my_up{ new int, my_deleter };
```

By default, the deleter is `std::default_delete<T>`, which simply calls `delete` or `delete[]` on the object. Thus, it is extremely useful when the controlled resources are more than dynamic memory.  

A good example to illustrate this is the management of `FILE` objects. The `File` is the file handle referencing to a file the OS manages. The OS requires programs to invoke `fclose` after using it, otherwise it would lead to a *resource leakage*. It is recommended to use `fclose` as the deleter as it is a function-like object.

```cpp
#include <cstdio>

using FileGuard = std::unique_ptr<FILE>;

void say_hello(FileGuard file) {
  fprintf(file.get(), "HELLO DAVE");
}

int main() {
  auto file = fopen("HAL9000", "w");
  if(!file)
    return errno;
  // use `fclose` as the deleter
  FileGuard file_guard{ file, fclose }; 
  // File open here
  say_hello(std::move(file_guard));
  // File closed here
  return 0;
}
```

## Shared Pointers
A shared pointer has transferable, non-exclusive ownership over a single dynamic object. **When a single object has been owned by multiple shared pointers, the last owner is the one to release it.**

The stdlib has a `std::shared_ptr` available in the `<memory>` header.

{:.note}
>Boost also has a `boost::shared_ptr` and it is essentially identical to `std::shared_ptr`. But the implementation in boost does not support arrays, so you should generally use the stdlib shared pointer.

The API designs of shared pointers are almost identical to those in unique pointers. Thus, it would be pedantic to give elaborated examples here. Some frequent APIs are:
- `make_shared<T>`: forwards argument to construct a shared pointer and a dynamic object.
- Dereference Operators `*`, `->` 
- `reset()`: Give up ownership or replace by a new object.
- `use_count()`:  count how many shared pointers own it.

### Control Blocks
Shared pointers require a *control block*, which is a dynamically-allocated object that keeps track of several quantities. For example:
- the number of `shared_ptr`s that own the managed object;
- the number of `weak_ptr`s that refer to the managed object.

The functionality of shared pointers relied on the correctness of the control block. When `shared_ptr` is created by calling `std::make_shared` or `std::allocate_shared`, the memory for both the control block and the managed object is **created with a single allocation**[^3]. For this sack, you should generally use `make_shared` or `allocate_shared` instead of constructors to create shared pointers.

### Allocator
In addition to the deleter, it is possible to configure the *allocator* of a `std::shared_ptr`. The default allocator `std::allocator` allocates memory from the dynamic storage. But for some historical reason, you can't use custom deleter or custom allocators in `make_share`. Instead, you are supposed to use `std::allocate_shared` for this purpose. 

This example illustrates the usage of allocator.

```cpp
static size_t n_allocated;
static size_t n_deallocated;

template <typename T>
struct MyAllocator {
    using value_type = T;

    MyAllocator() noexcept = default;
    template <typename U>
    MyAllocator(const MyAllocator<U>&) noexcept {}

    T* allocate(size_t n) {
        auto p = operator new(sizeof(T) * n);
        ++n_allocated;
        return static_cast<T*>(p);
    }

    void deallocate(T* p, size_t n) {
        operator delete(p);
        ++n_deallocated;
    }
};

TEST_CLASS(SharedPtrs) {
    TEST_METHOD(Shared_Ptrs_Support_Allocators) {
        MyAllocator<Kingdom> my_alloc;
        auto aragorn = std::allocate_shared<Kingdom>(my_alloc, "aragorn");

        by_val(std::move(aragorn));
        Assert::IsTrue(Kingdom::number_of_kindom == 0);

        Assert::IsTrue(n_allocated == 1);
        Assert::IsTrue(n_deallocated == 1);
    }
};
```

By the way, the deleters work the same way for shared pointers as they do for unique pointers.

## Weak Pointers
A weak pointer is a special kind of smart pointer that has ownership. It can be "promoted" to a shared pointer when necessary. In general, weak pointers allow you to track object and convert to a shared pointer *only if the tracked object is still alive*.

A common usage for weak pointers is *cache*, which is often temporary and programmers should provide a appropriate fallbacks when the cache is failed.

The stdlib has a `std::weak_ptr`, and Boost also has a `boost::weak_ptr`. They are used with their respective shared pointers.

The constructor of a weak pointer takes a shared pointer. To convert it to a shared pointer, invoke the `lock()` method.

```cpp
TEST_METHOD(Weak_Ptrs) {
    auto aragorn = std::make_shared<Kingdom>("aragorn");
    auto weak_refer = std::weak_ptr<Kingdom>{ aragorn };

    Assert::IsTrue(aragorn.use_count() == 1);

    auto shared_refer = weak_refer.lock();

    Assert::IsTrue(aragorn.use_count() == 2);
}
```

## Intrusive Pointers

{:.info}
>This section is here only for reminding that "there is such a pointer".

A intrusive pointer is a shared pointer to an object with an embedded reference count. For the `boost::intrusive_ptr`, every new `intrusive_ptr` instance increments the reference count by using an unqualified call to the function `intrusive_ptr_add_ref`, passing it the pointer as an argument. Similarly, when an `intrusive_ptr` is destroyed, it calls `intrusive_ptr_release`; this function is responsible for destroying the object when its reference count drops to zero.

It's rare to use an intrusive pointer. Plus, there is no standard "interface" mechanism in C++, making it even more hard to use and maintain. Unless there is a strong reason, for example, some existing frameworks or OSes provide objects with embedded reference counts, you should not consider intrusive pointers.

## References

[^1]: Resource acquisition is initialization. (2023). Retrieved from `https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization`
[^2]: TylerMSFT. (2023). Microsoft.VisualStudio.TestTools.CppUnitTestFramework API - Visual Studio (Windows). Retrieved from https://learn.microsoft.com/en-us/visualstudio/test/microsoft-visualstudio-testtools-cppunittestframework-api-reference?view=vs-2022
[^3]: `std::shared_ptr`. (2023). Retrieved from https://en.cppreference.com/w/cpp/memory/shared\_ptr