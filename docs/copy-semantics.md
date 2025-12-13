# Copy & Move Semantics

## Copies

Structs are copied under certain conditions which causes an additioanl in-place
stack allocation at the copy site. The following operations cause a copy
operation to be emited:

### 1. Assignment

```rs
fn main() {
    // a's stack memory is initialized
    let a = Foo { bar: 1 };
    
    // the fields of a are shallow copied into the stack memory of b
    let mut b = a;
    
    // b is mutated
    b.bar = 2;
    
    // a is unchanged since its value was copied
    print("{}", a.bar); // 1
    print("{}", b.bar); // 2
}
```

### 2. Function Calls

```rs
fn main() {
    // a's stack memory is initialized
    let a = Foo { bar: 1 };
    
    // a temporary stack varibale of size `sizeof(Foo)` is created and a is
    // copied into it before the pointer to this allocated memory is passed into
    // the function foo (or split across arguments for small structs)
    foo(a);
    
    // the original a is not mutated since it was copied
    print("{}", a.bar); // 1
}

fn foo(mut a: Foo) {
    // a is mutated within the scope of the function
    a.bar = 2;
}
```

## Copy Elision

Under certain situations, copies of this kind can be elided when the
`copy-elision` optimization is enabled (enabled by default in O1 or higher)

### 1. Immutable Assignment

```rs
fn main() {
    // a's stack memory is initialized
    let a = Foo { bar: 1 };
    
    // since a and b are both immutable, b can just be substituted for a and no
    // copy is performed
    let b = a;
    
    // both are unchanged
    print("{}", a.bar); // 1
    print("{}", b.bar); // 1
}
```

### 2. Immutable Function Calls

```rs
fn main() {
    // a's stack memory is initialized
    let a = Foo { bar: 1 };
    
    // since the local a is immutable and the function argument is also 
    // immutable, we can directly pass the address of a on the stack as the 
    // argument to the function instead of creating a temporary copy
    foo(a);
    
    // a is unchanged even though it was not copied
    print("{}", a.bar); // 1
}

fn foo(a: Foo) {
    // ... anything that doesnt mutate a ...
}
```
