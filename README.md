# co

This is an implementation of [Abhinav Sarkar][abhinavsarkar]'s "small, interpreted language with coroutines" based on a
[blog post] he wrote demonstrating implementing this language in Haskell using the [Megaparsec][megaparsec] parser
combinator library. Here, I am Rewriting it in Rust™️ using the [Pom][pom] parser combinator library because the blog
post already demonstrates how to do this in Haskell, so might as well do this in another language I enjoy!

This is primarily serving as a way to teach myself about tree-walk interpreters, parser combinators, and how
asynchronous programming is implemented in languages like Go, Kotlin, and, of course, Rust, where asynchronous functions
suspend and resume their computation in the middle of execution to yield to another unit of execution.

I am still only currently on Part 1 of 3 of Abhinav's blog post series, so this is very much far from being done and not
that very functional.

## Building

As previously mentioned, this is written in Rust and so uses Rust's package manager and build system, Cargo. Therefore,
all you need to is clone this repository and run

```shell
cargo run
```

to run the interpreter. However, I have been focusing more on unit tests rather than functionality so you will get more
excitement out of running the unit tests with

```shell
cargo test
```

[abhinavsarkar]: https://abhinavsarkar.net/

[blog post]: https://abhinavsarkar.net/posts/implementing-co-1/

[megaparsec]: https://hackage.haskell.org/package/megaparsec-9.2.0

[pom]: https://crates.io/crates/pom