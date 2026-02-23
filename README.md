# Idem

Idem is a functional programming language designed for defining and working with **idempotent functions**. It provides a unique approach to computation by leveraging the mathematical property of idempotence ($f(f(x)) = f(x)$) through the composition of isomorphisms and base idempotent transformations.

## Features

- **Idempotent Function Definition**: Define idempotent functions using the `idem` keyword and the `with` operator.
- **Reversible Isomorphisms**: Define reversible transformations (isomorphisms) using the `iso` keyword and the `<->` operator.
- **Automatic Inversion**: Isomorphisms can be automatically inverted using `inv`.
- **Compositional Idempotency**: Create complex idempotent functions by composing isomorphisms with simpler idempotent operations.
- **Type Inference**: Built-in type system for both isomorphisms and idempotent functions.

## How it Works

In Idem, any idempotent function $f$ can be expressed in the form:
$$f(x) = \omega^{-1}(\gamma(\omega(x)))$$
where $\omega$ is an isomorphism and $\gamma$ is a base idempotent function. The `with` keyword in Idem facilitates this exact construction:
```ocaml
idem f = omega with gamma
```

## Installation

1.  Clone the repository:
    ```bash
    git clone https://github.com/ryu-mtda/idem.git
    cd idem
    ```

2.  Build the project using Dune:
    ```bash
    dune build
    ```

## Usage

To run an Idem program:

```bash
dune exec idem -- path/to/program.idem
```

## Example: Idempotent Addition

This example from `src/idem.idem` shows how to define an idempotent function using an isomorphism for addition:

```ocaml
type nat = Z | S of nat

(* Define an isomorphism for addition: add(m, n) = (m+n, n) *)
iso rec add = case
| (m, Z)   <-> (m, Z)
| (m, S n) <-> let (m, n) = add (S m, n) in (m, S n)
in

(* Define an idempotent function f(x, y) = add_inv(gamma(add(x, y)))
   where gamma(x, y) = (x, x) *)
idem f = add with (x, y) -> (x, x)
in

(* f(2, 4) will evaluate to (0, 6)
   f(0, 6) will evaluate to (0, 6) *)
f (2, 4)
```

## Project Structure

-   `bin/`: Core implementation of the Idem language (lexer, parser, evaluator, type inference).
-   `src/`: Example programs and library definitions.
-   `test/`: Test suite for the language.
