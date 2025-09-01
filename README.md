# Formalizing Higher-Order Logic in Lean

This project aims to formalize Higher-Order Logic (HOL) using the Lean theorem prover. Higher-Order Logic is a powerful and expressive framework for reasoning about mathematics, computer science, and beyond. By leveraging Lean's capabilities, we aim to create a robust and reusable library for HOL.

## Project Structure

- `HOL.lean`: The main entry point for the project.
- `lakefile.toml`: Configuration file for the Lean project.
- `lean-toolchain`: Specifies the Lean version used.
- `HOL/`
  - `Basic.lean`: Foundational definitions and theorems.
  - `Section_5_3.lean`: Formalization of concepts from Section 5.3.
  - `Section_7_1.lean`: Formalization of concepts from Section 7.1.

## Getting Started

### Prerequisites

- [Lean](https://leanprover.github.io/) theorem prover
- [Lake](https://github.com/leanprover/lake) build tool

### Installation

1. Clone the repository:
   ```bash
   git clone https://github.com/Sundayyh/HOL-in-Lean.git
   cd HOL-in-Lean
   ```
2. Ensure you have the correct Lean version installed:
   ```bash
   lake env lean --version
   ```
3. Build the project:
   ```bash
   lake build
   ```

## Usage

Open any of the `.lean` files in your favorite Lean editor (e.g., VS Code with the Lean extension) to explore the formalizations. You can also run proofs and check theorems interactively.

## Contributing

Contributions are welcome! If you'd like to contribute:

1. Fork the repository.
2. Create a new branch for your feature or bugfix.
3. Submit a pull request.

## Acknowledgments

- The Lean community for their support and tools.
- Authors and researchers in Higher-Order Logic for foundational work.