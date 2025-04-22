# Crate Documentation

**Version:** 0.2.0

**Format Version:** 45

# Module `pumpkin_solver`

# Pumpkin
Pumpkin is a combinatorial optimisation solver developed by the ConSol Lab at TU Delft. It is
based on the (lazy clause generation) constraint programming paradigm.

Our goal is to keep the solver efficient, easy to use, and well-documented. The solver is
written in pure Rust and follows Rust best practices.

A unique feature of Pumpkin is that it can produce a _certificate of unsatisfiability_. See [our CP’24 paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2024.11) for more details.

The solver currently supports integer variables and a number of (global) constraints:
* [Cumulative global constraint][crate::constraints::cumulative].
* [Element global constraint][crate::constraints::element].
* Arithmetic constraints: [linear integer
  (in)equalities][crate::constraints::less_than_or_equals], [integer
  division][crate::constraints::division], [integer multiplication][crate::constraints::times],
  [maximum][crate::constraints::maximum], [absolute value][crate::constraints::absolute].
* [Clausal constraints][Solver::add_clause].

We are actively developing Pumpkin and would be happy to hear from you should you have any
questions or feature requests!

 # Using Pumpkin
Pumpkin can be used to solve a variety of problems. The first step to solving a problem is
**adding variables**:
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::OptimisationResult;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::ProblemSolution;
# use pumpkin_solver::constraints::Constraint;
# use std::cmp::max;
// We create the solver with default options
let mut solver = Solver::default();

// We create 3 variables
let x = solver.new_bounded_integer(5, 10);
let y = solver.new_bounded_integer(-3, 15);
let z = solver.new_bounded_integer(7, 25);
```

Then we can **add constraints** supported by the [`Solver`]:
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::OptimisationResult;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::ProblemSolution;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
# use std::cmp::max;
# let mut solver = Solver::default();
# let x = solver.new_bounded_integer(5, 10);
# let y = solver.new_bounded_integer(-3, 15);
# let z = solver.new_bounded_integer(7, 25);
// We create the constraint:
// - x + y + z = 17
solver
    .add_constraint(constraints::equals(vec![x, y, z], 17))
    .post();
```

For finding a solution, a [`TerminationCondition`] and a [`Brancher`] should be specified, which
determine when the solver should stop searching and the variable/value selection strategy which
should be used:
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::termination::Indefinite;
# let mut solver = Solver::default();
// We create a termination condition which allows the solver to run indefinitely
let mut termination = Indefinite;
// And we create a search strategy (in this case, simply the default)
let mut brancher = solver.default_brancher();
```


**Finding a solution** to this problem can be done by using [`Solver::satisfy`]:
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::SatisfactionResult;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::ProblemSolution;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
# use std::cmp::max;
# let mut solver = Solver::default();
# let x = solver.new_bounded_integer(5, 10);
# let y = solver.new_bounded_integer(-3, 15);
# let z = solver.new_bounded_integer(7, 25);
# solver.add_constraint(constraints::equals(vec![x, y, z], 17)).post();
# let mut termination = Indefinite;
# let mut brancher = solver.default_brancher();
// Then we find a solution to the problem
let result = solver.satisfy(&mut brancher, &mut termination);

if let SatisfactionResult::Satisfiable(solution) = result {
    let value_x = solution.get_integer_value(x);
    let value_y = solution.get_integer_value(y);
    let value_z = solution.get_integer_value(z);

    // The constraint should hold for this solution
    assert!(value_x + value_y + value_z == 17);
} else {
    panic!("This problem should have a solution")
}
```

**Optimizing an objective** can be done in a similar way using [`Solver::optimise`]; first the
objective variable and a constraint over this value are added:

```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
# let mut solver = Solver::default();
# let x = solver.new_bounded_integer(5, 10);
# let y = solver.new_bounded_integer(-3, 15);
# let z = solver.new_bounded_integer(7, 25);
// We add another variable, the objective
let objective = solver.new_bounded_integer(-10, 30);

// We add a constraint which specifies the value of the objective
solver
    .add_constraint(constraints::maximum(vec![x, y, z], objective))
    .post();
```

Then we can find the optimal solution using [`Solver::optimise`]:
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::OptimisationResult;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::ProblemSolution;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
# use pumpkin_solver::optimisation::OptimisationDirection;
# use pumpkin_solver::optimisation::linear_sat_unsat::LinearSatUnsat;
# use std::cmp::max;
# use crate::pumpkin_solver::optimisation::OptimisationProcedure;
# use pumpkin_solver::results::SolutionReference;
# use pumpkin_solver::DefaultBrancher;
# let mut solver = Solver::default();
# let x = solver.new_bounded_integer(5, 10);
# let y = solver.new_bounded_integer(-3, 15);
# let z = solver.new_bounded_integer(7, 25);
# let objective = solver.new_bounded_integer(-10, 30);
# solver.add_constraint(constraints::equals(vec![x, y, z], 17)).post();
# solver.add_constraint(constraints::maximum(vec![x, y, z], objective)).post();
# let mut termination = Indefinite;
# let mut brancher = solver.default_brancher();
// Then we solve to optimality
let callback: fn(&Solver, SolutionReference, &DefaultBrancher) = |_, _, _| {};
let result = solver.optimise(
    &mut brancher,
    &mut termination,
    LinearSatUnsat::new(OptimisationDirection::Minimise, objective, callback),
);

if let OptimisationResult::Optimal(optimal_solution) = result {
    let value_x = optimal_solution.get_integer_value(x);
    let value_y = optimal_solution.get_integer_value(y);
    let value_z = optimal_solution.get_integer_value(z);
    // The maximum objective values is 7;
    // with one possible solution being: {x = 5, y = 5, z = 7, objective = 7}.

    // We check whether the constraint holds again
    assert!(value_x + value_y + value_z == 17);
    // We check whether the newly added constraint for the objective value holds
    assert!(
        max(value_x, max(value_y, value_z)) == optimal_solution.get_integer_value(objective)
    );
    // We check whether this is actually an optimal solution
    assert_eq!(optimal_solution.get_integer_value(objective), 7);
} else {
    panic!("This problem should have an optimal solution")
}
```

# Obtaining multiple solutions
Pumpkin supports obtaining multiple solutions from the [`Solver`] when solving satisfaction
problems. The same solution is prevented from occurring multiple times by adding blocking
clauses to the solver which means that after iterating over solutions, these solutions will
remain blocked if the solver is used again.
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::SatisfactionResult;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::ProblemSolution;
# use pumpkin_solver::results::solution_iterator::IteratedSolution;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
// We create the solver with default options
let mut solver = Solver::default();

// We create 3 variables with domains within the range [0, 2]
let x = solver.new_bounded_integer(0, 2);
let y = solver.new_bounded_integer(0, 2);
let z = solver.new_bounded_integer(0, 2);

// We create the all-different constraint
solver.add_constraint(constraints::all_different(vec![x, y, z])).post();

// We create a termination condition which allows the solver to run indefinitely
let mut termination = Indefinite;
// And we create a search strategy (in this case, simply the default)
let mut brancher = solver.default_brancher();

// Then we solve to satisfaction
let mut solution_iterator = solver.get_solution_iterator(&mut brancher, &mut termination);

let mut number_of_solutions = 0;

// We keep track of a list of known solutions
let mut known_solutions = Vec::new();

loop {
    match solution_iterator.next_solution() {
        IteratedSolution::Solution(solution, _, _) => {
            number_of_solutions += 1;
            // We have found another solution, the same invariant should hold
            let value_x = solution.get_integer_value(x);
            let value_y = solution.get_integer_value(y);
            let value_z = solution.get_integer_value(z);
            assert!(x != y && x != z && y != z);

            // It should also be the case that we have not found this solution before
            assert!(!known_solutions.contains(&(value_x, value_y, value_z)));
            known_solutions.push((value_x, value_y, value_z));
        }
        IteratedSolution::Finished => {
            // No more solutions exist
            break;
        }
        IteratedSolution::Unknown => {
            // Our termination condition has caused the solver to terminate
            break;
        }
        IteratedSolution::Unsatisfiable => {
            panic!("Problem should be satisfiable")
        }
    }
}
// There are six possible solutions to this problem
assert_eq!(number_of_solutions, 6)
 ```

# Obtaining an unsatisfiable core
Pumpkin allows the user to specify assumptions which can then be used to extract an
unsatisfiable core (see [`UnsatisfiableUnderAssumptions::extract_core`]).
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::SatisfactionResultUnderAssumptions;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::predicate;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
// We create the solver with default options
let mut solver = Solver::default();

// We create 3 variables with domains within the range [0, 2]
let x = solver.new_bounded_integer(0, 2);
let y = solver.new_bounded_integer(0, 2);
let z = solver.new_bounded_integer(0, 2);

// We create the all-different constraint
solver.add_constraint(constraints::all_different(vec![x, y, z])).post();

// We create a termination condition which allows the solver to run indefinitely
let mut termination = Indefinite;
// And we create a search strategy (in this case, simply the default)
let mut brancher = solver.default_brancher();

// Then we solve to satisfaction
let assumptions = vec![
    predicate!(x == 1),
    predicate!(y <= 1),
    predicate!(y != 0),
];
let result =
    solver.satisfy_under_assumptions(&mut brancher, &mut termination, &assumptions);

if let SatisfactionResultUnderAssumptions::UnsatisfiableUnderAssumptions(
    mut unsatisfiable,
) = result
{
    {
        let core = unsatisfiable.extract_core();

        // In this case, the core should be equal to all of the assumption literals
        assert_eq!(core, vec![predicate!(y == 1), predicate!(x == 1)].into());
    }
}
 ```

## Modules

## Module `basic_types`

```rust
pub(crate) mod basic_types { /* ... */ }
```

### Modules

## Module `constraint_operation_error`

```rust
pub(in ::basic_types) mod constraint_operation_error { /* ... */ }
```

### Types

#### Enum `ConstraintOperationError`

Errors related to adding constraints to the [`Solver`].

```rust
pub enum ConstraintOperationError {
    InfeasibleNogood,
    InfeasibleClause,
    InfeasibleState,
    InfeasiblePropagator,
}
```

##### Variants

###### `InfeasibleNogood`

###### `InfeasibleClause`

Error which indicate that adding a clause led to infeasibility at the root.

###### `InfeasibleState`

Error which indicates that a constraint was attempted to be added while the [`Solver`] was
in an infeasible state.

###### `InfeasiblePropagator`

Error which indicate that adding a propagator led to infeasibility at the root.

##### Implementations

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Error**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **IntoEither**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &ConstraintOperationError) -> bool { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Copy**
- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Eq**
- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, __formatter: &mut ::core::fmt::Formatter<''_>) -> ::core::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **StructuralPartialEq**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> ConstraintOperationError { /* ... */ }
    ```

## Module `csp_solver_execution_flag`

```rust
pub(in ::basic_types) mod csp_solver_execution_flag { /* ... */ }
```

### Types

#### Enum `CSPSolverExecutionFlag`

```rust
pub enum CSPSolverExecutionFlag {
    Feasible,
    Infeasible,
    Timeout,
}
```

##### Variants

###### `Feasible`

###### `Infeasible`

###### `Timeout`

##### Implementations

###### Trait Implementations

- **RefUnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **StructuralPartialEq**
- **Sync**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **IntoEither**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &CSPSolverExecutionFlag) -> bool { /* ... */ }
    ```

- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Copy**
- **Eq**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> CSPSolverExecutionFlag { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `function`

```rust
pub(in ::basic_types) mod function { /* ... */ }
```

### Types

#### Struct `Function`

A struct which represents a linear function over weighted [`Literal`]s, and a
constant term.

```rust
pub struct Function {
    pub(in ::basic_types::function) literals: std::collections::HashMap<crate::variables::Literal, u64, fnv::FnvBuildHasher>,
    pub(in ::basic_types::function) constant_term: u64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `literals` | `std::collections::HashMap<crate::variables::Literal, u64, fnv::FnvBuildHasher>` |  |
| `constant_term` | `u64` |  |

##### Implementations

###### Methods

- ```rust
  pub fn get_sum_of_literal_weights(self: &Self) -> u64 { /* ... */ }
  ```

- ```rust
  pub fn add_weighted_literal(self: &mut Self, literal: Literal, weight: u64) { /* ... */ }
  ```

- ```rust
  pub fn add_constant_term(self: &mut Self, value: u64) { /* ... */ }
  ```

- ```rust
  pub fn get_literal_terms(self: &Self) -> impl Iterator<Item = (&Literal, &u64)> { /* ... */ }
  ```

- ```rust
  pub fn get_constant_term(self: &Self) -> u64 { /* ... */ }
  ```

- ```rust
  pub fn evaluate_solution(self: &Self, solution: SolutionReference<''_>) -> u64 { /* ... */ }
  ```

- ```rust
  pub fn evaluate_assignment(self: &Self, solution: &Solution) -> u64 { /* ... */ }
  ```

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Function { /* ... */ }
    ```

- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Default**
  - ```rust
    fn default() -> Function { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Freeze**
- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **UnwindSafe**
## Module `hash_structures`

```rust
pub(in ::basic_types) mod hash_structures { /* ... */ }
```

### Types

#### Type Alias `HashMap`

```rust
pub(crate) type HashMap<K, V, Hasher = fnv::FnvBuildHasher> = std::collections::HashMap<K, V, Hasher>;
```

#### Type Alias `HashSet`

```rust
pub(crate) type HashSet<K, Hasher = fnv::FnvBuildHasher> = std::collections::HashSet<K, Hasher>;
```

## Module `moving_averages`

```rust
pub(crate) mod moving_averages { /* ... */ }
```

### Modules

## Module `cumulative_moving_average`

```rust
pub(crate) mod cumulative_moving_average { /* ... */ }
```

### Types

#### Struct `CumulativeMovingAverage`

```rust
pub(crate) struct CumulativeMovingAverage<Term> {
    pub(in ::basic_types::moving_averages::cumulative_moving_average) sum: Term,
    pub(in ::basic_types::moving_averages::cumulative_moving_average) num_terms: u64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `sum` | `Term` |  |
| `num_terms` | `u64` |  |

##### Implementations

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Copy**
- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **RefUnwindSafe**
- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> CumulativeMovingAverage<Term> { /* ... */ }
    ```

- **Send**
- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Freeze**
- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Default**
  - ```rust
    fn default() -> CumulativeMovingAverage<Term> { /* ... */ }
    ```

- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **MovingAverage**
  - ```rust
    fn add_term(self: &mut Self, new_term: Term) { /* ... */ }
    ```

  - ```rust
    fn value(self: &Self) -> f64 { /* ... */ }
    ```

  - ```rust
    fn adapt(self: &mut Self, _interval_length: u64) { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

## Module `moving_average`

```rust
pub(crate) mod moving_average { /* ... */ }
```

### Traits

#### Trait `MovingAverage`

```rust
pub(crate) trait MovingAverage<Term>: Debug {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `add_term`
- `value`: Returns the moving average value; in case there are no terms, the convention is to return 0
- `adapt`: Adapts the internal data structures to take into account the given interval length; this

##### Implementations

This trait is implemented for the following types:

- `CumulativeMovingAverage<Term>` with <Term>
- `WindowedMovingAverage<Term>` with <Term>

## Module `windowed_moving_average`

```rust
pub(crate) mod windowed_moving_average { /* ... */ }
```

### Types

#### Struct `WindowedMovingAverage`

```rust
pub(crate) struct WindowedMovingAverage<Term> {
    pub(in ::basic_types::moving_averages::windowed_moving_average) window_size: u64,
    pub(in ::basic_types::moving_averages::windowed_moving_average) windowed_sum: Term,
    pub(in ::basic_types::moving_averages::windowed_moving_average) values_in_window: std::collections::VecDeque<Term>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `window_size` | `u64` |  |
| `windowed_sum` | `Term` |  |
| `values_in_window` | `std::collections::VecDeque<Term>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(window_size: u64) -> WindowedMovingAverage<Term> { /* ... */ }
  ```

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Eq**
- **StructuralPartialEq**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> WindowedMovingAverage<Term> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Unpin**
- **MovingAverage**
  - ```rust
    fn add_term(self: &mut Self, new_term: Term) { /* ... */ }
    ```

  - ```rust
    fn value(self: &Self) -> f64 { /* ... */ }
    ```

  - ```rust
    fn adapt(self: &mut Self, interval_length: u64) { /* ... */ }
    ```

- **Send**
- **Sync**
- **IntoEither**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Freeze**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &WindowedMovingAverage<Term>) -> bool { /* ... */ }
    ```

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

## Module `predicate_id_generator`

```rust
pub(in ::basic_types) mod predicate_id_generator { /* ... */ }
```

### Types

#### Struct `PredicateIdGenerator`

```rust
pub(crate) struct PredicateIdGenerator {
    pub(in ::basic_types::predicate_id_generator) next_id: u32,
    pub(in ::basic_types::predicate_id_generator) deleted_ids: Vec<PredicateId>,
    pub(in ::basic_types::predicate_id_generator) id_to_predicate: std::collections::HashMap<PredicateId, crate::engine::predicates::predicate::Predicate, fnv::FnvBuildHasher>,
    pub(in ::basic_types::predicate_id_generator) predicate_to_id: std::collections::HashMap<crate::engine::predicates::predicate::Predicate, PredicateId, fnv::FnvBuildHasher>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `next_id` | `u32` | The value of the next id, provided there are no delete_ids that can be reused. |
| `deleted_ids` | `Vec<PredicateId>` | When an id is deleted, it gets stored here, so that the id can be reused in the future. |
| `id_to_predicate` | `std::collections::HashMap<PredicateId, crate::engine::predicates::predicate::Predicate, fnv::FnvBuildHasher>` | Active predicates are stored here.<br>todo: consider direct hashing. |
| `predicate_to_id` | `std::collections::HashMap<crate::engine::predicates::predicate::Predicate, PredicateId, fnv::FnvBuildHasher>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn has_id_for_predicate(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::basic_types::predicate_id_generator) fn get_new_predicate_id(self: &mut Self) -> PredicateId { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_id(self: &mut Self, predicate: Predicate) -> PredicateId { /* ... */ }
  ```
  Returns an id for the predicate. If the predicate already has an id, its id is returned.

- ```rust
  pub(crate) fn get_predicate(self: &Self, id: PredicateId) -> Option<Predicate> { /* ... */ }
  ```

- ```rust
  pub(crate) fn delete_id(self: &mut Self, id: PredicateId) { /* ... */ }
  ```

- ```rust
  pub(crate) fn clear(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn replace_predicate(self: &mut Self, predicate: Predicate, replacement: Predicate) { /* ... */ }
  ```

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> PredicateIdGenerator { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> PredicateIdGenerator { /* ... */ }
    ```

- **Send**
#### Struct `PredicateId`

```rust
pub(crate) struct PredicateId {
    pub(crate) id: u32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `id` | `u32` |  |

##### Implementations

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **PartialOrd**
  - ```rust
    fn partial_cmp(self: &Self, other: &PredicateId) -> $crate::option::Option<$crate::cmp::Ordering> { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &PredicateId) -> bool { /* ... */ }
    ```

- **StructuralPartialEq**
- **StorageKey**
  - ```rust
    fn index(self: &Self) -> usize { /* ... */ }
    ```

  - ```rust
    fn create_from_index(index: usize) -> Self { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **Sync**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Ord**
  - ```rust
    fn cmp(self: &Self, other: &PredicateId) -> $crate::cmp::Ordering { /* ... */ }
    ```

- **Eq**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> PredicateId { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **RefUnwindSafe**
- **Copy**
- **Freeze**
## Module `propagation_status_cp`

```rust
pub(in ::basic_types) mod propagation_status_cp { /* ... */ }
```

### Types

#### Type Alias `PropagationStatusCP`

The result of invoking a constraint programming propagator. The propagation can either succeed
or identify a conflict. The necessary conditions for the conflict must be captured in the error
variant, i.e. a propositional conjunction.

```rust
pub(crate) type PropagationStatusCP = Result<(), Inconsistency>;
```

#### Enum `Inconsistency`

```rust
pub(crate) enum Inconsistency {
    EmptyDomain,
    Conflict(crate::basic_types::PropositionalConjunction),
}
```

##### Variants

###### `EmptyDomain`

###### `Conflict`

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::PropositionalConjunction` |  |

##### Implementations

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **StructuralPartialEq**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(_: EmptyDomain) -> Self { /* ... */ }
    ```

  - ```rust
    fn from(conflict_nogood: PropositionalConjunction) -> Self { /* ... */ }
    ```

  - ```rust
    fn from(value: Slice) -> Self { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **IntoEither**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Inconsistency) -> bool { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Freeze**
- **Unpin**
- **Eq**
## Module `propositional_conjunction`

```rust
pub(in ::basic_types) mod propositional_conjunction { /* ... */ }
```

### Types

#### Struct `PropositionalConjunction`

A struct which represents a conjunction of [`Predicate`]s (e.g. it can represent `[x >= 5] /\ [y
<= 10]`).

```rust
pub struct PropositionalConjunction {
    pub(in ::basic_types::propositional_conjunction) predicates_in_conjunction: Vec<crate::engine::predicates::predicate::Predicate>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `predicates_in_conjunction` | `Vec<crate::engine::predicates::predicate::Predicate>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(predicates_in_conjunction: Vec<Predicate>) -> Self { /* ... */ }
  ```

- ```rust
  pub fn len(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub fn is_empty(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn contains(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub fn num_predicates(self: &Self) -> u32 { /* ... */ }
  ```

- ```rust
  pub fn add(self: &mut Self, predicate: Predicate) { /* ... */ }
  ```

- ```rust
  pub fn iter(self: &Self) -> impl Iterator<Item = &Predicate> + ''_ { /* ... */ }
  ```

- ```rust
  pub fn as_slice(self: &Self) -> &[Predicate] { /* ... */ }
  ```

- ```rust
  pub fn clear(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub fn push(self: &mut Self, predicate: Predicate) { /* ... */ }
  ```

- ```rust
  pub fn swap(self: &mut Self, a: usize, b: usize) { /* ... */ }
  ```

- ```rust
  pub fn pop(self: &mut Self) -> Option<Predicate> { /* ... */ }
  ```

- ```rust
  pub fn extend_and_remove_duplicates</* synthetic */ impl Iterator<Item = Predicate>: Iterator<Item = Predicate>>(self: Self, additional_elements: impl Iterator<Item = Predicate>) -> PropositionalConjunction { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **FromIterator**
  - ```rust
    fn from_iter<T: IntoIterator<Item = Predicate>>(iter: T) -> Self { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> PropositionalConjunction { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Eq**
- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(conflict_nogood: PropositionalConjunction) -> Self { /* ... */ }
    ```

  - ```rust
    fn from(slice: T) -> Self { /* ... */ }
    ```

  - ```rust
    fn from(conjunction: PropositionalConjunction) -> Vec<Predicate> { /* ... */ }
    ```

  - ```rust
    fn from(predicate: Predicate) -> Self { /* ... */ }
    ```

  - ```rust
    fn from(value: PropositionalConjunction) -> Self { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Send**
- **IntoEither**
- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Extend**
  - ```rust
    fn extend<T: IntoIterator<Item = Predicate>>(self: &mut Self, iter: T) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Self) -> bool { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IndexMut**
  - ```rust
    fn index_mut(self: &mut Self, index: usize) -> &mut <Self as >::Output { /* ... */ }
    ```

- **Freeze**
- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Index**
  - ```rust
    fn index(self: &Self, index: usize) -> &<Self as >::Output { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoIterator**
  - ```rust
    fn into_iter(self: Self) -> <Self as >::IntoIter { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **Default**
  - ```rust
    fn default() -> PropositionalConjunction { /* ... */ }
    ```

## Module `random`

```rust
pub(in ::basic_types) mod random { /* ... */ }
```

### Traits

#### Trait `Random`

Abstraction for randomness, in order to swap out different source of randomness.

This is especially useful when testing, to control which variables are generated when random
values are required.

# Testing
We have also created an implementation of this trait which takes as input a list of `usize`s and
`bool`s and returns them in that order. This allows the user to define deterministic test-cases
while the implementation makes use of an implementation of the [`Random`] trait.

```rust
pub trait Random: Debug {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `generate_bool`: Generates a bool with probability `probability` of being true. It should hold that
- `generate_usize_in_range`: Generates a random usize in the provided range with equal probability; this can be seen as
- `generate_i32_in_range`: Generates a random i32 in the provided range with equal probability; this can be seen as
- `generate_f64`: Generate a random float in the range 0..1.
- `get_weighted_choice`: Given a slice of weights, select the index with `weight` weighted probability compared to

##### Implementations

This trait is implemented for the following types:

- `T` with <T>

## Module `sequence_generators`

```rust
pub(crate) mod sequence_generators { /* ... */ }
```

### Modules

## Module `constant_sequence`

```rust
pub(crate) mod constant_sequence { /* ... */ }
```

### Types

#### Struct `ConstantSequence`

```rust
pub(crate) struct ConstantSequence {
    pub(in ::basic_types::sequence_generators::constant_sequence) constant_value: i64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `constant_value` | `i64` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(constant_value: i64) -> ConstantSequence { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ConstantSequence { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **SequenceGenerator**
  - ```rust
    fn next(self: &mut Self) -> i64 { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
- **Copy**
- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `geometric_sequence`

```rust
pub(crate) mod geometric_sequence { /* ... */ }
```

### Types

#### Struct `GeometricSequence`

Given constants 'a' and 'm', the i-th element f(i) in a geometric sequence is computed as:
 f(i) = f(i-1) * m
 f(0) = a
When 'm' is not an integer, the above formula is _not_ the same as f(i) = a * m^i since
intermediate values will be rounded down

Note that overflows are not taken into account

```rust
pub(crate) struct GeometricSequence {
    pub(in ::basic_types::sequence_generators::geometric_sequence) current_value: i64,
    pub(in ::basic_types::sequence_generators::geometric_sequence) multiplication_factor: f64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `current_value` | `i64` |  |
| `multiplication_factor` | `f64` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(starting_value: i64, multiplication_factor: f64) -> GeometricSequence { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> GeometricSequence { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **SequenceGenerator**
  - ```rust
    fn next(self: &mut Self) -> i64 { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Copy**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **RefUnwindSafe**
## Module `luby_sequence`

```rust
pub(crate) mod luby_sequence { /* ... */ }
```

### Types

#### Struct `LubySequence`

1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2....
 The above sequence is multiplied with a given constant 'base_value'
Generating the next element is computed in constant time using Knuth's 'reluctant doubling'
formula.

Note that overflows are not taken into account

```rust
pub(crate) struct LubySequence {
    pub(in ::basic_types::sequence_generators::luby_sequence) u: i64,
    pub(in ::basic_types::sequence_generators::luby_sequence) v: i64,
    pub(in ::basic_types::sequence_generators::luby_sequence) base_value: i64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `u` | `i64` |  |
| `v` | `i64` |  |
| `base_value` | `i64` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(base_value: i64) -> LubySequence { /* ... */ }
  ```

###### Trait Implementations

- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LubySequence { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **SequenceGenerator**
  - ```rust
    fn next(self: &mut Self) -> i64 { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **RefUnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Copy**
- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
## Module `sequence_generator`

```rust
pub(crate) mod sequence_generator { /* ... */ }
```

### Traits

#### Trait `SequenceGenerator`

```rust
pub(crate) trait SequenceGenerator: Debug {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `next`

##### Implementations

This trait is implemented for the following types:

- `ConstantSequence`
- `GeometricSequence`
- `LubySequence`

## Module `sequence_generator_type`

```rust
pub(crate) mod sequence_generator_type { /* ... */ }
```

### Types

#### Enum `SequenceGeneratorType`

Specifies the type of sequence which is used to generate conflict limits before a restart
occurs.

```rust
pub enum SequenceGeneratorType {
    Constant,
    Geometric,
    Luby,
}
```

##### Variants

###### `Constant`

Indicates that the restart strategy should restart every `x` conflicts.

###### `Geometric`

Indicates that the restarts strategy should use geometric restarts.

Given two constants `base` and `multiplicative_factor`, the i-th element `f(i)` in a
geometric sequence is caluclated as follows:
- `f(i) = f(i - 1) * multiplicative_factor`
- `f(0) = base`

When `multiplicative_factor` is not an integer, then the above formula is **not** the same
as the formula `f(i) = a * m^i` since intermediate values are founded down.

###### `Luby`

Indicates that the restart strategy should use Luby restarts \[1\].

 The Luby sequence is a recursive sequence of the form:
1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2....

# Bibliography
\[1\] M. Luby, A. Sinclair, and D. Zuckerman, ‘Optimal speedup of Las Vegas algorithms’,
Information Processing Letters, vol. 47, no. 4, pp. 173–180, 1993.

##### Implementations

###### Trait Implementations

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **ValueEnum**
  - ```rust
    fn value_variants<''a>() -> &''a [Self] { /* ... */ }
    ```

  - ```rust
    fn to_possible_value<''a>(self: &Self) -> ::std::option::Option<clap::builder::PossibleValue> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> SequenceGeneratorType { /* ... */ }
    ```

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> SequenceGeneratorType { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **Send**
- **Copy**
### Re-exports

#### Re-export `SequenceGeneratorType`

```rust
pub use sequence_generator_type::SequenceGeneratorType;
```

## Module `solution`

```rust
pub(in ::basic_types) mod solution { /* ... */ }
```

### Types

#### Struct `SolutionReference`

A solution which keeps reference to its inner structures.

```rust
pub struct SolutionReference<''a> {
    pub(in ::basic_types::solution) assignments: &''a assignments::Assignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `&''a assignments::Assignments` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(assignments: &''a Assignments) -> SolutionReference<''a> { /* ... */ }
  ```

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> SolutionReference<''a> { /* ... */ }
    ```

- **ProblemSolution**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &''a Assignments { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Sync**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: SolutionReference<''_>) -> Self { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Freeze**
- **UnwindSafe**
- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Copy**
- **RefUnwindSafe**
#### Struct `Solution`

A solution which takes ownership of its inner structures.

```rust
pub struct Solution {
    pub(in ::basic_types::solution) assignments: assignments::Assignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `assignments::Assignments` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(assignments: Assignments) -> Self { /* ... */ }
  ```

- ```rust
  pub fn get_domains(self: &Self) -> DomainGeneratorIterator { /* ... */ }
  ```

- ```rust
  pub fn as_reference(self: &Self) -> SolutionReference<''_> { /* ... */ }
  ```

- ```rust
  pub fn contains_domain_id(self: &Self, domain_id: DomainId) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_predicate_satisfied(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

###### Trait Implementations

- **IntoEither**
- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &Assignments { /* ... */ }
    ```

- **ProblemSolution**
- **Send**
- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: SolutionReference<''_>) -> Self { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Solution { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Solution { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
### Traits

#### Trait `ProblemSolution`

A trait which specifies the common behaviours of [`Solution`] and [`SolutionReference`].

```rust
pub trait ProblemSolution: HasAssignments {
    /* Associated items */
}
```

> This trait is not object-safe and cannot be used in dynamic trait objects.

##### Provided Methods

- ```rust
  fn num_domains(self: &Self) -> usize { /* ... */ }
  ```
  Returns the number of defined [`DomainId`]s.

- ```rust
  fn get_integer_value<Var: IntegerVariable + ''static>(self: &Self, var: Var) -> i32 { /* ... */ }
  ```

- ```rust
  fn get_literal_value(self: &Self, literal: Literal) -> bool { /* ... */ }
  ```

##### Implementations

This trait is implemented for the following types:

- `SolutionReference<''_>`
- `Solution`

## Module `stored_conflict_info`

```rust
pub(in ::basic_types) mod stored_conflict_info { /* ... */ }
```

### Types

#### Enum `StoredConflictInfo`

A conflict info which can be stored in the solver.
Two (related) conflicts can happen:
1) A propagator explicitly detects a conflict.
2) A propagator post a domain change that results in a variable having an empty domain.

```rust
pub(crate) enum StoredConflictInfo {
    Propagator {
        conflict_nogood: super::PropositionalConjunction,
        propagator_id: propagator_id::PropagatorId,
    },
    EmptyDomain {
        conflict_nogood: super::PropositionalConjunction,
    },
    RootLevelConflict(crate::ConstraintOperationError),
}
```

##### Variants

###### `Propagator`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `conflict_nogood` | `super::PropositionalConjunction` |  |
| `propagator_id` | `propagator_id::PropagatorId` |  |

###### `EmptyDomain`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `conflict_nogood` | `super::PropositionalConjunction` |  |

###### `RootLevelConflict`

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::ConstraintOperationError` |  |

##### Implementations

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &StoredConflictInfo) -> bool { /* ... */ }
    ```

- **Unpin**
- **StructuralPartialEq**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> StoredConflictInfo { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Eq**
- **UnwindSafe**
- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **IntoEither**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Freeze**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

## Module `trail`

```rust
pub(in ::basic_types) mod trail { /* ... */ }
```

### Types

#### Struct `Trail`

```rust
pub(crate) struct Trail<T> {
    pub(in ::basic_types::trail) current_decision_level: usize,
    pub(in ::basic_types::trail) trail_delimiter: Vec<usize>,
    pub(in ::basic_types::trail) trail: Vec<T>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `current_decision_level` | `usize` |  |
| `trail_delimiter` | `Vec<usize>` | At index i is the position where the i-th decision level ends (exclusive) on the trail |
| `trail` | `Vec<T>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn increase_decision_level(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn values_on_decision_level(self: &Self, decision_level: usize) -> &[T] { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_decision_level(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn synchronise(self: &mut Self, new_decision_level: usize) -> Rev<Drain<''_, T>> { /* ... */ }
  ```

- ```rust
  pub(crate) fn push(self: &mut Self, elem: T) { /* ... */ }
  ```

- ```rust
  pub(crate) fn pop(self: &mut Self) -> Option<T> { /* ... */ }
  ```
  This method pops an entry from the trail without doing any checks.

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Receiver**
- **Sync**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Trail<T> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Deref**
  - ```rust
    fn deref(self: &Self) -> &<Self as >::Target { /* ... */ }
    ```

- **IntoEither**
### Re-exports

#### Re-export `ConstraintOperationError`

```rust
pub use constraint_operation_error::ConstraintOperationError;
```

#### Re-export `Function`

```rust
pub use function::Function;
```

#### Re-export `PropositionalConjunction`

```rust
pub use propositional_conjunction::PropositionalConjunction;
```

#### Re-export `ProblemSolution`

```rust
pub use solution::ProblemSolution;
```

#### Re-export `Solution`

```rust
pub use solution::Solution;
```

#### Re-export `SolutionReference`

```rust
pub use solution::SolutionReference;
```

#### Re-export `random::*`

```rust
pub use random::*;
```

## Module `containers`

Contains containers which are used by the solver.

```rust
pub mod containers { /* ... */ }
```

### Modules

## Module `key_value_heap`

A heap where the keys range from [0, ..., n - 1] and the values are nonnegative floating points.
The heap can be queried to return key with the maximum value, and certain keys can be
(temporarily) removed/readded as necessary It allows increasing/decreasing the values of its
entries

```rust
pub(in ::containers) mod key_value_heap { /* ... */ }
```

### Types

#### Struct `KeyValueHeap`

A [max-heap](https://en.wikipedia.org/wiki/Min-max_heap)
which allows for generalised `Key`s (required to implement [StorageKey]) and `Value`s (which are
required to be ordered, divisible and addable).

```rust
pub struct KeyValueHeap<Key, Value> {
    pub(in ::containers::key_value_heap) values: Vec<Value>,
    pub(in ::containers::key_value_heap) map_key_to_position: super::KeyedVec<Key, usize>,
    pub(in ::containers::key_value_heap) map_position_to_key: Vec<Key>,
    pub(in ::containers::key_value_heap) end_position: usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `values` | `Vec<Value>` | Contains the values stored as a heap; the value of key `i` is at index<br>[`KeyValueHeap::map_key_to_position\[i\]`][KeyValueHeap::map_key_to_position] |
| `map_key_to_position` | `super::KeyedVec<Key, usize>` | `map_key_to_position[i]` is the index of the value of the key `i` in<br>[`KeyValueHeap::values`] |
| `map_position_to_key` | `Vec<Key>` | `map_position_to_key[i]` is the key which is associated with `i` in<br>[`KeyValueHeap::values`] |
| `end_position` | `usize` | The index of the last element in [`KeyValueHeap::values`] |

##### Implementations

###### Methods

- ```rust
  pub(crate) const fn new() -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn keys(self: &Self) -> impl Iterator<Item = Key> + ''_ { /* ... */ }
  ```
  Get the keys in the heap.

- ```rust
  pub(crate) fn peek_max(self: &Self) -> Option<(&Key, &Value)> { /* ... */ }
  ```
  Return the key with maximum value from the heap, or None if the heap is empty. Note that

- ```rust
  pub(crate) fn get_value(self: &Self, key: Key) -> &Value { /* ... */ }
  ```

- ```rust
  pub(crate) fn pop_max(self: &mut Self) -> Option<Key> { /* ... */ }
  ```
  Deletes the key with maximum value from the heap and returns it, or None if the heap is

- ```rust
  pub(crate) fn increment(self: &mut Self, key: Key, increment: Value) { /* ... */ }
  ```
  Increments the value of the element of 'key' by 'increment'

- ```rust
  pub(crate) fn restore_key(self: &mut Self, key: Key) { /* ... */ }
  ```
  Restores the entry with key 'key' to the heap if the key is not present, otherwise does

- ```rust
  pub(crate) fn delete_key(self: &mut Self, key: Key) { /* ... */ }
  ```
  Removes the entry with key 'key' (temporarily) from the heap if the key is present,

- ```rust
  pub(crate) fn len(self: &Self) -> usize { /* ... */ }
  ```
  Returns how many elements are in the heap (including the (temporarily) "removed" values)

- ```rust
  pub(crate) fn num_nonremoved_elements(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn has_no_nonremoved_elements(self: &Self) -> bool { /* ... */ }
  ```
  Returns whether there are elements left in the heap (excluding the "removed" values)

- ```rust
  pub(crate) fn is_key_present(self: &Self, key: Key) -> bool { /* ... */ }
  ```
  Returns whether the key is currently not (temporarily) remove

- ```rust
  pub(crate) fn grow(self: &mut Self, key: Key, value: Value) { /* ... */ }
  ```
  Increases the size of the heap by one and adjust the data structures appropriately by adding

- ```rust
  pub(crate) fn clear(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn divide_values(self: &mut Self, divisor: Value) { /* ... */ }
  ```
  Divides all the values in the heap by 'divisor'. This will also affect the values of keys

- ```rust
  pub(in ::containers::key_value_heap) fn swap_positions(self: &mut Self, a: usize, b: usize) { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn sift_up(self: &mut Self, position: usize) { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn sift_down(self: &mut Self, position: usize) { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn is_heap_locally(self: &Self, position: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn is_leaf(self: &Self, position: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn get_largest_child_position(self: &Self, position: usize) -> usize { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn get_parent_position(child_position: usize) -> usize { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn get_left_child_position(position: usize) -> usize { /* ... */ }
  ```

- ```rust
  pub(in ::containers::key_value_heap) fn get_right_child_position(position: usize) -> usize { /* ... */ }
  ```

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> KeyValueHeap<Key, Value> { /* ... */ }
    ```

- **Freeze**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Unpin**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `keyed_vec`

```rust
pub(in ::containers) mod keyed_vec { /* ... */ }
```

### Types

#### Struct `KeyedVec`

Structure for storing elements of type `Value`, the structure can only be indexed by structures
of type `Key`.

Almost all features of this structure require that `Key` implements the [StorageKey] trait.

```rust
pub struct KeyedVec<Key, Value> {
    pub(in ::containers::keyed_vec) key: std::marker::PhantomData<Key>,
    pub(in ::containers::keyed_vec) elements: Vec<Value>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `key` | `std::marker::PhantomData<Key>` | [PhantomData] to ensure that the [KeyedVec] is bound to the structure |
| `elements` | `Vec<Value>` | Storage of the elements of type `Value` |

##### Implementations

###### Methods

- ```rust
  pub(crate) const fn new() -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn len(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub fn push(self: &mut Self, value: Value) -> Key { /* ... */ }
  ```
  Add a new value to the vector.

- ```rust
  pub fn iter(self: &Self) -> impl Iterator<Item = &Value> { /* ... */ }
  ```
  Iterate over the values in the vector.

- ```rust
  pub(crate) fn keys(self: &Self) -> impl Iterator<Item = Key> { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_mut(self: &mut Self) -> impl Iterator<Item = &mut Value> { /* ... */ }
  ```

- ```rust
  pub(crate) fn swap(self: &mut Self, a: usize, b: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn resize(self: &mut Self, new_len: usize, value: Value) { /* ... */ }
  ```

- ```rust
  pub(crate) fn clear(self: &mut Self) { /* ... */ }
  ```

###### Trait Implementations

- **IndexMut**
  - ```rust
    fn index_mut(self: &mut Self, index: Key) -> &mut <Self as >::Output { /* ... */ }
    ```

- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **Unpin**
- **Eq**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &KeyedVec<Key, Value>) -> bool { /* ... */ }
    ```

- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **StructuralPartialEq**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **Index**
  - ```rust
    fn index(self: &Self, index: Key) -> &<Self as >::Output { /* ... */ }
    ```

  - ```rust
    fn index(self: &Self, index: &Key) -> &<Self as >::Output { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Self { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

### Traits

#### Trait `StorageKey`

A simple trait which requires that the structures implementing this trait can generate an index.

```rust
pub trait StorageKey {
    /* Associated items */
}
```

> This trait is not object-safe and cannot be used in dynamic trait objects.

##### Required Items

###### Required Methods

- `index`
- `create_from_index`

##### Implementations

This trait is implemented for the following types:

- `PredicateId`
- `usize`
- `PropagatorId`
- `TrailedInt`
- `DomainId`
- `NogoodId`

## Module `sparse_set`

A set for keeping track of which values are still part of the original domain, allows O(1)
removals and O(|D|) traversal of the domain (where D are the values which are currently in the
domain).

# Theoretical
The idea of this structure is to allow efficient removal and traversal of the values which are
still in the domain at the "cost" of expensive queries to check whether a value is currently in
the domain.

The idea is that the sparse-set keeps track of the number of elements which are in
the domain in ([`SparseSet::size`]) and it guarantees that the first [`SparseSet::size`] values
are in the domain. To remove a value, the element at index `i` is swapped with the element at
index [`SparseSet::size`] and [`SparseSet::size`] is afterwards decremented by 1. This does not
allow the reclamation of memory when an element is removed from the structure but it allows easy
backtracking by simply moving the [`SparseSet::size`] pointer.

# Practical
Our implementation follows [\[1\]](https://hal.science/hal-01339250/document). The [`SparseSet`]
structure keeps track of a number of variables; the main practical consideration is that a
function `mapping` should be provided which maps every
value in the domain to an index in \[0..|domain|\) in a bijective manner.

# Bibliography
\[1\] V. le C. de Saint-Marcq, P. Schaus, C. Solnon, and C. Lecoutre, ‘Sparse-sets for domain
implementation’, in CP workshop on Techniques foR Implementing Constraint programming Systems
(TRICS), 2013, pp. 1–10.

```rust
pub(in ::containers) mod sparse_set { /* ... */ }
```

### Types

#### Struct `SparseSet`

A set for keeping track of which values are still part of the original domain based on [\[1\]](https://hal.science/hal-01339250/document).
See the module level documentation for more information.

It provides O(1) removals of values from the domain and O(|D|) traversal of the domain (where D
are the values which are currently in the domain).

Note that it is required that each element contained in the domain can be
uniquely mapped to an index in the range [0, |D|) (i.e. the mapping function is bijective)

# Bibliography
\[1\] V. le C. de Saint-Marcq, P. Schaus, C. Solnon, and C. Lecoutre, ‘Sparse-sets for domain
implementation’, in CP workshop on Techniques foR Implementing Constraint programming Systems
(TRICS), 2013, pp. 1–10.

```rust
pub(crate) struct SparseSet<T> {
    pub(in ::containers::sparse_set) size: usize,
    pub(in ::containers::sparse_set) domain: Vec<T>,
    pub(in ::containers::sparse_set) indices: Vec<usize>,
    pub(in ::containers::sparse_set) mapping: fn(&T) -> usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `size` | `usize` | The number of elements which are currently in the domain |
| `domain` | `Vec<T>` | The current state of the domain, this structure guarantees that the first<br>[`size`][SparseSet::size] elements are part of the domain |
| `indices` | `Vec<usize>` | Stores for each value of T what its corresponding index is in<br>[`domain`][`SparseSet::domain`] |
| `mapping` | `fn(&T) -> usize` | A bijective function which takes as input an element `T` and returns an index in the range<br>[0, |D_{original}|) to be used for retrieving values from<br>[`indices`][`SparseSet::indices`] |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(input: Vec<T>, mapping: fn(&T) -> usize) -> Self { /* ... */ }
  ```
  Assumption: It is assumed that `mapping` is a bijective function which

- ```rust
  pub(crate) fn set_to_empty(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_empty(self: &Self) -> bool { /* ... */ }
  ```
  Determines whether the domain represented by the [`SparseSet`] is empty

- ```rust
  pub(crate) fn len(self: &Self) -> usize { /* ... */ }
  ```
  Returns how many elements are part of the domain

- ```rust
  pub(crate) fn get(self: &Self, index: usize) -> &T { /* ... */ }
  ```
  Returns the `index`th element in the domain; if `index` is larger than or equal to

- ```rust
  pub(in ::containers::sparse_set) fn swap(self: &mut Self, i: usize, j: usize) { /* ... */ }
  ```
  Swaps the elements at positions `i` and `j` in [`domain`][SparseSet::domain] and swaps the

- ```rust
  pub(crate) fn remove(self: &mut Self, to_remove: &T) { /* ... */ }
  ```
  Remove the value of `to_remove` from the domain; if the value is not in the domain then this

- ```rust
  pub(crate) fn remove_temporarily(self: &mut Self, to_remove: &T) { /* ... */ }
  ```

- ```rust
  pub(crate) fn restore_temporarily_removed(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn contains(self: &Self, element: &T) -> bool { /* ... */ }
  ```
  Determines whehter the `element` is contained in the domain of the sparse-set.

- ```rust
  pub(crate) fn accommodate(self: &mut Self, element: &T) { /* ... */ }
  ```
  Accomodates the `element`.

- ```rust
  pub(crate) fn insert(self: &mut Self, element: T) { /* ... */ }
  ```
  Inserts the element if it is not already contained in the sparse set.

- ```rust
  pub(crate) fn iter(self: &Self) -> impl Iterator<Item = &T> { /* ... */ }
  ```
  Returns an iterator which goes over the values in the domain of the sparse-set

- ```rust
  pub(crate) fn out_of_domain(self: &Self) -> impl Iterator<Item = &T> { /* ... */ }
  ```

###### Trait Implementations

- **UnwindSafe**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> SparseSet<T> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Send**
- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoIterator**
  - ```rust
    fn into_iter(self: Self) -> <Self as >::IntoIter { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

### Re-exports

#### Re-export `KeyValueHeap`

```rust
pub use key_value_heap::KeyValueHeap;
```

#### Re-export `KeyedVec`

```rust
pub use keyed_vec::KeyedVec;
```

#### Re-export `StorageKey`

```rust
pub use keyed_vec::StorageKey;
```

## Module `engine`

```rust
pub(crate) mod engine { /* ... */ }
```

### Modules

## Module `conflict_analysis`

Contains algorithms for conflict analysis, core extraction, and clause minimisation.
The algorithms use resolution and implement the 1uip and all decision literal learning schemes

```rust
pub(crate) mod conflict_analysis { /* ... */ }
```

### Modules

## Module `conflict_analysis_context`

```rust
pub(in ::engine::conflict_analysis) mod conflict_analysis_context { /* ... */ }
```

### Types

#### Struct `ConflictAnalysisContext`

Used during conflict analysis to provide the necessary information.

All fields are made public for the time being for simplicity. In the future that may change.

```rust
pub(crate) struct ConflictAnalysisContext<''a> {
    pub(crate) assignments: &''a mut assignments::Assignments,
    pub(crate) solver_state: &''a mut crate::engine::constraint_satisfaction_solver::CSPSolverState,
    pub(crate) reason_store: &''a mut crate::engine::reason::ReasonStore,
    pub(crate) brancher: &''a mut dyn Brancher,
    pub(crate) propagators: &''a mut crate::engine::propagation::store::PropagatorStore,
    pub(crate) semantic_minimiser: &''a mut super::minimisers::SemanticMinimiser,
    pub(crate) last_notified_cp_trail_index: &''a mut usize,
    pub(crate) watch_list_cp: &''a mut watch_list_cp::WatchListCP,
    pub(crate) propagator_queue: &''a mut propagator_queue::PropagatorQueue,
    pub(crate) event_drain: &''a mut Vec<(watch_list_cp::IntDomainEvent, crate::variables::DomainId)>,
    pub(crate) backtrack_event_drain: &''a mut Vec<(watch_list_cp::IntDomainEvent, crate::variables::DomainId)>,
    pub(crate) counters: &''a mut crate::engine::solver_statistics::SolverStatistics,
    pub(crate) proof_log: &''a mut crate::proof::ProofLog,
    pub(crate) should_minimise: bool,
    pub(crate) unit_nogood_step_ids: &''a std::collections::HashMap<crate::engine::predicates::predicate::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>,
    pub(crate) stateful_assignments: &''a mut crate::engine::TrailedAssignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `&''a mut assignments::Assignments` |  |
| `solver_state` | `&''a mut crate::engine::constraint_satisfaction_solver::CSPSolverState` |  |
| `reason_store` | `&''a mut crate::engine::reason::ReasonStore` |  |
| `brancher` | `&''a mut dyn Brancher` |  |
| `propagators` | `&''a mut crate::engine::propagation::store::PropagatorStore` |  |
| `semantic_minimiser` | `&''a mut super::minimisers::SemanticMinimiser` |  |
| `last_notified_cp_trail_index` | `&''a mut usize` |  |
| `watch_list_cp` | `&''a mut watch_list_cp::WatchListCP` |  |
| `propagator_queue` | `&''a mut propagator_queue::PropagatorQueue` |  |
| `event_drain` | `&''a mut Vec<(watch_list_cp::IntDomainEvent, crate::variables::DomainId)>` |  |
| `backtrack_event_drain` | `&''a mut Vec<(watch_list_cp::IntDomainEvent, crate::variables::DomainId)>` |  |
| `counters` | `&''a mut crate::engine::solver_statistics::SolverStatistics` |  |
| `proof_log` | `&''a mut crate::proof::ProofLog` |  |
| `should_minimise` | `bool` |  |
| `unit_nogood_step_ids` | `&''a std::collections::HashMap<crate::engine::predicates::predicate::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>` |  |
| `stateful_assignments` | `&''a mut crate::engine::TrailedAssignments` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn find_last_decision(self: &mut Self) -> Option<Predicate> { /* ... */ }
  ```
  Returns the last decision which was made by the solver.

- ```rust
  pub(crate) fn enqueue_propagated_predicate(self: &mut Self, predicate: Predicate) { /* ... */ }
  ```
  Posts the predicate with reason an empty reason.

- ```rust
  pub(crate) fn backtrack(self: &mut Self, backtrack_level: usize) { /* ... */ }
  ```
  Backtracks the solver to the provided backtrack level.

- ```rust
  pub(crate) fn get_conflict_nogood(self: &mut Self) -> Vec<Predicate> { /* ... */ }
  ```
  Returns a nogood which led to the conflict, excluding predicates from the root decision

- ```rust
  pub(crate) fn get_propagation_reason</* synthetic */ impl Extend<Predicate> + AsRef<[Predicate]>: Extend<Predicate> + AsRef<[Predicate]>>(predicate: Predicate, assignments: &Assignments, current_nogood: CurrentNogood<''_>, reason_store: &mut ReasonStore, propagators: &mut PropagatorStore, proof_log: &mut ProofLog, unit_nogood_step_ids: &std::collections::HashMap<Predicate, StepId, fnv::FnvBuildHasher>, reason_buffer: &mut impl Extend<Predicate> + AsRef<[Predicate]>) { /* ... */ }
  ```
  Compute the reason for `predicate` being true. The reason will be stored in

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Freeze**
- **Send**
- **Sync**
- **Unpin**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

## Module `learned_nogood`

```rust
pub(in ::engine::conflict_analysis) mod learned_nogood { /* ... */ }
```

### Types

#### Struct `LearnedNogood`

```rust
pub(crate) struct LearnedNogood {
    pub(crate) predicates: Vec<crate::predicates::Predicate>,
    pub(crate) backjump_level: usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `predicates` | `Vec<crate::predicates::Predicate>` |  |
| `backjump_level` | `usize` |  |

##### Implementations

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LearnedNogood { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **Unpin**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
## Module `minimisers`

```rust
pub(in ::engine::conflict_analysis) mod minimisers { /* ... */ }
```

### Modules

## Module `recursive_minimiser`

```rust
pub(in ::engine::conflict_analysis::minimisers) mod recursive_minimiser { /* ... */ }
```

### Types

#### Struct `RecursiveMinimiser`

```rust
pub(crate) struct RecursiveMinimiser {
    pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) current_depth: usize,
    pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) allowed_decision_levels: std::collections::HashSet<usize, fnv::FnvBuildHasher>,
    pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) label_assignments: std::collections::HashMap<crate::predicates::Predicate, Option<Label>, fnv::FnvBuildHasher>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `current_depth` | `usize` |  |
| `allowed_decision_levels` | `std::collections::HashSet<usize, fnv::FnvBuildHasher>` |  |
| `label_assignments` | `std::collections::HashMap<crate::predicates::Predicate, Option<Label>, fnv::FnvBuildHasher>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn remove_dominated_predicates(self: &mut Self, nogood: &mut Vec<Predicate>, context: &mut ConflictAnalysisContext<''_>) { /* ... */ }
  ```
  Removes redundant literals from the learned clause.

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn compute_label(self: &mut Self, input_predicate: Predicate, context: &mut ConflictAnalysisContext<''_>, current_nogood: &[Predicate]) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn is_decision_level_allowed(self: &Self, decision_level: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn mark_decision_level_as_allowed(self: &mut Self, decision_level: usize) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn is_predicate_assigned_seen(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn get_predicate_label(self: &Self, predicate: Predicate) -> Label { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn assign_predicate_label(self: &mut Self, predicate: Predicate, label: Label) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn is_predicate_label_already_computed(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn initialise_minimisation_data_structures(self: &mut Self, nogood: &Vec<Predicate>, assignments: &Assignments) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn clean_up_minimisation(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) fn is_at_max_allowed_depth(self: &Self) -> bool { /* ... */ }
  ```

###### Trait Implementations

- **Unpin**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Default**
  - ```rust
    fn default() -> RecursiveMinimiser { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> RecursiveMinimiser { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

#### Enum `Label`

```rust
pub(in ::engine::conflict_analysis::minimisers::recursive_minimiser) enum Label {
    Seen,
    Poison,
    Removable,
    Keep,
}
```

##### Variants

###### `Seen`

###### `Poison`

###### `Removable`

###### `Keep`

##### Implementations

###### Trait Implementations

- **Copy**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> Label { /* ... */ }
    ```

- **StructuralPartialEq**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Label) -> bool { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `semantic_minimiser`

```rust
pub(in ::engine::conflict_analysis::minimisers) mod semantic_minimiser { /* ... */ }
```

### Types

#### Struct `SemanticMinimiser`

```rust
pub(crate) struct SemanticMinimiser {
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) original_domains: crate::containers::KeyedVec<crate::variables::DomainId, SimpleIntegerDomain>,
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) domains: crate::containers::KeyedVec<crate::variables::DomainId, SimpleIntegerDomain>,
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) present_ids: sparse_set::SparseSet<crate::variables::DomainId>,
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) helper: Vec<crate::predicates::Predicate>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `original_domains` | `crate::containers::KeyedVec<crate::variables::DomainId, SimpleIntegerDomain>` |  |
| `domains` | `crate::containers::KeyedVec<crate::variables::DomainId, SimpleIntegerDomain>` |  |
| `present_ids` | `sparse_set::SparseSet<crate::variables::DomainId>` |  |
| `helper` | `Vec<crate::predicates::Predicate>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn minimise(self: &mut Self, nogood: &Vec<Predicate>, assignments: &Assignments, mode: Mode) -> Vec<Predicate> { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn apply_predicates(self: &mut Self, nogood: &Vec<Predicate>) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn accommodate(self: &mut Self, assignments: &Assignments) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn grow(self: &mut Self, lower_bound: i32, upper_bound: i32, holes: Vec<i32>) { /* ... */ }
  ```

- ```rust
  pub(crate) fn clean_up(self: &mut Self) { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **Sync**
- **Freeze**
- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> SemanticMinimiser { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

#### Enum `Mode`

```rust
pub(crate) enum Mode {
    EnableEqualityMerging,
    DisableEqualityMerging,
}
```

##### Variants

###### `EnableEqualityMerging`

###### `DisableEqualityMerging`

##### Implementations

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Copy**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> Mode { /* ... */ }
    ```

- **UnwindSafe**
- **RefUnwindSafe**
- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

#### Struct `SimpleIntegerDomain`

```rust
pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) struct SimpleIntegerDomain {
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) lower_bound: i32,
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) upper_bound: i32,
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) holes: std::collections::HashSet<i32, fnv::FnvBuildHasher>,
    pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) inconsistent: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `lower_bound` | `i32` |  |
| `upper_bound` | `i32` |  |
| `holes` | `std::collections::HashSet<i32, fnv::FnvBuildHasher>` |  |
| `inconsistent` | `bool` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn tighten_lower_bound(self: &mut Self, lower_bound: i32) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn tighten_upper_bound(self: &mut Self, upper_bound: i32) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn add_hole(self: &mut Self, hole: i32) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn assign(self: &mut Self, value: i32) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn propagate_holes_on_lower_bound(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn propagate_holes_on_upper_bound(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn update_consistency(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn remove_redundant_holes(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::minimisers::semantic_minimiser) fn add_domain_description_to_vector(self: &Self, domain_id: DomainId, original_domain: &SimpleIntegerDomain, description: &mut Vec<Predicate>, mode: Mode) { /* ... */ }
  ```

###### Trait Implementations

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> SimpleIntegerDomain { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **Default**
  - ```rust
    fn default() -> SimpleIntegerDomain { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
## Module `resolvers`

```rust
pub(in ::engine::conflict_analysis) mod resolvers { /* ... */ }
```

### Modules

## Module `conflict_resolver`

```rust
pub(in ::engine::conflict_analysis::resolvers) mod conflict_resolver { /* ... */ }
```

### Traits

#### Trait `ConflictResolver`

```rust
pub(crate) trait ConflictResolver: Debug {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `resolve_conflict`
- `process`

##### Implementations

This trait is implemented for the following types:

- `NoLearningResolver`
- `ResolutionResolver`

## Module `no_learning_resolver`

```rust
pub(in ::engine::conflict_analysis::resolvers) mod no_learning_resolver { /* ... */ }
```

### Types

#### Struct `NoLearningResolver`

Resolve conflicts by backtracking one decision level trying the opposite of the last decision.

```rust
pub(crate) struct NoLearningResolver;
```

##### Implementations

###### Trait Implementations

- **Copy**
- **ConflictResolver**
  - ```rust
    fn resolve_conflict(self: &mut Self, _context: &mut ConflictAnalysisContext<''_>) -> Option<LearnedNogood> { /* ... */ }
    ```

  - ```rust
    fn process(self: &mut Self, context: &mut ConflictAnalysisContext<''_>, learned_nogood: &Option<LearnedNogood>) -> Result<(), ()> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Unpin**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> NoLearningResolver { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **Default**
  - ```rust
    fn default() -> NoLearningResolver { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `resolution_resolver`

```rust
pub(in ::engine::conflict_analysis::resolvers) mod resolution_resolver { /* ... */ }
```

### Types

#### Struct `ResolutionResolver`

Resolve conflicts according to the CDCL procedure.

This conflict resolver will derive a nogood that is implied by the constraints already present
in the solver. This new nogood is added as a constraint to the solver, and the solver
backtracks to the decision level at which the new constraint propagates.

```rust
pub(crate) struct ResolutionResolver {
    pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) to_process_heap: crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, u32>,
    pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) predicate_id_generator: predicate_id_generator::PredicateIdGenerator,
    pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) processed_nogood_predicates: Vec<crate::predicates::Predicate>,
    pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) recursive_minimiser: crate::engine::conflict_analysis::minimisers::RecursiveMinimiser,
    pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) mode: AnalysisMode,
    pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) reason_buffer: Vec<crate::predicates::Predicate>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `to_process_heap` | `crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, u32>` | Heap containing the predicates which still need to be processed; sorted non-increasing<br>based on trail-index where implied predicates are processed first. |
| `predicate_id_generator` | `predicate_id_generator::PredicateIdGenerator` | The generator is used in combination with the heap to keep track of which predicates are<br>stored in the heap. |
| `processed_nogood_predicates` | `Vec<crate::predicates::Predicate>` | Predicates which have been processed and have been determined to be (potentially) part of<br>the nogood.<br><br>Note that this structure may contain duplicates which are removed at the end by semantic<br>minimisation. |
| `recursive_minimiser` | `crate::engine::conflict_analysis::minimisers::RecursiveMinimiser` | A minimiser which recursively determines whether a predicate is redundant in the nogood |
| `mode` | `AnalysisMode` | Whether the resolver employs 1-UIP or all-decision learning. |
| `reason_buffer` | `Vec<crate::predicates::Predicate>` | Re-usable buffer which reasons are written into. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn with_mode(mode: AnalysisMode) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) fn clean_up(self: &mut Self) { /* ... */ }
  ```
  Clears all data structures to prepare for the new conflict analysis.

- ```rust
  pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) fn add_predicate_to_conflict_nogood(self: &mut Self, predicate: Predicate, assignments: &Assignments, brancher: &mut dyn Brancher, mode: AnalysisMode, root_explanation_context: Option<&mut RootExplanationContext<''_>>) { /* ... */ }
  ```
  Add the predicate to the current conflict nogood if we know it needs to be added.

- ```rust
  pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) fn pop_predicate_from_conflict_nogood(self: &mut Self) -> Predicate { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) fn peek_predicate_from_conflict_nogood(self: &Self) -> Predicate { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) fn replace_predicate_in_conflict_nogood(self: &mut Self, predicate: Predicate, replacement: Predicate) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::conflict_analysis::resolvers::resolution_resolver) fn extract_final_nogood(self: &mut Self, context: &mut ConflictAnalysisContext<''_>) -> LearnedNogood { /* ... */ }
  ```

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Default**
  - ```rust
    fn default() -> ResolutionResolver { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **ConflictResolver**
  - ```rust
    fn resolve_conflict(self: &mut Self, context: &mut ConflictAnalysisContext<''_>) -> Option<LearnedNogood> { /* ... */ }
    ```

  - ```rust
    fn process(self: &mut Self, context: &mut ConflictAnalysisContext<''_>, learned_nogood: &Option<LearnedNogood>) -> Result<(), ()> { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ResolutionResolver { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Sync**
#### Enum `AnalysisMode`

Determines which type of learning is performed by the resolver.

```rust
pub(crate) enum AnalysisMode {
    OneUIP,
    AllDecision,
}
```

##### Variants

###### `OneUIP`

Stanard conflict analysis which returns as soon as the first unit implication point is
found (i.e. when a nogood is created which only contains a single predicate from the
current decision level)

###### `AllDecision`

An alternative to 1-UIP which stops as soon as the learned nogood only creates decision
predicates.

##### Implementations

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> AnalysisMode { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> AnalysisMode { /* ... */ }
    ```

- **Send**
- **Copy**
- **Sync**
- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Unpin**
- **RefUnwindSafe**
## Module `constraint_satisfaction_solver`

Houses the solver which attempts to find a solution to a Constraint Satisfaction Problem (CSP)
using a Lazy Clause Generation approach.

```rust
pub(crate) mod constraint_satisfaction_solver { /* ... */ }
```

### Types

#### Struct `ConstraintSatisfactionSolver`

A solver which attempts to find a solution to a Constraint Satisfaction Problem (CSP) using
a Lazy Clause Generation (LCG [\[1\]](https://people.eng.unimelb.edu.au/pstuckey/papers/cp09-lc.pdf))
approach.

It requires that all of the propagators which are added, are able to explain the
propagations and conflicts they have made/found. It then uses standard SAT concepts such as
1UIP (see \[2\]) to learn clauses (also called nogoods in the CP field, see \[3\]) to avoid
unnecessary exploration of the search space while utilizing the search procedure benefits from
constraint programming (e.g. by preventing the exponential blow-up of problem encodings).

# Practical
The [`ConstraintSatisfactionSolver`] makes use of certain options which allow the user to
influence the behaviour of the solver; see for example the [`SatisfactionSolverOptions`].

The solver switches between making decisions using implementations of the [`Brancher`] (which
are passed to the [`ConstraintSatisfactionSolver::solve`] method) and propagation (use
[`ConstraintSatisfactionSolver::add_propagator`] to add a propagator). If a conflict is found by
any of the propagators then the solver will analyse the conflict
using 1UIP reasoning and backtrack if possible.

# Bibliography
\[1\] T. Feydy and P. J. Stuckey, ‘Lazy clause generation reengineered’, in International
Conference on Principles and Practice of Constraint Programming, 2009, pp. 352–366.

\[2\] J. Marques-Silva, I. Lynce, and S. Malik, ‘Conflict-driven clause learning SAT
solvers’, in Handbook of satisfiability, IOS press, 2021

\[3\] F. Rossi, P. Van Beek, and T. Walsh, ‘Constraint programming’, Foundations of Artificial
Intelligence, vol. 3, pp. 181–211, 2008.

```rust
pub struct ConstraintSatisfactionSolver {
    pub(crate) state: CSPSolverState,
    pub(in ::engine::constraint_satisfaction_solver) propagators: super::propagation::store::PropagatorStore,
    pub(in ::engine::constraint_satisfaction_solver) restart_strategy: restart_strategy::RestartStrategy,
    pub(in ::engine::constraint_satisfaction_solver) assumptions: Vec<crate::engine::predicates::predicate::Predicate>,
    pub(in ::engine::constraint_satisfaction_solver) semantic_minimiser: super::conflict_analysis::SemanticMinimiser,
    pub(crate) assignments: assignments::Assignments,
    pub(in ::engine::constraint_satisfaction_solver) watch_list_cp: watch_list_cp::WatchListCP,
    pub(in ::engine::constraint_satisfaction_solver) propagator_queue: propagator_queue::PropagatorQueue,
    pub(crate) reason_store: crate::engine::reason::ReasonStore,
    pub(in ::engine::constraint_satisfaction_solver) event_drain: Vec<(watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>,
    pub(in ::engine::constraint_satisfaction_solver) backtrack_event_drain: Vec<(watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>,
    pub(in ::engine::constraint_satisfaction_solver) last_notified_cp_trail_index: usize,
    pub(in ::engine::constraint_satisfaction_solver) solver_statistics: super::solver_statistics::SolverStatistics,
    pub(in ::engine::constraint_satisfaction_solver) internal_parameters: SatisfactionSolverOptions,
    pub(in ::engine::constraint_satisfaction_solver) variable_names: crate::variable_names::VariableNames,
    pub(in ::engine::constraint_satisfaction_solver) lbd_helper: literal_block_distance::Lbd,
    pub(in ::engine::constraint_satisfaction_solver) unit_nogood_step_ids: std::collections::HashMap<crate::engine::predicates::predicate::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>,
    pub(in ::engine::constraint_satisfaction_solver) conflict_resolver: Box<dyn Resolver>,
    pub(crate) stateful_assignments: super::TrailedAssignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `state` | `CSPSolverState` | The solver continuously changes states during the search.<br>The state helps track additional information and contributes to making the code clearer. |
| `propagators` | `super::propagation::store::PropagatorStore` | The list of propagators. Propagators live here and are queried when events (domain changes)<br>happen. The list is only traversed during synchronisation for now. |
| `restart_strategy` | `restart_strategy::RestartStrategy` | Tracks information about the restarts. Occassionally the solver will undo all its decisions<br>and start the search from the root note. Note that learned clauses and other state<br>information is kept after a restart. |
| `assumptions` | `Vec<crate::engine::predicates::predicate::Predicate>` | Holds the assumptions when the solver is queried to solve under assumptions. |
| `semantic_minimiser` | `super::conflict_analysis::SemanticMinimiser` |  |
| `assignments` | `assignments::Assignments` | Tracks information related to the assignments of integer variables. |
| `watch_list_cp` | `watch_list_cp::WatchListCP` | Contains information on which propagator to notify upon<br>integer events, e.g., lower or upper bound change of a variable. |
| `propagator_queue` | `propagator_queue::PropagatorQueue` | Dictates the order in which propagators will be called to propagate. |
| `reason_store` | `crate::engine::reason::ReasonStore` | Handles storing information about propagation reasons, which are used later to construct<br>explanations during conflict analysis |
| `event_drain` | `Vec<(watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>` | Contains events that need to be processed to notify propagators of event occurrences.<br>Used as a helper storage vector to avoid reallocation, and to take away ownership from the<br>events in assignments. |
| `backtrack_event_drain` | `Vec<(watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>` | Contains events that need to be processed to notify propagators of backtrack<br>[`IntDomainEvent`] occurrences (i.e. [`IntDomainEvent`]s being undone). |
| `last_notified_cp_trail_index` | `usize` |  |
| `solver_statistics` | `super::solver_statistics::SolverStatistics` | A set of counters updated during the search. |
| `internal_parameters` | `SatisfactionSolverOptions` | Miscellaneous constant parameters used by the solver. |
| `variable_names` | `crate::variable_names::VariableNames` | The names of the variables in the solver. |
| `lbd_helper` | `literal_block_distance::Lbd` | Computes the LBD for nogoods. |
| `unit_nogood_step_ids` | `std::collections::HashMap<crate::engine::predicates::predicate::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>` | A map from clause references to nogood step ids in the proof. |
| `conflict_resolver` | `Box<dyn Resolver>` | The resolver which is used upon a conflict. |
| `stateful_assignments` | `super::TrailedAssignments` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn get_nogood_propagator_id() -> PropagatorId { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn process_backtrack_events(watch_list_cp: &mut WatchListCP, backtrack_event_drain: &mut Vec<(IntDomainEvent, DomainId)>, assignments: &mut Assignments, propagators: &mut PropagatorStore) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn notify_nogood_propagator(event: IntDomainEvent, domain: DomainId, propagators: &mut PropagatorStore, propagator_queue: &mut PropagatorQueue, assignments: &mut Assignments, stateful_assignments: &mut TrailedAssignments) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn notify_propagator(propagator_id: PropagatorId, local_id: LocalId, event: IntDomainEvent, propagators: &mut PropagatorStore, propagator_queue: &mut PropagatorQueue, assignments: &mut Assignments, stateful_assignments: &mut TrailedAssignments) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn notify_propagators_about_domain_events(self: &mut Self) { /* ... */ }
  ```
  Process the stored domain events that happens as a result of decision/propagation predicates

- ```rust
  pub fn get_solution_reference(self: &Self) -> SolutionReference<''_> { /* ... */ }
  ```
  This is a temporary accessor to help refactoring.

- ```rust
  pub fn conclude_proof_unsat(self: &mut Self) -> std::io::Result<()> { /* ... */ }
  ```
  Conclude the proof with the unsatisfiable claim.

- ```rust
  pub fn conclude_proof_optimal(self: &mut Self, bound: Predicate) -> std::io::Result<()> { /* ... */ }
  ```
  Conclude the proof with the optimality claim.

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn complete_proof(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub fn new(solver_options: SatisfactionSolverOptions) -> Self { /* ... */ }
  ```

- ```rust
  pub fn solve</* synthetic */ impl TerminationCondition: TerminationCondition, /* synthetic */ impl Brancher: Brancher>(self: &mut Self, termination: &mut impl TerminationCondition, brancher: &mut impl Brancher) -> CSPSolverExecutionFlag { /* ... */ }
  ```

- ```rust
  pub fn solve_under_assumptions</* synthetic */ impl TerminationCondition: TerminationCondition, /* synthetic */ impl Brancher: Brancher>(self: &mut Self, assumptions: &[Predicate], termination: &mut impl TerminationCondition, brancher: &mut impl Brancher) -> CSPSolverExecutionFlag { /* ... */ }
  ```

- ```rust
  pub fn get_state(self: &Self) -> &CSPSolverState { /* ... */ }
  ```

- ```rust
  pub fn get_random_generator(self: &mut Self) -> &mut impl Random { /* ... */ }
  ```

- ```rust
  pub fn log_statistics(self: &Self) { /* ... */ }
  ```

- ```rust
  pub fn create_new_literal(self: &mut Self, name: Option<String>) -> Literal { /* ... */ }
  ```

- ```rust
  pub fn create_new_literal_for_predicate(self: &mut Self, predicate: Predicate, name: Option<String>) -> Literal { /* ... */ }
  ```

- ```rust
  pub fn create_new_integer_variable(self: &mut Self, lower_bound: i32, upper_bound: i32, name: Option<String>) -> DomainId { /* ... */ }
  ```
  Create a new integer variable. Its domain will have the given lower and upper bounds.

- ```rust
  pub fn create_new_integer_variable_sparse(self: &mut Self, values: Vec<i32>, name: Option<String>) -> DomainId { /* ... */ }
  ```
  Creates an integer variable with a domain containing only the values in `values`

- ```rust
  pub fn extract_clausal_core</* synthetic */ impl Brancher: Brancher>(self: &mut Self, brancher: &mut impl Brancher) -> CoreExtractionResult { /* ... */ }
  ```
  Returns an unsatisfiable core or an [`Err`] if the provided assumptions were conflicting

- ```rust
  pub fn get_literal_value(self: &Self, literal: Literal) -> Option<bool> { /* ... */ }
  ```

- ```rust
  pub fn get_lower_bound</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, variable: &impl IntegerVariable) -> i32 { /* ... */ }
  ```
  Get the lower bound for the given variable.

- ```rust
  pub fn get_upper_bound</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, variable: &impl IntegerVariable) -> i32 { /* ... */ }
  ```
  Get the upper bound for the given variable.

- ```rust
  pub fn integer_variable_contains</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, variable: &impl IntegerVariable, value: i32) -> bool { /* ... */ }
  ```
  Determine whether `value` is in the domain of `variable`.

- ```rust
  pub fn get_assigned_integer_value</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, variable: &impl IntegerVariable) -> Option<i32> { /* ... */ }
  ```
  Get the assigned integer for the given variable. If it is not assigned, `None` is returned.

- ```rust
  pub fn restore_state_at_root</* synthetic */ impl Brancher: Brancher>(self: &mut Self, brancher: &mut impl Brancher) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn initialise(self: &mut Self, assumptions: &[Predicate]) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn solve_internal</* synthetic */ impl TerminationCondition: TerminationCondition, /* synthetic */ impl Brancher: Brancher>(self: &mut Self, termination: &mut impl TerminationCondition, brancher: &mut impl Brancher) -> CSPSolverExecutionFlag { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn decay_nogood_activities(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn make_next_decision</* synthetic */ impl Brancher: Brancher>(self: &mut Self, brancher: &mut impl Brancher) -> Result<(), CSPSolverExecutionFlag> { /* ... */ }
  ```

- ```rust
  pub(crate) fn declare_new_decision_level(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn resolve_conflict_with_nogood</* synthetic */ impl Brancher: Brancher>(self: &mut Self, brancher: &mut impl Brancher) { /* ... */ }
  ```
  Changes the state based on the conflict analysis. It performs the following:

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn add_learned_nogood(self: &mut Self, learned_nogood: LearnedNogood) { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_asserting_nogood_to_nogood_propagator(nogood_propagator: &mut dyn Propagator, nogood: Vec<Predicate>, context: &mut PropagationContextMut<''_>, statistics: &mut SolverStatistics) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn restart_during_search</* synthetic */ impl Brancher: Brancher>(self: &mut Self, brancher: &mut impl Brancher) { /* ... */ }
  ```
  Performs a restart during the search process; it is only called when it has been determined

- ```rust
  pub(crate) fn backtrack<BrancherType: Brancher + ?Sized>(assignments: &mut Assignments, last_notified_cp_trail_index: &mut usize, reason_store: &mut ReasonStore, propagator_queue: &mut PropagatorQueue, watch_list_cp: &mut WatchListCP, propagators: &mut PropagatorStore, event_drain: &mut Vec<(IntDomainEvent, DomainId)>, backtrack_event_drain: &mut Vec<(IntDomainEvent, DomainId)>, backtrack_level: usize, brancher: &mut BrancherType, stateful_assignments: &mut TrailedAssignments) { /* ... */ }
  ```

- ```rust
  pub(crate) fn compute_reason_for_empty_domain(self: &mut Self) -> PropositionalConjunction { /* ... */ }
  ```

- ```rust
  pub(crate) fn propagate(self: &mut Self) { /* ... */ }
  ```
  Main propagation loop.

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn log_root_propagation_to_proof(self: &mut Self, start_trail_index: usize, tag: Option<NonZero<u32>>) { /* ... */ }
  ```
  Introduces any root-level propagations to the proof by introducing them as

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn peek_next_assumption_predicate(self: &Self) -> Option<Predicate> { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_propagator</* synthetic */ impl Propagator + 'static: Propagator + ''static>(self: &mut Self, propagator_to_add: impl Propagator + ''static, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Post a new propagator to the solver. If unsatisfiability can be immediately determined

- ```rust
  pub fn post_predicate(self: &mut Self, predicate: Predicate) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```

- ```rust
  pub fn add_nogood(self: &mut Self, nogood: Vec<Predicate>) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn prepare_for_conflict_resolution(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn add_nogood_to_nogood_propagator(nogood_propagator: &mut dyn Propagator, nogood: Vec<Predicate>, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```

- ```rust
  pub fn add_clause</* synthetic */ impl IntoIterator<Item = Predicate>: IntoIterator<Item = Predicate>>(self: &mut Self, predicates: impl IntoIterator<Item = Predicate>) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Creates a clause from `literals` and adds it to the current formula.

- ```rust
  pub(crate) fn get_decision_level(self: &Self) -> usize { /* ... */ }
  ```

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **UnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

#### Enum `CoreExtractionResult`

The result of [`ConstraintSatisfactionSolver::extract_clausal_core`]; there are 2 cases:
1. In the case of [`CoreExtractionResult::ConflictingAssumption`], two assumptions have been
   given which directly conflict with one another; e.g. if the assumptions `[x, !x]` have been
   given then the result of [`ConstraintSatisfactionSolver::extract_clausal_core`] will be a
   [`CoreExtractionResult::ConflictingAssumption`] containing `x`.
2. The standard case is when a [`CoreExtractionResult::Core`] is returned which contains (a
   subset of) the assumptions which led to conflict.

```rust
pub enum CoreExtractionResult {
    ConflictingAssumption(crate::engine::predicates::predicate::Predicate),
    Core(Vec<crate::engine::predicates::predicate::Predicate>),
}
```

##### Variants

###### `ConflictingAssumption`

Conflicting assumptions were provided; e.g. in the case of the assumptions `[x, !x]`, this
result will contain `!x`

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::engine::predicates::predicate::Predicate` |  |

###### `Core`

The standard case where this result contains the core consisting of (a subset of) the
assumptions which led to conflict.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `Vec<crate::engine::predicates::predicate::Predicate>` |  |

##### Implementations

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> CoreExtractionResult { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **UnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

#### Enum `ConflictResolver`

During search, the CP solver will inevitably evaluate partial assignments that violate at
least one constraint. When this happens, conflict resolution is applied to restore the
solver to a state from which it can continue the search.

The manner in which conflict resolution is done greatly impacts the performance of the
solver.

```rust
pub enum ConflictResolver {
    NoLearning,
    UIP,
}
```

##### Variants

###### `NoLearning`

###### `UIP`

##### Implementations

###### Trait Implementations

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **StructuralPartialEq**
- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &ConflictResolver) -> bool { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **Send**
- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Eq**
- **ValueEnum**
  - ```rust
    fn value_variants<''a>() -> &''a [Self] { /* ... */ }
    ```

  - ```rust
    fn to_possible_value<''a>(self: &Self) -> ::std::option::Option<clap::builder::PossibleValue> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Copy**
- **UnwindSafe**
- **RefUnwindSafe**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ConflictResolver { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> ConflictResolver { /* ... */ }
    ```

#### Struct `SatisfactionSolverOptions`

Options for the [`Solver`] which determine how it behaves.

```rust
pub struct SatisfactionSolverOptions {
    pub restart_options: crate::engine::RestartOptions,
    pub learning_clause_minimisation: bool,
    pub random_generator: rand::rngs::SmallRng,
    pub proof_log: crate::proof::ProofLog,
    pub conflict_resolver: ConflictResolver,
    pub learning_options: crate::propagators::nogoods::LearningOptions,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `restart_options` | `crate::engine::RestartOptions` | The options used by the restart strategy. |
| `learning_clause_minimisation` | `bool` | Whether learned clause minimisation should take place |
| `random_generator` | `rand::rngs::SmallRng` | A random number generator which is used by the [`Solver`] to determine randomised values. |
| `proof_log` | `crate::proof::ProofLog` | The proof log for the solver. |
| `conflict_resolver` | `ConflictResolver` | The resolver used for conflict analysis |
| `learning_options` | `crate::propagators::nogoods::LearningOptions` | The options which influence the learning of the solver. |

##### Implementations

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

#### Enum `CSPSolverStateInternal`

```rust
pub(in ::engine::constraint_satisfaction_solver) enum CSPSolverStateInternal {
    Ready,
    Solving,
    ContainsSolution,
    Conflict {
        conflict_info: stored_conflict_info::StoredConflictInfo,
    },
    Infeasible,
    InfeasibleUnderAssumptions {
        violated_assumption: crate::engine::predicates::predicate::Predicate,
    },
    Timeout,
}
```

##### Variants

###### `Ready`

###### `Solving`

###### `ContainsSolution`

###### `Conflict`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `conflict_info` | `stored_conflict_info::StoredConflictInfo` |  |

###### `Infeasible`

###### `InfeasibleUnderAssumptions`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `violated_assumption` | `crate::engine::predicates::predicate::Predicate` |  |

###### `Timeout`

##### Implementations

###### Trait Implementations

- **RefUnwindSafe**
- **Sync**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> CSPSolverStateInternal { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

#### Struct `CSPSolverState`

```rust
pub struct CSPSolverState {
    pub(in ::engine::constraint_satisfaction_solver) internal_state: CSPSolverStateInternal,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `internal_state` | `CSPSolverStateInternal` |  |

##### Implementations

###### Methods

- ```rust
  pub fn is_ready(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn no_conflict(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_conflicting(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_infeasible(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_inconsistent(self: &Self) -> bool { /* ... */ }
  ```
  Determines whether the current state is inconsistent; i.e. whether it is conflicting,

- ```rust
  pub fn is_infeasible_under_assumptions(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn get_violated_assumption(self: &Self) -> Predicate { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_conflict_info(self: &Self) -> StoredConflictInfo { /* ... */ }
  ```

- ```rust
  pub fn timeout(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn has_solution(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn declare_ready(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub fn declare_solving(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn declare_infeasible(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn declare_conflict(self: &mut Self, conflict_info: StoredConflictInfo) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn declare_solution_found(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn declare_timeout(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::constraint_satisfaction_solver) fn declare_infeasible_under_assumptions(self: &mut Self, violated_assumption: Predicate) { /* ... */ }
  ```

###### Trait Implementations

- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> CSPSolverState { /* ... */ }
    ```

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Freeze**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Sync**
## Module `cp`

```rust
pub(crate) mod cp { /* ... */ }
```

### Modules

## Module `assignments`

```rust
pub(in ::engine::cp) mod assignments { /* ... */ }
```

### Types

#### Struct `Assignments`

```rust
pub struct Assignments {
    pub(crate) trail: trail::Trail<ConstraintProgrammingTrailEntry>,
    pub(in ::engine::cp::assignments) domains: crate::containers::KeyedVec<crate::engine::variables::DomainId, IntegerDomain>,
    pub(in ::engine::cp::assignments) events: crate::engine::cp::event_sink::EventSink,
    pub(in ::engine::cp::assignments) backtrack_events: crate::engine::cp::event_sink::EventSink,
    pub(in ::engine::cp::assignments) pruned_values: u64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `trail` | `trail::Trail<ConstraintProgrammingTrailEntry>` |  |
| `domains` | `crate::containers::KeyedVec<crate::engine::variables::DomainId, IntegerDomain>` |  |
| `events` | `crate::engine::cp::event_sink::EventSink` |  |
| `backtrack_events` | `crate::engine::cp::event_sink::EventSink` |  |
| `pruned_values` | `u64` | The number of values that have been pruned from the domain. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn increase_decision_level(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn find_last_decision(self: &Self) -> Option<Predicate> { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_decision_level(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn num_domains(self: &Self) -> u32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_domains(self: &Self) -> DomainGeneratorIterator { /* ... */ }
  ```

- ```rust
  pub(crate) fn num_trail_entries(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_trail_entry(self: &Self, index: usize) -> ConstraintProgrammingTrailEntry { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_last_entry_on_trail(self: &Self) -> ConstraintProgrammingTrailEntry { /* ... */ }
  ```

- ```rust
  pub(crate) fn grow(self: &mut Self, lower_bound: i32, upper_bound: i32) -> DomainId { /* ... */ }
  ```

- ```rust
  pub fn create_new_integer_variable_sparse(self: &mut Self, values: Vec<i32>) -> DomainId { /* ... */ }
  ```

- ```rust
  pub(crate) fn drain_domain_events(self: &mut Self) -> impl Iterator<Item = (IntDomainEvent, DomainId)> + ''_ { /* ... */ }
  ```

- ```rust
  pub(crate) fn drain_backtrack_domain_events(self: &mut Self) -> impl Iterator<Item = (IntDomainEvent, DomainId)> + ''_ { /* ... */ }
  ```

- ```rust
  pub(crate) fn debug_create_empty_clone(self: &Self) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_initial_bound(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_lower_bound(self: &Self, domain_id: DomainId) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_lower_bound_at_trail_position(self: &Self, domain_id: DomainId, trail_position: usize) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_upper_bound(self: &Self, domain_id: DomainId) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_upper_bound_at_trail_position(self: &Self, domain_id: DomainId, trail_position: usize) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_initial_lower_bound(self: &Self, domain_id: DomainId) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_initial_upper_bound(self: &Self, domain_id: DomainId) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_initial_holes(self: &Self, domain_id: DomainId) -> Vec<i32> { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_assigned_value<Var: IntegerVariable + ''static>(self: &Self, var: &Var) -> Option<i32> { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_decision_predicate(self: &Self, predicate: &Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_domain_iterator(self: &Self, domain_id: DomainId) -> IntegerDomainIterator<''_> { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_domain_description(self: &Self, domain_id: DomainId) -> Vec<Predicate> { /* ... */ }
  ```
  Returns the conjunction of predicates that define the domain.

- ```rust
  pub(crate) fn is_value_in_domain(self: &Self, domain_id: DomainId, value: i32) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_value_in_domain_at_trail_position(self: &Self, domain_id: DomainId, value: i32, trail_position: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_domain_assigned<Var: IntegerVariable>(self: &Self, var: &Var) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_trail_position(self: &Self, predicate: &Predicate) -> Option<usize> { /* ... */ }
  ```
  Returns the index of the trail entry at which point the given predicate became true.

- ```rust
  pub(crate) fn get_decision_level_for_predicate(self: &Self, predicate: &Predicate) -> Option<usize> { /* ... */ }
  ```

- ```rust
  pub fn get_domain_descriptions(self: &Self) -> Vec<Predicate> { /* ... */ }
  ```

- ```rust
  pub(crate) fn tighten_lower_bound(self: &mut Self, domain_id: DomainId, new_lower_bound: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn tighten_upper_bound(self: &mut Self, domain_id: DomainId, new_upper_bound: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn make_assignment(self: &mut Self, domain_id: DomainId, assigned_value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove_value_from_domain(self: &mut Self, domain_id: DomainId, removed_value_from_domain: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn post_predicate(self: &mut Self, predicate: Predicate, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
  ```
  Apply the given [`Predicate`] to the integer domains.

- ```rust
  pub(crate) fn evaluate_predicate(self: &Self, predicate: Predicate) -> Option<bool> { /* ... */ }
  ```
  Determines whether the provided [`Predicate`] holds in the current state of the

- ```rust
  pub(crate) fn is_predicate_satisfied(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_predicate_falsified(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn synchronise(self: &mut Self, new_decision_level: usize, last_notified_trail_index: usize, is_watching_any_backtrack_events: bool) -> Vec<(DomainId, i32)> { /* ... */ }
  ```
  Synchronises the internal structures of [`Assignments`] based on the fact that

- ```rust
  pub(crate) fn remove_last_trail_element(self: &mut Self) { /* ... */ }
  ```
  todo: This is a temporary hack, not to be used in general.

- ```rust
  pub(crate) fn get_pruned_value_count(self: &Self) -> u64 { /* ... */ }
  ```
  Get the number of values pruned from all the domains.

###### Trait Implementations

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: &''a Assignments) -> Self { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Freeze**
- **Unpin**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Send**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> Assignments { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

#### Struct `EmptyDomain`

```rust
pub struct EmptyDomain;
```

##### Implementations

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **IntoEither**
- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(_: EmptyDomain) -> Self { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> EmptyDomain { /* ... */ }
    ```

- **Copy**
- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **Sync**
#### Struct `ConstraintProgrammingTrailEntry`

```rust
pub(crate) struct ConstraintProgrammingTrailEntry {
    pub(crate) predicate: crate::engine::predicates::predicate::Predicate,
    pub(crate) old_lower_bound: i32,
    pub(crate) old_upper_bound: i32,
    pub(crate) reason: Option<crate::engine::cp::reason::ReasonRef>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `predicate` | `crate::engine::predicates::predicate::Predicate` |  |
| `old_lower_bound` | `i32` | Explicitly store the bound before the predicate was applied so that it is easier later on<br> to update the bounds when backtracking. |
| `old_upper_bound` | `i32` |  |
| `reason` | `Option<crate::engine::cp::reason::ReasonRef>` | Stores the a reference to the reason in the `ReasonStore`, only makes sense if a<br>propagation  took place, e.g., does _not_ make sense in the case of a decision or if<br>the update was due  to synchronisation from the propositional trail. |

##### Implementations

###### Trait Implementations

- **UnwindSafe**
- **RefUnwindSafe**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> ConstraintProgrammingTrailEntry { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Copy**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Unpin**
#### Struct `PairDecisionLevelTrailPosition`

```rust
pub(in ::engine::cp::assignments) struct PairDecisionLevelTrailPosition {
    pub(in ::engine::cp::assignments) decision_level: usize,
    pub(in ::engine::cp::assignments) trail_position: usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `decision_level` | `usize` |  |
| `trail_position` | `usize` |  |

##### Implementations

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Copy**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> PairDecisionLevelTrailPosition { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
#### Struct `BoundUpdateInfo`

```rust
pub(in ::engine::cp::assignments) struct BoundUpdateInfo {
    pub(in ::engine::cp::assignments) bound: i32,
    pub(in ::engine::cp::assignments) decision_level: usize,
    pub(in ::engine::cp::assignments) trail_position: usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `bound` | `i32` |  |
| `decision_level` | `usize` |  |
| `trail_position` | `usize` |  |

##### Implementations

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> BoundUpdateInfo { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **IntoEither**
- **Freeze**
- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
#### Struct `HoleUpdateInfo`

```rust
pub(in ::engine::cp::assignments) struct HoleUpdateInfo {
    pub(in ::engine::cp::assignments) removed_value: i32,
    pub(in ::engine::cp::assignments) decision_level: usize,
    pub(in ::engine::cp::assignments) triggered_lower_bound_update: bool,
    pub(in ::engine::cp::assignments) triggered_upper_bound_update: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `removed_value` | `i32` |  |
| `decision_level` | `usize` |  |
| `triggered_lower_bound_update` | `bool` |  |
| `triggered_upper_bound_update` | `bool` |  |

##### Implementations

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Freeze**
- **Send**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> HoleUpdateInfo { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **IntoEither**
- **Unpin**
#### Struct `IntegerDomain`

This is the CP representation of a domain. It stores the bounds alongside holes in the domain.
When the domain is in an empty state, `lower_bound > upper_bound`.
The domain tracks all domain changes, so it is possible to query the domain at a given
cp trail position, i.e., the domain at some previous point in time.
This is needed to support lazy explanations.

```rust
pub(in ::engine::cp::assignments) struct IntegerDomain {
    pub(in ::engine::cp::assignments) id: crate::engine::variables::DomainId,
    pub(in ::engine::cp::assignments) lower_bound_updates: Vec<BoundUpdateInfo>,
    pub(in ::engine::cp::assignments) upper_bound_updates: Vec<BoundUpdateInfo>,
    pub(in ::engine::cp::assignments) hole_updates: Vec<HoleUpdateInfo>,
    pub(in ::engine::cp::assignments) holes: std::collections::HashMap<i32, PairDecisionLevelTrailPosition, fnv::FnvBuildHasher>,
    pub(in ::engine::cp::assignments) initial_bounds_below_trail: usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `id` | `crate::engine::variables::DomainId` |  |
| `lower_bound_updates` | `Vec<BoundUpdateInfo>` | The 'updates' fields chronologically records the changes to the domain. |
| `upper_bound_updates` | `Vec<BoundUpdateInfo>` |  |
| `hole_updates` | `Vec<HoleUpdateInfo>` |  |
| `holes` | `std::collections::HashMap<i32, PairDecisionLevelTrailPosition, fnv::FnvBuildHasher>` | Auxiliary data structure to make it easy to check if a value is present or not.<br>This is done to avoid going through 'hole_updates'.<br>It maps a removed value with its decision level and trail position.<br>In the future we could consider using direct hashing if the domain is small. |
| `initial_bounds_below_trail` | `usize` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::engine::cp::assignments) fn new(lower_bound: i32, upper_bound: i32, id: DomainId, initial_bounds_below_trail: usize) -> IntegerDomain { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn lower_bound(self: &Self) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn lower_bound_decision_level(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn initial_lower_bound(self: &Self) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn lower_bound_at_trail_position(self: &Self, trail_position: usize) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn upper_bound(self: &Self) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn upper_bound_decision_level(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn initial_upper_bound(self: &Self) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn upper_bound_at_trail_position(self: &Self, trail_position: usize) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn domain_iterator(self: &Self) -> IntegerDomainIterator<''_> { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn contains(self: &Self, value: i32) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn contains_at_trail_position(self: &Self, value: i32, trail_position: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn remove_value(self: &mut Self, removed_value: i32, decision_level: usize, trail_position: usize, events: &mut EventSink) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn debug_is_valid_upper_bound_domain_update(self: &Self, decision_level: usize, trail_position: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn set_upper_bound(self: &mut Self, new_upper_bound: i32, decision_level: usize, trail_position: usize, events: &mut EventSink) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn update_upper_bound_with_respect_to_holes(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn debug_is_valid_lower_bound_domain_update(self: &Self, decision_level: usize, trail_position: usize) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn set_lower_bound(self: &mut Self, new_lower_bound: i32, decision_level: usize, trail_position: usize, events: &mut EventSink) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn update_lower_bound_with_respect_to_holes(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn debug_bounds_check(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn verify_consistency(self: &Self) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn undo_trail_entry(self: &mut Self, entry: &ConstraintProgrammingTrailEntry) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::assignments) fn get_update_info(self: &Self, predicate: &Predicate) -> Option<PairDecisionLevelTrailPosition> { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Unpin**
- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Send**
- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> IntegerDomain { /* ... */ }
    ```

#### Struct `IntegerDomainIterator`

```rust
pub(crate) struct IntegerDomainIterator<''a> {
    pub(in ::engine::cp::assignments) domain: &''a IntegerDomain,
    pub(in ::engine::cp::assignments) current_value: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `domain` | `&''a IntegerDomain` |  |
| `current_value` | `i32` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::engine::cp::assignments) fn new(domain: &IntegerDomain) -> IntegerDomainIterator<''_> { /* ... */ }
  ```

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Itertools**
- **Send**
- **Unpin**
- **Iterator**
  - ```rust
    fn next(self: &mut Self) -> Option<i32> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoIterator**
  - ```rust
    fn into_iter(self: Self) -> I { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **IteratorRandom**
## Module `domain_events`

```rust
pub(crate) mod domain_events { /* ... */ }
```

### Types

#### Struct `DomainEvents`

```rust
pub(crate) struct DomainEvents {
    pub(in ::engine::cp::domain_events) int_events: Option<enumset::EnumSet<watch_list_cp::IntDomainEvent>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `int_events` | `Option<enumset::EnumSet<watch_list_cp::IntDomainEvent>>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) const fn create_with_int_events(int_events: EnumSet<IntDomainEvent>) -> DomainEvents { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_int_events(self: &Self) -> EnumSet<IntDomainEvent> { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> DomainEvents { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **Sync**
- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

## Module `event_sink`

```rust
pub(in ::engine::cp) mod event_sink { /* ... */ }
```

### Types

#### Struct `EventSink`

While a propagator runs (see [`propagators`]), the propagations it performs
are captured as events in the event sink. When the propagator finishes, the event sink is
drained to notify all the propagators that subscribe to those [`IntDomainEvent`].

Triggering any [`DomainEvents`] will also trigger the event [`DomainEvents::ANY_INT`].

The event sink will ensure duplicate events are ignored.

```rust
pub(crate) struct EventSink {
    pub(in ::engine::cp::event_sink) present: crate::containers::KeyedVec<crate::engine::variables::DomainId, enumset::EnumSet<watch_list_cp::IntDomainEvent>>,
    pub(in ::engine::cp::event_sink) events: Vec<(watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `present` | `crate::containers::KeyedVec<crate::engine::variables::DomainId, enumset::EnumSet<watch_list_cp::IntDomainEvent>>` |  |
| `events` | `Vec<(watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(num_domains: usize) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn grow(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn event_occurred(self: &mut Self, event: IntDomainEvent, domain: DomainId) { /* ... */ }
  ```

- ```rust
  pub(crate) fn drain(self: &mut Self) -> Drain<''_> { /* ... */ }
  ```
  Drain all the events from the [`EventSink`]. When the iterator is dropped, all remaining

- ```rust
  pub(crate) fn num_domains(self: &Self) -> usize { /* ... */ }
  ```

###### Trait Implementations

- **Send**
- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> EventSink { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **UnwindSafe**
- **Unpin**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> EventSink { /* ... */ }
    ```

#### Struct `Drain`

```rust
pub(crate) struct Drain<''a> {
    pub(in ::engine::cp::event_sink) present: &''a mut crate::containers::KeyedVec<crate::engine::variables::DomainId, enumset::EnumSet<watch_list_cp::IntDomainEvent>>,
    pub(in ::engine::cp::event_sink) drain: std::vec::Drain<''a, (watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `present` | `&''a mut crate::containers::KeyedVec<crate::engine::variables::DomainId, enumset::EnumSet<watch_list_cp::IntDomainEvent>>` |  |
| `drain` | `std::vec::Drain<''a, (watch_list_cp::IntDomainEvent, crate::engine::variables::DomainId)>` |  |

##### Implementations

###### Trait Implementations

- **DoubleEndedIterator**
  - ```rust
    fn next_back(self: &mut Self) -> Option<<Self as >::Item> { /* ... */ }
    ```

- **Iterator**
  - ```rust
    fn next(self: &mut Self) -> Option<<Self as >::Item> { /* ... */ }
    ```

  - ```rust
    fn size_hint(self: &Self) -> (usize, Option<usize>) { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IteratorRandom**
- **Sync**
- **UnwindSafe**
- **Itertools**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Drop**
  - ```rust
    fn drop(self: &mut Self) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **MultiUnzip**
  - ```rust
    fn multiunzip(self: Self) -> (FromA, FromB) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **ExactSizeIterator**
- **IntoIterator**
  - ```rust
    fn into_iter(self: Self) -> I { /* ... */ }
    ```

## Module `opaque_domain_event`

```rust
pub(crate) mod opaque_domain_event { /* ... */ }
```

### Types

#### Struct `OpaqueDomainEvent`

A wrapper for a domain event, which forces the propagator implementation to map the event
through the variable view.

```rust
pub struct OpaqueDomainEvent(pub(in ::engine::cp::opaque_domain_event) watch_list_cp::IntDomainEvent);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `watch_list_cp::IntDomainEvent` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn unwrap(self: Self) -> IntDomainEvent { /* ... */ }
  ```

###### Trait Implementations

- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OpaqueDomainEvent { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(event: IntDomainEvent) -> Self { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **Copy**
## Module `propagation`

Contains the main building blocks for propagators.

# Background

A propagator takes as input a set of variables (<code>x<sub>i</sub> ∈ X</code>) and for each
variable a corresponding domain (<code>D<sub>i</sub> ∈ D</code>); it can then be seen as a
function which maps `D ↦ D'` such that <code>D'<sub>i</sub> ⊆ D<sub>i</sub></code> for all
variables (i.e. the domain of a variable either remains the same after applying the propagator
or it becomes a subset of the domain before applying the propagator).

An example of a propagator can be the simple not equal (`!=`) propagator, suppose that
we have two variables `x ∈ {0}` and `y ∈ {0, 1}` and the constraint `x != y`. The not equal
propagator will then take as input the variables `x` and `y` and their respective domains
<code>D = {D<sub>x</sub> = {0}, D<sub>y</sub> = {0, 1}</code> and produce a new domain <code>D'
= {D'<sub>x</sub> = {0}, D'<sub>y</sub> = {1}}</code> for which we can see that <code>D_x =
D'<sub>x</sub></code> and <code>D'<sub>y</sub> ⊆ D<sub>y</sub></code>.

A propagator is said to be at fix-point if <code>D<sub>x</sub> = D'<sub>x</sub></code> meaning
that no further propagations can take place when applying the propagator. A propagator is said
to be "idempotent" if a single call to it will result in it being at fix-point.

For more information about the construction of these types of propagation-based solvers, we
refer to [\[1\]](https://dl.acm.org/doi/pdf/10.1145/1452044.1452046).

# Practical

Each concrete propagator is associated with one trait: [`Propagator`]. This trait contains the
functions which are required to be implemented by the propagator such as
[`Propagator::propagate`], [`Propagator::initialise_at_root`], and [`Propagator::notify`].

A [`Propagator`] can be notified of different domain changes to a variable by registering
variables using [`PropagatorInitialisationContext::register`] (and
[`PropagatorInitialisationContext::register_literal`]) which are provided when
[`Propagator::initialise_at_root`] is called. When domain changes happen for a variable outside
the propagator, the propagator will receive information that its variable with a specific
[`LocalId`] has changed (see [`Propagator::notify`]). The idea behind using the structs apart
from [`Propagator`] is to support views \[2\] (e.g. see [`AffineView`]) on variables.

We do not require propagators to be idempotent (see the previous section for a
definition) and it can be assumed that if a propagator is not at fix-point after propagating
that it will be called again by the solver until no further propagations happen.

See the [`propagators`] folder for concrete propagator implementations.

# How to implement a new propagator?

We recommend the following workflow:
1. Implement a propagator struct that implements the [`Propagator`] trait. For now only
   implement the required functions, i.e., [`Propagator::debug_propagate_from_scratch`] and
   [`Propagator::name`].
2. Implement the [`Propagator::initialise_at_root`] function which detects root-level
   inconsistencies and is also responsible for registering the variables and corresponding
   [`DomainEvents`] with the solver, so that the solver can notify the propagator once an event
   happens that relates to one of the variables of the propagator.
3. Following the procedure above gives an initial version of the propagator that is likely not
   efficient, but has an important role for testing. Now is a good time to write tests which use
   the [`TestSolver`]. **We strongly discourage skipping this step**.
    * For example, see the tests in [`crate::propagators::arithmetic::absolute_value`].
4. Implement [`Propagator::notify`]. Depending on the concrete propagator, this may only make
   sense when done together with the next step.
5. Implement the remaining functions, i.e., [`Propagator::propagate`],
   [`Propagator::synchronise`], and [`Propagator::initialise_at_root`]. These are all
   interdependent.
6. Decide on the priortiy of the propagator, i.e., implement [`Propagator::priority`].
7. Make sure to write new tests and run all tests throughout the process.
8. The propagator implementation is now done!

The propagator is added to the solver through [`ConstraintSatisfactionSolver::add_propagator`].

# Bibliography

\[1\] C. Schulte and P. J. Stuckey, ‘Efficient constraint propagation engines’, ACM Transactions
on Programming Languages and Systems (TOPLAS), vol. 31, no. 1, pp. 1–43, 2008.

\[2\] C. Schulte and G. Tack, ‘Views and iterators for generic constraint implementations’, in
International Workshop on Constraint Solving and Constraint Logic Programming, 2005, pp.
118–132.

```rust
pub(crate) mod propagation { /* ... */ }
```

### Modules

## Module `contexts`

```rust
pub(crate) mod contexts { /* ... */ }
```

### Modules

## Module `explanation_context`

```rust
pub(crate) mod explanation_context { /* ... */ }
```

### Types

#### Struct `ExplanationContext`

The context that is available when lazily explaining propagations.

See [`pumpkin_solver::engine::propagation::Propagator`] for more information.

```rust
pub(crate) struct ExplanationContext<''a> {
    pub(in ::engine::cp::propagation::contexts::explanation_context) assignments: &''a assignments::Assignments,
    pub(in ::engine::cp::propagation::contexts::explanation_context) current_nogood: CurrentNogood<''a>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `&''a assignments::Assignments` |  |
| `current_nogood` | `CurrentNogood<''a>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(assignments: &''a Assignments, current_nogood: CurrentNogood<''a>) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn working_nogood(self: &Self) -> impl Iterator<Item = Predicate> + ''_ { /* ... */ }
  ```
  Get the current working nogood.

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **Sync**
- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &Assignments { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: &''a Assignments) -> Self { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

#### Struct `CurrentNogood`

```rust
pub(crate) struct CurrentNogood<''a> {
    pub(in ::engine::cp::propagation::contexts::explanation_context) heap: &''a crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, u32>,
    pub(in ::engine::cp::propagation::contexts::explanation_context) visited: &''a [crate::predicates::Predicate],
    pub(in ::engine::cp::propagation::contexts::explanation_context) ids: &''a predicate_id_generator::PredicateIdGenerator,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `heap` | `&''a crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, u32>` |  |
| `visited` | `&''a [crate::predicates::Predicate]` |  |
| `ids` | `&''a predicate_id_generator::PredicateIdGenerator` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(heap: &''a KeyValueHeap<PredicateId, u32>, visited: &''a [Predicate], ids: &''a PredicateIdGenerator) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn empty() -> CurrentNogood<''a> { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::propagation::contexts::explanation_context) fn iter<''this, ''ids>(self: &''this Self) -> impl Iterator<Item = Predicate> + ''this
where
    ''ids: ''this { /* ... */ }
  ```

###### Trait Implementations

- **Freeze**
- **Send**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: &''a [Predicate]) -> Self { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

### Constants and Statics

#### Static `EMPTY_HEAP`

```rust
pub(in ::engine::cp::propagation::contexts::explanation_context) static EMPTY_HEAP: crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, u32> = _;
```

#### Static `EMPTY_PREDICATE_IDS`

```rust
pub(in ::engine::cp::propagation::contexts::explanation_context) static EMPTY_PREDICATE_IDS: std::sync::LazyLock<predicate_id_generator::PredicateIdGenerator> = _;
```

#### Static `EMPTY_PREDICATES`

```rust
pub(in ::engine::cp::propagation::contexts::explanation_context) static EMPTY_PREDICATES: [crate::predicates::Predicate; 0] = _;
```

## Module `propagation_context`

```rust
pub(crate) mod propagation_context { /* ... */ }
```

### Modules

## Module `private`

```rust
pub(in ::engine::cp::propagation::contexts::propagation_context) mod private { /* ... */ }
```

### Types

#### Struct `StatefulPropagationContext`

```rust
pub(crate) struct StatefulPropagationContext<''a> {
    pub(crate) stateful_assignments: &''a mut crate::engine::TrailedAssignments,
    pub(crate) assignments: &''a assignments::Assignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `stateful_assignments` | `&''a mut crate::engine::TrailedAssignments` |  |
| `assignments` | `&''a assignments::Assignments` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(stateful_assignments: &''a mut TrailedAssignments, assignments: &''a Assignments) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn as_readonly(self: &Self) -> PropagationContext<''_> { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **HasStatefulAssignments**
  - ```rust
    fn stateful_assignments(self: &Self) -> &TrailedAssignments { /* ... */ }
    ```

  - ```rust
    fn stateful_assignments_mut(self: &mut Self) -> &mut TrailedAssignments { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &Assignments { /* ... */ }
    ```

- **Unpin**
- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

#### Struct `PropagationContext`

[`PropagationContext`] is passed to propagators during propagation.
It may be queried to retrieve information about the current variable domains such as the
lower-bound of a particular variable, or used to apply changes to the domain of a variable
e.g. set `[x >= 5]`.


Note that the [`PropagationContext`] is the only point of communication beween
the propagations and the solver during propagation.

```rust
pub(crate) struct PropagationContext<''a> {
    pub assignments: &''a assignments::Assignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `&''a assignments::Assignments` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(assignments: &''a Assignments) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &Assignments { /* ... */ }
    ```

- **RefUnwindSafe**
- **Unpin**
- **Send**
- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> PropagationContext<''a> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Copy**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

#### Struct `PropagationContextMut`

```rust
pub(crate) struct PropagationContextMut<''a> {
    pub(crate) stateful_assignments: &''a mut crate::engine::TrailedAssignments,
    pub(crate) assignments: &''a mut assignments::Assignments,
    pub(crate) reason_store: &''a mut crate::engine::reason::ReasonStore,
    pub(crate) propagator_id: propagator_id::PropagatorId,
    pub(crate) semantic_minimiser: &''a mut crate::engine::conflict_analysis::SemanticMinimiser,
    pub(in ::engine::cp::propagation::contexts::propagation_context) reification_literal: Option<crate::engine::variables::Literal>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `stateful_assignments` | `&''a mut crate::engine::TrailedAssignments` |  |
| `assignments` | `&''a mut assignments::Assignments` |  |
| `reason_store` | `&''a mut crate::engine::reason::ReasonStore` |  |
| `propagator_id` | `propagator_id::PropagatorId` |  |
| `semantic_minimiser` | `&''a mut crate::engine::conflict_analysis::SemanticMinimiser` |  |
| `reification_literal` | `Option<crate::engine::variables::Literal>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(stateful_assignments: &''a mut TrailedAssignments, assignments: &''a mut Assignments, reason_store: &''a mut ReasonStore, semantic_minimiser: &''a mut SemanticMinimiser, propagator_id: PropagatorId) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn with_reification(self: &mut Self, reification_literal: Literal) { /* ... */ }
  ```
  Apply a reification literal to all the explanations that are passed to the context.

- ```rust
  pub(in ::engine::cp::propagation::contexts::propagation_context) fn build_reason(self: &Self, reason: Reason) -> StoredReason { /* ... */ }
  ```

- ```rust
  pub(crate) fn as_stateful_readonly(self: &mut Self) -> StatefulPropagationContext<''_> { /* ... */ }
  ```

- ```rust
  pub(crate) fn as_readonly(self: &Self) -> PropagationContext<''_> { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_decision_level(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove<Var: IntegerVariable, R: Into<Reason>>(self: &mut Self, var: &Var, value: i32, reason: R) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_upper_bound<Var: IntegerVariable, R: Into<Reason>>(self: &mut Self, var: &Var, bound: i32, reason: R) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_lower_bound<Var: IntegerVariable, R: Into<Reason>>(self: &mut Self, var: &Var, bound: i32, reason: R) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn evaluate_predicate(self: &Self, predicate: Predicate) -> Option<bool> { /* ... */ }
  ```

- ```rust
  pub(crate) fn post_predicate<R: Into<Reason>>(self: &mut Self, predicate: Predicate, reason: R) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn assign_literal<R: Into<Reason> + Clone>(self: &mut Self, boolean: &Literal, truth_value: bool, reason: R) -> Result<(), EmptyDomain> { /* ... */ }
  ```

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **HasStatefulAssignments**
  - ```rust
    fn stateful_assignments(self: &Self) -> &TrailedAssignments { /* ... */ }
    ```

  - ```rust
    fn stateful_assignments_mut(self: &mut Self) -> &mut TrailedAssignments { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &Assignments { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **Unpin**
### Traits

#### Trait `HasAssignments`

A trait which defines common methods for retrieving the [`Assignments`] and
[`AssignmentsPropositional`] from the structure which implements this trait.

```rust
pub trait HasAssignments {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `assignments`: Returns the stored [`Assignments`].

##### Implementations

This trait is implemented for the following types:

- `SolutionReference<''a>` with <''a>
- `Solution`
- `ExplanationContext<''_>`
- `PropagationContext<''_>`
- `PropagationContextMut<''_>`
- `StatefulPropagationContext<''_>`
- `PropagatorInitialisationContext<''_>`

#### Trait `HasStatefulAssignments`

```rust
pub(crate) trait HasStatefulAssignments {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `stateful_assignments`
- `stateful_assignments_mut`

##### Implementations

This trait is implemented for the following types:

- `StatefulPropagationContext<''_>`
- `PropagationContextMut<''_>`
- `PropagatorInitialisationContext<''_>`

#### Trait `ManipulateStatefulIntegers`

```rust
pub(crate) trait ManipulateStatefulIntegers: HasStatefulAssignments {
    /* Associated items */
}
```

##### Provided Methods

- ```rust
  fn new_stateful_integer(self: &mut Self, initial_value: i64) -> TrailedInt { /* ... */ }
  ```

- ```rust
  fn value(self: &Self, stateful_integer: TrailedInt) -> i64 { /* ... */ }
  ```

- ```rust
  fn add_assign(self: &mut Self, stateful_integer: TrailedInt, addition: i64) { /* ... */ }
  ```

- ```rust
  fn assign(self: &mut Self, stateful_integer: TrailedInt, value: i64) { /* ... */ }
  ```

##### Implementations

This trait is implemented for the following types:

- `T` with <T: HasStatefulAssignments>

#### Trait `ReadDomains`

```rust
pub(crate) trait ReadDomains: HasAssignments {
    /* Associated items */
}
```

> This trait is not object-safe and cannot be used in dynamic trait objects.

##### Provided Methods

- ```rust
  fn is_predicate_satisfied(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  fn is_predicate_falsified(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  fn is_literal_true(self: &Self, literal: &Literal) -> bool { /* ... */ }
  ```

- ```rust
  fn is_literal_false(self: &Self, literal: &Literal) -> bool { /* ... */ }
  ```

- ```rust
  fn is_literal_fixed(self: &Self, literal: &Literal) -> bool { /* ... */ }
  ```

- ```rust
  fn is_fixed<Var: IntegerVariable>(self: &Self, var: &Var) -> bool { /* ... */ }
  ```
  Returns `true` if the domain of the given variable is singleton.

- ```rust
  fn lower_bound<Var: IntegerVariable>(self: &Self, var: &Var) -> i32 { /* ... */ }
  ```

- ```rust
  fn lower_bound_at_trail_position<Var: IntegerVariable>(self: &Self, var: &Var, trail_position: usize) -> i32 { /* ... */ }
  ```

- ```rust
  fn upper_bound<Var: IntegerVariable>(self: &Self, var: &Var) -> i32 { /* ... */ }
  ```

- ```rust
  fn upper_bound_at_trail_position<Var: IntegerVariable>(self: &Self, var: &Var, trail_position: usize) -> i32 { /* ... */ }
  ```

- ```rust
  fn contains<Var: IntegerVariable>(self: &Self, var: &Var, value: i32) -> bool { /* ... */ }
  ```

- ```rust
  fn iterate_domain<Var: IntegerVariable>(self: &Self, var: &Var) -> impl Iterator<Item = i32> { /* ... */ }
  ```

##### Implementations

This trait is implemented for the following types:

- `T` with <T: HasAssignments>

## Module `propagator_initialisation_context`

```rust
pub(crate) mod propagator_initialisation_context { /* ... */ }
```

### Modules

## Module `private`

```rust
pub(in ::engine::cp::propagation::contexts::propagator_initialisation_context) mod private { /* ... */ }
```

### Types

#### Struct `PropagatorInitialisationContext`

[`PropagatorInitialisationContext`] is used when [`Propagator`]s are initialised after creation.

It represents a communication point between the [`Solver`] and the [`Propagator`].
Propagators use the [`PropagatorInitialisationContext`] to register to domain changes
of variables and to retrieve the current bounds of variables.

```rust
pub(crate) struct PropagatorInitialisationContext<''a> {
    pub(in ::engine::cp::propagation::contexts::propagator_initialisation_context) watch_list: &''a mut watch_list_cp::WatchListCP,
    pub(crate) stateful_assignments: &''a mut crate::engine::TrailedAssignments,
    pub(in ::engine::cp::propagation::contexts::propagator_initialisation_context) propagator_id: propagator_id::PropagatorId,
    pub(in ::engine::cp::propagation::contexts::propagator_initialisation_context) next_local_id: local_id::LocalId,
    pub assignments: &''a mut assignments::Assignments,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `watch_list` | `&''a mut watch_list_cp::WatchListCP` |  |
| `stateful_assignments` | `&''a mut crate::engine::TrailedAssignments` |  |
| `propagator_id` | `propagator_id::PropagatorId` |  |
| `next_local_id` | `local_id::LocalId` |  |
| `assignments` | `&''a mut assignments::Assignments` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new<''a>(watch_list: &''a mut WatchListCP, stateful_assignments: &''a mut TrailedAssignments, propagator_id: PropagatorId, assignments: &''a mut Assignments) -> PropagatorInitialisationContext<''a> { /* ... */ }
  ```

- ```rust
  pub(crate) fn as_stateful_readonly(self: &mut Self) -> StatefulPropagationContext<''_> { /* ... */ }
  ```

- ```rust
  pub(crate) fn as_readonly(self: &Self) -> PropagationContext<''_> { /* ... */ }
  ```

- ```rust
  pub(crate) fn register<Var: IntegerVariable>(self: &mut Self, var: Var, domain_events: DomainEvents, local_id: LocalId) -> Var { /* ... */ }
  ```
  Subscribes the propagator to the given [`DomainEvents`].

- ```rust
  pub(crate) fn register_for_backtrack_events<Var: IntegerVariable>(self: &mut Self, var: Var, domain_events: DomainEvents, local_id: LocalId) -> Var { /* ... */ }
  ```
  Subscribes the propagator to the given [`DomainEvents`] when they are undone during

- ```rust
  pub(crate) fn get_next_local_id(self: &Self) -> LocalId { /* ... */ }
  ```

###### Trait Implementations

- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Send**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **HasAssignments**
  - ```rust
    fn assignments(self: &Self) -> &Assignments { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **HasStatefulAssignments**
  - ```rust
    fn stateful_assignments(self: &Self) -> &TrailedAssignments { /* ... */ }
    ```

  - ```rust
    fn stateful_assignments_mut(self: &mut Self) -> &mut TrailedAssignments { /* ... */ }
    ```

## Module `local_id`

```rust
pub(crate) mod local_id { /* ... */ }
```

### Types

#### Struct `LocalId`

A local id uniquely identifies a variable within a specific propagator. A local id can be
thought of as the index of the variable in the propagator.

```rust
pub(crate) struct LocalId(pub(in ::engine::cp::propagation::local_id) u32);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `u32` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) const fn from(value: u32) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn unpack(self: Self) -> u32 { /* ... */ }
  ```

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **StructuralPartialEq**
- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Copy**
- **UnwindSafe**
- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &LocalId) -> bool { /* ... */ }
    ```

- **Ord**
  - ```rust
    fn cmp(self: &Self, other: &LocalId) -> $crate::cmp::Ordering { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LocalId { /* ... */ }
    ```

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **PartialOrd**
  - ```rust
    fn partial_cmp(self: &Self, other: &LocalId) -> $crate::option::Option<$crate::cmp::Ordering> { /* ... */ }
    ```

- **IntoEither**
- **Freeze**
- **Send**
- **Eq**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
## Module `propagator`

```rust
pub(crate) mod propagator { /* ... */ }
```

### Types

#### Enum `EnqueueDecision`

Indicator of what to do when a propagator is notified.

```rust
pub(crate) enum EnqueueDecision {
    Enqueue,
    Skip,
}
```

##### Variants

###### `Enqueue`

The propagator should be enqueued.

###### `Skip`

The propagator should not be enqueued.

##### Implementations

###### Trait Implementations

- **UnwindSafe**
- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Eq**
- **IntoEither**
- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> EnqueueDecision { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Copy**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **StructuralPartialEq**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &EnqueueDecision) -> bool { /* ... */ }
    ```

### Traits

#### Trait `Propagator`

All propagators implement the [`Propagator`] trait, which defines the main propagator logic with
regards to propagation, detecting conflicts, and providing explanations.

The only required functions are [`Propagator::name`],
[`Propagator::initialise_at_root`], and [`Propagator::debug_propagate_from_scratch`]; all other
functions have default implementations. For initial development, the required functions are
enough, but a more mature implementation considers all functions in most cases.

See the [`crate::engine::cp::propagation`] documentation for more details.

```rust
pub(crate) trait Propagator: Downcast {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `name`: Return the name of the propagator, this is a convenience method that is used for printing.
- `debug_propagate_from_scratch`: A propagation method that is used to help debugging.
- `initialise_at_root`: Initialises the propagator without performing propagation. This method is called only once

##### Provided Methods

- ```rust
  fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Propagate method that will be called during search (e.g. in

- ```rust
  fn notify(self: &mut Self, _context: StatefulPropagationContext<''_>, _local_id: LocalId, _event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
  ```
  Called when an event happens to one of the variables the propagator is subscribed to. It

- ```rust
  fn notify_backtrack(self: &mut Self, _context: PropagationContext<''_>, _local_id: LocalId, _event: OpaqueDomainEvent) { /* ... */ }
  ```
  Called when an event happens to one of the variables the propagator is subscribed to. This

- ```rust
  fn synchronise(self: &mut Self, _context: PropagationContext<''_>) { /* ... */ }
  ```
  Called each time the [`ConstraintSatisfactionSolver`] backtracks, the propagator can then

- ```rust
  fn priority(self: &Self) -> u32 { /* ... */ }
  ```
  Returns the priority of the propagator represented as an integer. Lower values mean higher

- ```rust
  fn detect_inconsistency(self: &Self, _context: StatefulPropagationContext<''_>) -> Option<PropositionalConjunction> { /* ... */ }
  ```
  A check whether this propagator can detect an inconsistency.

- ```rust
  fn lazy_explanation(self: &mut Self, _code: u64, _context: ExplanationContext<''_>) -> &[Predicate] { /* ... */ }
  ```
  Hook which is called when a propagation was done with a lazy reason.

- ```rust
  fn log_statistics(self: &Self, _statistic_logger: StatisticLogger) { /* ... */ }
  ```
  Logs statistics of the propagator using the provided [`StatisticLogger`].

##### Implementations

This trait is implemented for the following types:

- `AbsoluteValuePropagator<VA, VB>` with <VA: IntegerVariable + ''static, VB: IntegerVariable + ''static>
- `DivisionPropagator<VA, VB, VC>` with <VA, VB, VC>
- `IntegerMultiplicationPropagator<VA, VB, VC>` with <VA, VB, VC>
- `LinearLessOrEqualPropagator<Var>` with <Var>
- `LinearNotEqualPropagator<Var>` with <Var>
- `MaximumPropagator<ElementVar, Rhs>` with <ElementVar: IntegerVariable + ''static, Rhs: IntegerVariable + ''static>
- `TimeTableOverIntervalIncrementalPropagator<Var, SYNCHRONISE>` with <Var: IntegerVariable + ''static, const SYNCHRONISE: bool>
- `TimeTablePerPointIncrementalPropagator<Var, SYNCHRONISE>` with <Var: IntegerVariable + ''static + Debug, const SYNCHRONISE: bool>
- `TimeTableOverIntervalPropagator<Var>` with <Var: IntegerVariable + ''static>
- `TimeTablePerPointPropagator<Var>` with <Var: IntegerVariable + ''static>
- `ElementPropagator<VX, VI, VE>` with <VX, VI, VE>
- `NogoodPropagator`
- `ReifiedPropagator<WrappedPropagator>` with <WrappedPropagator: Propagator>

## Module `propagator_id`

```rust
pub(crate) mod propagator_id { /* ... */ }
```

### Types

#### Struct `PropagatorId`

**Attributes:**

- `#[repr(transparent)]`

An identifier to a propagator instance within the solver.
Each propagator is assigned a unique identifier at runtime.

```rust
pub(crate) struct PropagatorId(pub(crate) u32);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `u32` |  |

##### Implementations

###### Trait Implementations

- **Index**
  - ```rust
    fn index(self: &Self, index: PropagatorId) -> &<Self as >::Output { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IndexMut**
  - ```rust
    fn index_mut(self: &mut Self, index: PropagatorId) -> &mut <Self as >::Output { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **RefUnwindSafe**
- **IntoEither**
- **Copy**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Eq**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **StructuralPartialEq**
- **Send**
- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> PropagatorId { /* ... */ }
    ```

- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **StorageKey**
  - ```rust
    fn index(self: &Self) -> usize { /* ... */ }
    ```

  - ```rust
    fn create_from_index(index: usize) -> Self { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &PropagatorId) -> bool { /* ... */ }
    ```

## Module `propagator_var_id`

```rust
pub(crate) mod propagator_var_id { /* ... */ }
```

### Types

#### Struct `PropagatorVarId`

A handle to a variable registered to a propagator.

```rust
pub(crate) struct PropagatorVarId {
    pub(crate) propagator: propagator_id::PropagatorId,
    pub(crate) variable: local_id::LocalId,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `propagator` | `propagator_id::PropagatorId` |  |
| `variable` | `local_id::LocalId` |  |

##### Implementations

###### Trait Implementations

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **StructuralPartialEq**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> PropagatorVarId { /* ... */ }
    ```

- **Unpin**
- **Sync**
- **IntoEither**
- **Eq**
- **Send**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Copy**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &PropagatorVarId) -> bool { /* ... */ }
    ```

- **Freeze**
## Module `store`

```rust
pub(crate) mod store { /* ... */ }
```

### Types

#### Struct `PropagatorStore`

A central store for propagators.

The propagator store associates tags with propagators, whenever a tag is provided for a
propagator.

```rust
pub(crate) struct PropagatorStore {
    pub(in ::engine::cp::propagation::store) propagators: crate::containers::KeyedVec<propagator_id::PropagatorId, Box<dyn Propagator>>,
    pub(in ::engine::cp::propagation::store) tags: crate::containers::KeyedVec<propagator_id::PropagatorId, Option<std::num::NonZero<u32>>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `propagators` | `crate::containers::KeyedVec<propagator_id::PropagatorId, Box<dyn Propagator>>` |  |
| `tags` | `crate::containers::KeyedVec<propagator_id::PropagatorId, Option<std::num::NonZero<u32>>>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn alloc(self: &mut Self, propagator: Box<dyn Propagator>, tag: Option<NonZero<u32>>) -> PropagatorId { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_tag(self: &Self, propagator_id: PropagatorId) -> Option<NonZero<u32>> { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_propagators(self: &Self) -> impl Iterator<Item = &dyn Propagator> + ''_ { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_propagators_mut(self: &mut Self) -> impl Iterator<Item = &mut Box<dyn Propagator>> + ''_ { /* ... */ }
  ```

###### Trait Implementations

- **IntoEither**
- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **Default**
  - ```rust
    fn default() -> PropagatorStore { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Index**
  - ```rust
    fn index(self: &Self, index: PropagatorId) -> &<Self as >::Output { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Unpin**
- **IndexMut**
  - ```rust
    fn index_mut(self: &mut Self, index: PropagatorId) -> &mut <Self as >::Output { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

## Module `propagator_queue`

```rust
pub(in ::engine::cp) mod propagator_queue { /* ... */ }
```

### Types

#### Struct `PropagatorQueue`

```rust
pub(crate) struct PropagatorQueue {
    pub(in ::engine::cp::propagator_queue) queues: Vec<std::collections::VecDeque<propagator_id::PropagatorId>>,
    pub(in ::engine::cp::propagator_queue) present_propagators: std::collections::HashSet<propagator_id::PropagatorId, fnv::FnvBuildHasher>,
    pub(in ::engine::cp::propagator_queue) present_priorities: std::collections::BinaryHeap<std::cmp::Reverse<u32>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `queues` | `Vec<std::collections::VecDeque<propagator_id::PropagatorId>>` |  |
| `present_propagators` | `std::collections::HashSet<propagator_id::PropagatorId, fnv::FnvBuildHasher>` |  |
| `present_priorities` | `std::collections::BinaryHeap<std::cmp::Reverse<u32>>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(num_priority_levels: u32) -> PropagatorQueue { /* ... */ }
  ```

- ```rust
  pub(crate) fn enqueue_propagator(self: &mut Self, propagator_id: PropagatorId, priority: u32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn pop(self: &mut Self) -> Option<PropagatorId> { /* ... */ }
  ```

- ```rust
  pub(crate) fn clear(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::propagator_queue) fn is_propagator_enqueued(self: &Self, propagator_id: PropagatorId) -> bool { /* ... */ }
  ```

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **IntoEither**
- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `reason`

```rust
pub(crate) mod reason { /* ... */ }
```

### Types

#### Struct `ReasonStore`

The reason store holds a reason for each change made by a CP propagator on a trail.

```rust
pub(crate) struct ReasonStore {
    pub(in ::engine::cp::reason) trail: trail::Trail<(propagator_id::PropagatorId, StoredReason)>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `trail` | `trail::Trail<(propagator_id::PropagatorId, StoredReason)>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn push(self: &mut Self, propagator: PropagatorId, reason: StoredReason) -> ReasonRef { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_or_compute</* synthetic */ impl Extend<Predicate>: Extend<Predicate>>(self: &Self, reference: ReasonRef, context: ExplanationContext<''_>, propagators: &mut PropagatorStore, destination_buffer: &mut impl Extend<Predicate>) -> bool { /* ... */ }
  ```
  Evaluate the reason with the given reference, and write the predicates to

- ```rust
  pub(crate) fn get_lazy_code(self: &Self, reference: ReasonRef) -> Option<&u64> { /* ... */ }
  ```

- ```rust
  pub(crate) fn increase_decision_level(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn synchronise(self: &mut Self, level: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_propagator(self: &Self, reason_ref: ReasonRef) -> PropagatorId { /* ... */ }
  ```
  Get the propagator which generated the given reason.

###### Trait Implementations

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Sync**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> ReasonStore { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

#### Struct `ReasonRef`

A reference to a reason

```rust
pub struct ReasonRef(pub(crate) u32);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `u32` |  |

##### Implementations

###### Trait Implementations

- **Default**
  - ```rust
    fn default() -> ReasonRef { /* ... */ }
    ```

- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ReasonRef { /* ... */ }
    ```

- **Copy**
- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &ReasonRef) -> bool { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **Eq**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **StructuralPartialEq**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **Unpin**
- **RefUnwindSafe**
#### Enum `Reason`

A reason for CP propagator to make a change

```rust
pub(crate) enum Reason {
    Eager(crate::basic_types::PropositionalConjunction),
    DynamicLazy(u64),
}
```

##### Variants

###### `Eager`

An eager reason contains the propositional conjunction with the reason, without the
  propagated predicate.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::PropositionalConjunction` |  |

###### `DynamicLazy`

A lazy reason, which is computed on-demand rather than up-front. This is also referred to
as a 'backward' reason.

A lazy reason contains a payload that propagators can use to identify what type of
propagation the reason is for. The payload should be enough for the propagator to construct
an explanation based on its internal state.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `u64` |  |

##### Implementations

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: PropositionalConjunction) -> Self { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Send**
- **UnwindSafe**
#### Enum `StoredReason`

A reason for CP propagator to make a change

```rust
pub(crate) enum StoredReason {
    Eager(crate::basic_types::PropositionalConjunction),
    DynamicLazy(u64),
    ReifiedLazy(crate::variables::Literal, u64),
}
```

##### Variants

###### `Eager`

An eager reason contains the propositional conjunction with the reason, without the
  propagated predicate.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::PropositionalConjunction` |  |

###### `DynamicLazy`

A lazy reason, which is computed on-demand rather than up-front. This is also referred to
as a 'backward' reason.

A lazy reason contains a payload that propagators can use to identify what type of
propagation the reason is for. The payload should be enough for the propagator to construct
an explanation based on its internal state.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `u64` |  |

###### `ReifiedLazy`

A lazy explanation that has been reified.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::variables::Literal` |  |
| 1 | `u64` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn compute</* synthetic */ impl Extend<Predicate>: Extend<Predicate>>(self: &Self, context: ExplanationContext<''_>, propagator_id: PropagatorId, propagators: &mut PropagatorStore, destination_buffer: &mut impl Extend<Predicate>) { /* ... */ }
  ```
  Evaluate the reason, and write the predicates to the `destination_buffer`.

###### Trait Implementations

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Freeze**
## Module `test_solver`

**Attributes:**

- `#[<cfg>(any(test, doc))]`

This module exposes helpers that aid testing of CP propagators. The [`TestSolver`] allows
setting up specific scenarios under which to test the various operations of a propagator.

```rust
pub(crate) mod test_solver { /* ... */ }
```

### Types

#### Struct `TestSolver`

A container for CP variables, which can be used to test propagators.

```rust
pub(crate) struct TestSolver {
    pub assignments: assignments::Assignments,
    pub propagator_store: super::propagation::store::PropagatorStore,
    pub reason_store: crate::engine::reason::ReasonStore,
    pub semantic_minimiser: crate::engine::conflict_analysis::SemanticMinimiser,
    pub stateful_assignments: super::TrailedAssignments,
    pub(in ::engine::cp::test_solver) watch_list: watch_list_cp::WatchListCP,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `assignments::Assignments` |  |
| `propagator_store` | `super::propagation::store::PropagatorStore` |  |
| `reason_store` | `crate::engine::reason::ReasonStore` |  |
| `semantic_minimiser` | `crate::engine::conflict_analysis::SemanticMinimiser` |  |
| `stateful_assignments` | `super::TrailedAssignments` |  |
| `watch_list` | `watch_list_cp::WatchListCP` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new_variable(self: &mut Self, lb: i32, ub: i32) -> DomainId { /* ... */ }
  ```

- ```rust
  pub(crate) fn new_literal(self: &mut Self) -> Literal { /* ... */ }
  ```

- ```rust
  pub(crate) fn new_propagator</* synthetic */ impl Propagator + 'static: Propagator + ''static>(self: &mut Self, propagator: impl Propagator + ''static) -> Result<PropagatorId, Inconsistency> { /* ... */ }
  ```

- ```rust
  pub(crate) fn contains<Var: IntegerVariable>(self: &Self, var: Var, value: i32) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn lower_bound(self: &Self, var: DomainId) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn increase_lower_bound_and_notify(self: &mut Self, propagator: PropagatorId, local_id: u32, var: DomainId, value: i32) -> EnqueueDecision { /* ... */ }
  ```

- ```rust
  pub(crate) fn decrease_upper_bound_and_notify(self: &mut Self, propagator: PropagatorId, local_id: u32, var: DomainId, value: i32) -> EnqueueDecision { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_literal_false(self: &Self, literal: Literal) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn upper_bound(self: &Self, var: DomainId) -> i32 { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove(self: &mut Self, var: DomainId, value: i32) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_literal(self: &mut Self, literal: Literal, truth_value: bool) -> Result<(), EmptyDomain> { /* ... */ }
  ```

- ```rust
  pub(crate) fn propagate(self: &mut Self, propagator: PropagatorId) -> Result<(), Inconsistency> { /* ... */ }
  ```

- ```rust
  pub(crate) fn propagate_until_fixed_point(self: &mut Self, propagator: PropagatorId) -> Result<(), Inconsistency> { /* ... */ }
  ```

- ```rust
  pub(crate) fn notify_propagator(self: &mut Self, propagator: PropagatorId) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_reason_int(self: &mut Self, predicate: Predicate) -> PropositionalConjunction { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_reason_bool(self: &mut Self, literal: Literal, truth_value: bool) -> PropositionalConjunction { /* ... */ }
  ```

- ```rust
  pub(crate) fn assert_bounds(self: &Self, var: DomainId, lb: i32, ub: i32) { /* ... */ }
  ```

###### Trait Implementations

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Sync**
- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **Freeze**
- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

## Module `trailed`

```rust
pub(in ::engine::cp) mod trailed { /* ... */ }
```

### Modules

## Module `trailed_assignments`

```rust
pub(in ::engine::cp::trailed) mod trailed_assignments { /* ... */ }
```

### Types

#### Struct `TrailedInt`

```rust
pub(crate) struct TrailedInt {
    pub(in ::engine::cp::trailed::trailed_assignments) id: u32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `id` | `u32` |  |

##### Implementations

###### Trait Implementations

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> TrailedInt { /* ... */ }
    ```

- **UnwindSafe**
- **StorageKey**
  - ```rust
    fn index(self: &Self) -> usize { /* ... */ }
    ```

  - ```rust
    fn create_from_index(index: usize) -> Self { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Send**
- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Copy**
#### Struct `TrailedAssignments`

```rust
pub(crate) struct TrailedAssignments {
    pub(in ::engine::cp::trailed::trailed_assignments) trail: trail::Trail<super::TrailedChange>,
    pub(in ::engine::cp::trailed::trailed_assignments) values: crate::containers::KeyedVec<TrailedInt, i64>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `trail` | `trail::Trail<super::TrailedChange>` |  |
| `values` | `crate::containers::KeyedVec<TrailedInt, i64>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn grow(self: &mut Self, initial_value: i64) -> TrailedInt { /* ... */ }
  ```

- ```rust
  pub(crate) fn increase_decision_level(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn read(self: &Self, stateful_int: TrailedInt) -> i64 { /* ... */ }
  ```

- ```rust
  pub(crate) fn synchronise(self: &mut Self, new_decision_level: usize) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::cp::trailed::trailed_assignments) fn write(self: &mut Self, stateful_int: TrailedInt, value: i64) { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_assign(self: &mut Self, stateful_int: TrailedInt, addition: i64) { /* ... */ }
  ```

- ```rust
  pub(crate) fn assign(self: &mut Self, stateful_int: TrailedInt, value: i64) { /* ... */ }
  ```

- ```rust
  pub(crate) fn debug_create_empty_clone(self: &Self) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> TrailedAssignments { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> TrailedAssignments { /* ... */ }
    ```

## Module `trailed_change`

```rust
pub(in ::engine::cp::trailed) mod trailed_change { /* ... */ }
```

### Types

#### Struct `TrailedChange`

```rust
pub(crate) struct TrailedChange {
    pub(crate) old_value: i64,
    pub(crate) reference: super::TrailedInt,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `old_value` | `i64` |  |
| `reference` | `super::TrailedInt` |  |

##### Implementations

###### Trait Implementations

- **Sync**
- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> TrailedChange { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `watch_list_cp`

```rust
pub(in ::engine::cp) mod watch_list_cp { /* ... */ }
```

### Types

#### Struct `WatchListCP`

```rust
pub(crate) struct WatchListCP {
    pub(in ::engine::cp::watch_list_cp) watchers: crate::containers::KeyedVec<crate::engine::variables::DomainId, WatcherCP>,
    pub(in ::engine::cp::watch_list_cp) is_watching_anything: bool,
    pub(in ::engine::cp::watch_list_cp) is_watching_any_backtrack_events: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `watchers` | `crate::containers::KeyedVec<crate::engine::variables::DomainId, WatcherCP>` |  |
| `is_watching_anything` | `bool` |  |
| `is_watching_any_backtrack_events` | `bool` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn grow(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_watching_any_backtrack_events(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_affected_propagators(self: &Self, event: IntDomainEvent, domain: DomainId) -> &[PropagatorVarId] { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_backtrack_affected_propagators(self: &Self, event: IntDomainEvent, domain: DomainId) -> &[PropagatorVarId] { /* ... */ }
  ```

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Default**
  - ```rust
    fn default() -> WatchListCP { /* ... */ }
    ```

- **Unpin**
- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Send**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Freeze**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

#### Struct `Watchers`

Used to register a propagator for notifications about events to a particular variable

```rust
pub struct Watchers<''a> {
    pub(in ::engine::cp::watch_list_cp) propagator_var: propagator_var_id::PropagatorVarId,
    pub(in ::engine::cp::watch_list_cp) watch_list: &''a mut WatchListCP,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `propagator_var` | `propagator_var_id::PropagatorVarId` |  |
| `watch_list` | `&''a mut WatchListCP` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(propagator_var: PropagatorVarId, watch_list: &''a mut WatchListCP) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn watch_all(self: &mut Self, domain: DomainId, events: EnumSet<IntDomainEvent>) { /* ... */ }
  ```

- ```rust
  pub(crate) fn watch_all_backtrack(self: &mut Self, domain: DomainId, events: EnumSet<IntDomainEvent>) { /* ... */ }
  ```

###### Trait Implementations

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
#### Enum `IntDomainEvent`

A description of the kinds of events that can happen on a domain variable.

```rust
pub enum IntDomainEvent {
    Assign,
    LowerBound,
    UpperBound,
    // Some variants omitted
}
```

##### Variants

###### `Assign`

Event where an (integer) variable domain collapses to a single value.

###### `LowerBound`

Event where an (integer) variable domain tightens the lower bound.

###### `UpperBound`

Event where an (integer) variable domain tightens the upper bound.

*Note: Some variants have been omitted because they are private or hidden.*

##### Implementations

###### Trait Implementations

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Self { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BitXor**
  - ```rust
    fn bitxor(self: Self, other: O) -> <Self as >::Output { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **Unpin**
- **BitAnd**
  - ```rust
    fn bitand(self: Self, other: O) -> <Self as >::Output { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **Copy**
- **Send**
- **IntoEither**
- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Sync**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(event: IntDomainEvent) -> Self { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn eq(self: &Self, other: &::enumset::EnumSet<IntDomainEvent>) -> bool { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Not**
  - ```rust
    fn not(self: Self) -> <Self as >::Output { /* ... */ }
    ```

- **Eq**
- **Sub**
  - ```rust
    fn sub(self: Self, other: O) -> <Self as >::Output { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **UnwindSafe**
- **BitOr**
  - ```rust
    fn bitor(self: Self, other: O) -> <Self as >::Output { /* ... */ }
    ```

- **EnumSetTypePrivate**
  - ```rust
    fn enum_into_u32(self: Self) -> u32 { /* ... */ }
    ```

  - ```rust
    unsafe fn enum_from_u32(val: u32) -> Self { /* ... */ }
    ```

- **EnumSetType**
#### Struct `WatcherCP`

```rust
pub(in ::engine::cp::watch_list_cp) struct WatcherCP {
    pub(in ::engine::cp::watch_list_cp) forward_watcher: Watcher,
    pub(in ::engine::cp::watch_list_cp) backtrack_watcher: Watcher,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `forward_watcher` | `Watcher` |  |
| `backtrack_watcher` | `Watcher` |  |

##### Implementations

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> WatcherCP { /* ... */ }
    ```

#### Struct `Watcher`

```rust
pub(in ::engine::cp::watch_list_cp) struct Watcher {
    pub(in ::engine::cp::watch_list_cp) lower_bound_watchers: Vec<propagator_var_id::PropagatorVarId>,
    pub(in ::engine::cp::watch_list_cp) upper_bound_watchers: Vec<propagator_var_id::PropagatorVarId>,
    pub(in ::engine::cp::watch_list_cp) assign_watchers: Vec<propagator_var_id::PropagatorVarId>,
    pub(in ::engine::cp::watch_list_cp) removal_watchers: Vec<propagator_var_id::PropagatorVarId>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `lower_bound_watchers` | `Vec<propagator_var_id::PropagatorVarId>` |  |
| `upper_bound_watchers` | `Vec<propagator_var_id::PropagatorVarId>` |  |
| `assign_watchers` | `Vec<propagator_var_id::PropagatorVarId>` |  |
| `removal_watchers` | `Vec<propagator_var_id::PropagatorVarId>` |  |

##### Implementations

###### Trait Implementations

- **Sync**
- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Watcher { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **RefUnwindSafe**
- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

## Module `debug_helper`

```rust
pub(in ::engine) mod debug_helper { /* ... */ }
```

### Types

#### Struct `DebugDyn`

```rust
pub(crate) struct DebugDyn<''a> {
    pub(in ::engine::debug_helper) trait_name: &''a str,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `trait_name` | `&''a str` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn from(trait_name: &''a str) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Copy**
- **Unpin**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> DebugDyn<''a> { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

#### Struct `DebugHelper`

```rust
pub(crate) struct DebugHelper {
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|

##### Implementations

###### Methods

- ```rust
  pub(crate) fn debug_fixed_point_propagation(stateful_assignments: &TrailedAssignments, assignments: &Assignments, propagators: &PropagatorStore) -> bool { /* ... */ }
  ```
  Method which checks whether the reported fixed point is correct (i.e. whether any

- ```rust
  pub(crate) fn debug_reported_failure(stateful_assignments: &TrailedAssignments, assignments: &Assignments, failure_reason: &PropositionalConjunction, propagator: &dyn Propagator, propagator_id: PropagatorId) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn debug_check_propagations(num_trail_entries_before: usize, propagator_id: PropagatorId, stateful_assignments: &TrailedAssignments, assignments: &Assignments, reason_store: &mut ReasonStore, propagators: &mut PropagatorStore) -> bool { /* ... */ }
  ```
  Checks whether the propagations of the propagator since `num_trail_entries_before` are

- ```rust
  pub(in ::engine::debug_helper) fn debug_propagator_reason(propagated_predicate: Predicate, reason: &[Predicate], stateful_assignments: &TrailedAssignments, assignments: &Assignments, propagator: &dyn Propagator, propagator_id: PropagatorId) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::debug_helper) fn debug_reported_propagations_reproduce_failure(stateful_assignments: &TrailedAssignments, assignments: &Assignments, failure_reason: &PropositionalConjunction, propagator: &dyn Propagator, propagator_id: PropagatorId) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::debug_helper) fn debug_reported_propagations_negate_failure_and_check(stateful_assignments: &TrailedAssignments, assignments: &Assignments, failure_reason: &PropositionalConjunction, propagator: &dyn Propagator, propagator_id: PropagatorId) { /* ... */ }
  ```

- ```rust
  pub(in ::engine::debug_helper) fn debug_add_predicates_to_assignments(assignments: &mut Assignments, predicates: &[Predicate]) -> bool { /* ... */ }
  ```

###### Trait Implementations

- **Copy**
- **Unpin**
- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> DebugHelper { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
## Module `nogoods`

```rust
pub(crate) mod nogoods { /* ... */ }
```

### Modules

## Module `literal_block_distance`

```rust
pub(in ::engine::nogoods) mod literal_block_distance { /* ... */ }
```

### Types

#### Struct `Lbd`

Used to compute the LBD of nogoods. The type carries state that prevents the re-allocation of
helper data structures.

```rust
pub(crate) struct Lbd {
    pub(in ::engine::nogoods::literal_block_distance) lbd_helper: sparse_set::SparseSet<u32>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `lbd_helper` | `sparse_set::SparseSet<u32>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn compute_lbd(self: &mut Self, predicates: &[Predicate], assignments: &Assignments) -> u32 { /* ... */ }
  ```
  Compute the LBD of the given nogood under the given assignment.

###### Trait Implementations

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Lbd { /* ... */ }
    ```

## Module `predicates`

Structures which represent certain [predicates](https://en.wikipedia.org/wiki/Predicate_(mathematical_logic)).

The solver only utilizes the following types of predicates:
- **Predicates over integers** - These [`IntegerPredicate`]s specify atomic constraints of the
  form `[x >= v]`, `[x <= v]`, `[x == v]`, and `[x != v]`.
- **Predicates over literals** - These [`Predicate::Literal`]s specify [`Literal`]s which are
  linked to the aforementioned [`IntegerPredicate`]s through the [`VariableLiteralMappings`].
- **Always True/False** - The [`Predicate::True`]/[`Predicate::False`] specify logical
  predicates which are always true/false.

In general, these [`Predicate`]s are used to represent propagations, explanations or decisions.

```rust
pub(crate) mod predicates { /* ... */ }
```

### Modules

## Module `predicate`

```rust
pub(crate) mod predicate { /* ... */ }
```

### Types

#### Enum `Predicate`

Representation of a domain operation.

It can either be in the form of atomic constraints over
[`DomainId`]s (in the form of [`Predicate::LowerBound`],
[`Predicate::UpperBound`], [`Predicate::NotEqual`] or [`Predicate::Equal`])

```rust
pub enum Predicate {
    LowerBound {
        domain_id: crate::engine::variables::DomainId,
        lower_bound: i32,
    },
    UpperBound {
        domain_id: crate::engine::variables::DomainId,
        upper_bound: i32,
    },
    NotEqual {
        domain_id: crate::engine::variables::DomainId,
        not_equal_constant: i32,
    },
    Equal {
        domain_id: crate::engine::variables::DomainId,
        equality_constant: i32,
    },
}
```

##### Variants

###### `LowerBound`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `domain_id` | `crate::engine::variables::DomainId` |  |
| `lower_bound` | `i32` |  |

###### `UpperBound`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `domain_id` | `crate::engine::variables::DomainId` |  |
| `upper_bound` | `i32` |  |

###### `NotEqual`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `domain_id` | `crate::engine::variables::DomainId` |  |
| `not_equal_constant` | `i32` |  |

###### `Equal`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `domain_id` | `crate::engine::variables::DomainId` |  |
| `equality_constant` | `i32` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn is_mutually_exclusive_with(self: Self, other: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_equality_predicate(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_lower_bound_predicate(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_upper_bound_predicate(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn is_not_equal_predicate(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn get_domain(self: &Self) -> DomainId { /* ... */ }
  ```
  Returns the [`DomainId`] of the [`Predicate`]

- ```rust
  pub fn get_right_hand_side(self: &Self) -> i32 { /* ... */ }
  ```

- ```rust
  pub fn trivially_true() -> Predicate { /* ... */ }
  ```

- ```rust
  pub fn trivially_false() -> Predicate { /* ... */ }
  ```

###### Trait Implementations

- **UnwindSafe**
- **Eq**
- **Not**
  - ```rust
    fn not(self: Self) -> <Self as >::Output { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Extend**
  - ```rust
    fn extend<T: IntoIterator<Item = Predicate>>(self: &mut Self, iter: T) { /* ... */ }
    ```

- **Sync**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> Predicate { /* ... */ }
    ```

- **Unpin**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **StructuralPartialEq**
- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(predicate: Predicate) -> Self { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Copy**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **FromIterator**
  - ```rust
    fn from_iter<T: IntoIterator<Item = Predicate>>(iter: T) -> Self { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Predicate) -> bool { /* ... */ }
    ```

- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

## Module `predicate_constructor`

```rust
pub(crate) mod predicate_constructor { /* ... */ }
```

### Traits

#### Trait `PredicateConstructor`

A trait which defines methods for creating a [`Predicate`].

```rust
pub trait PredicateConstructor {
    /* Associated items */
}
```

##### Required Items

###### Associated Types

- `Value`: The value used to represent a bound.

###### Required Methods

- `lower_bound_predicate`: Creates a lower-bound predicate (e.g. `[x >= v]`).
- `upper_bound_predicate`: Creates an upper-bound predicate (e.g. `[x <= v]`).
- `equality_predicate`: Creates an equality predicate (e.g. `[x == v]`).
- `disequality_predicate`: Creates a disequality predicate (e.g. `[x != v]`).

##### Implementations

This trait is implemented for the following types:

- `crate::engine::variables::DomainId`
- `AffineView<Var>` with <Var: PredicateConstructor<Value = i32>>
- `Literal`

## Module `restart_strategy`

```rust
pub(in ::engine) mod restart_strategy { /* ... */ }
```

### Types

#### Struct `RestartOptions`

The options which are used by the solver to determine when a restart should occur.

An implementation of a restart strategy based on the specfication of [Section 4 of \[1\]](https://fmv.jku.at/papers/BiereFroehlich-POS15.pdf)
(for more information about the Glucose restart strategies see [\[2\]](https://www.cril.univ-artois.fr/articles/xxmain.pdf) and
[\[3\]](http://www.pragmaticsofsat.org/2012/slides-glucose.pdf)). The idea is to restart when the
the quality of the learned clauses (indicated by the LBD [\[4\]](https://www.ijcai.org/Proceedings/09/Papers/074.pdf)
which is the number of different decision levels present in a learned clause, lower is generally
better) is poor. It takes this into account by keeping track of the overall average LBD and the
short-term average LBD and comparing these with one another.

The strategy also takes into account that if a solver is "close" to finding a solution that it
would be better to not restart at that moment and it can then decide to skip a restart.

It generalises the aforementioned Glucose restart strategy by using adjustable
[`RestartOptions`] which allows the user to also specify Luby restarts
(see [\[5\]](https://www.sciencedirect.com/science/article/pii/0020019093900299)) and
constant restarts (see [Section 3 of \[1\]](https://fmv.jku.at/papers/BiereFroehlich-POS15.pdf)).

# Bibliography
\[1\] A. Biere and A. Fröhlich, ‘Evaluating CDCL restart schemes’, Proceedings of Pragmatics of
SAT, pp. 1–17, 2015.

\[2\] G. Audemard and L. Simon, ‘Refining restarts strategies for SAT and UNSAT’, in Principles
and Practice of Constraint Programming: 18th International Conference, CP 2012, Québec City, QC,
Canada, October 8-12, 2012. Proceedings, 2012, pp. 118–126.

\[3\] G. Audemard and L. Simon, ‘Glucose 2.1: Aggressive, but reactive, clause database
management, dynamic restarts (system description)’, in Pragmatics of SAT 2012 (POS’12), 2012.

\[4\] G. Audemard and L. Simon, ‘Predicting learnt clauses quality in modern SAT solvers’, in
Twenty-first international joint conference on artificial intelligence, 2009.

\[5\] M. Luby, A. Sinclair, and D. Zuckerman, ‘Optimal speedup of Las Vegas algorithms’,
Information Processing Letters, vol. 47, no. 4, pp. 173–180, 1993.

```rust
pub struct RestartOptions {
    pub sequence_generator_type: crate::basic_types::sequence_generators::SequenceGeneratorType,
    pub base_interval: u64,
    pub min_num_conflicts_before_first_restart: u64,
    pub lbd_coef: f64,
    pub num_assigned_coef: f64,
    pub num_assigned_window: u64,
    pub geometric_coef: Option<f64>,
    pub no_restarts: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `sequence_generator_type` | `crate::basic_types::sequence_generators::SequenceGeneratorType` | Decides the sequence based on which the restarts are performed.<br>To be used in combination with [`RestartOptions::base_interval`] |
| `base_interval` | `u64` | The base interval length is used as a multiplier to the restart sequence.<br>For example, constant restarts with base interval 100 means a retart is triggered every 100<br>conflicts. |
| `min_num_conflicts_before_first_restart` | `u64` | The minimum number of conflicts to be reached before the first restart is considered |
| `lbd_coef` | `f64` | Used to determine if a restart should be forced.<br>The state is "bad" if the current LBD value is much greater than the global LBD average A<br>greater/lower value for lbd-coef means a less/more frequent restart policy |
| `num_assigned_coef` | `f64` | Used to determine if a restart should be blocked.<br>To be used in combination with<br>[`RestartOptions::num_assigned_window`].<br>A restart is blocked if the number of assigned propositional variables is must greater than<br>the average number of assigned variables in the recent past A greater/lower value for<br>[`RestartOptions::num_assigned_coef`] means fewer/more blocked restarts |
| `num_assigned_window` | `u64` | Used to determine the length of the recent past that should be considered when deciding on<br>blocking restarts. The solver considers the last<br>[`RestartOptions::num_assigned_window`] conflicts as the reference point for the<br>number of assigned variables |
| `geometric_coef` | `Option<f64>` | The coefficient in the geometric sequence `x_i = x_{i-1} * geometric-coef` where `x_1 =<br>`[`RestartOptions::base_interval`]. Used only if<br>[`RestartOptions::sequence_generator_type`] is assigned to<br>[`SequenceGeneratorType::Geometric`]. |
| `no_restarts` | `bool` | Determines whether restarts should be able to occur |

##### Implementations

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Send**
- **Sync**
- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> RestartOptions { /* ... */ }
    ```

- **Copy**
- **IntoEither**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

#### Struct `RestartStrategy`

```rust
pub(crate) struct RestartStrategy {
    pub(in ::engine::restart_strategy) sequence_generator: Box<dyn SequenceGenerator>,
    pub(in ::engine::restart_strategy) number_of_conflicts_encountered_since_restart: u64,
    pub(in ::engine::restart_strategy) number_of_conflicts_until_restart: u64,
    pub(in ::engine::restart_strategy) minimum_number_of_conflicts_before_first_restart: u64,
    pub(in ::engine::restart_strategy) lbd_short_term_moving_average: Box<dyn MovingAverage<u64>>,
    pub(in ::engine::restart_strategy) lbd_coefficient: f64,
    pub(in ::engine::restart_strategy) lbd_long_term_moving_average: Box<dyn MovingAverage<u64>>,
    pub(in ::engine::restart_strategy) number_of_variables_coefficient: f64,
    pub(in ::engine::restart_strategy) number_of_assigned_variables_moving_average: Box<dyn MovingAverage<u64>>,
    pub(in ::engine::restart_strategy) number_of_restarts: u64,
    pub(in ::engine::restart_strategy) number_of_blocked_restarts: u64,
    pub(in ::engine::restart_strategy) no_restarts: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `sequence_generator` | `Box<dyn SequenceGenerator>` | A generator for determining how many conflicts should be found before the next restart is<br>able to take place (one example of such a generator is [`LubySequence`]). |
| `number_of_conflicts_encountered_since_restart` | `u64` | The number of conflicts encountered since the last restart took place |
| `number_of_conflicts_until_restart` | `u64` | The minimum number of conflicts until the next restart is able to take place (note that if<br>[`RestartStrategy::number_of_conflicts_encountered_since_restart`] ><br>[`RestartStrategy::number_of_conflicts_until_restart`] it does not necessarily mean<br>that a restart is guaranteed to take place in the next call to<br>[`RestartStrategy::should_restart`]). |
| `minimum_number_of_conflicts_before_first_restart` | `u64` | The minimum number of conflicts until the first restart is able to take place |
| `lbd_short_term_moving_average` | `Box<dyn MovingAverage<u64>>` | The recent average of LBD values, used in [`RestartStrategy::should_restart`]. |
| `lbd_coefficient` | `f64` | A coefficient which influences the decision whether a restart should take place in<br>[`RestartStrategy::should_restart`], the higher this value, the fewer restarts are<br>performed. |
| `lbd_long_term_moving_average` | `Box<dyn MovingAverage<u64>>` | The long-term average of LBD values, used in [`RestartStrategy::should_restart`]. |
| `number_of_variables_coefficient` | `f64` | A coefficient influencing whether a restart will be blocked in<br>[`RestartStrategy::notify_conflict`], the higher the value, the fewer restarts are<br>performed. |
| `number_of_assigned_variables_moving_average` | `Box<dyn MovingAverage<u64>>` | The average number of variables which are assigned, used in<br>[`RestartStrategy::notify_conflict`]. |
| `number_of_restarts` | `u64` | The number of restarts which have been performed. |
| `number_of_blocked_restarts` | `u64` | The number of restarts which have been blocked. |
| `no_restarts` | `bool` | Determines whether restarts should be able to occur |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(options: RestartOptions) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn should_restart(self: &Self) -> bool { /* ... */ }
  ```
  Determines whether the restart strategy indicates that a restart should take place; the

- ```rust
  pub(in ::engine::restart_strategy) fn should_restart_first_time(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn notify_conflict(self: &mut Self, lbd: u32, number_of_pruned_values: u64) { /* ... */ }
  ```
  Notifies the restart strategy that a conflict has taken place so that it can adjust its

- ```rust
  pub(in ::engine::restart_strategy) fn should_block_restart(self: &Self, number_of_pruned_values: u64) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::engine::restart_strategy) fn should_trigger_later_restart(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn notify_restart(self: &mut Self) { /* ... */ }
  ```
  Notifies the restart strategy that a restart has taken place so that it can adjust its

- ```rust
  pub(in ::engine::restart_strategy) fn reset_values(self: &mut Self) { /* ... */ }
  ```
  Resets the values related to determining whether a restart takes place; this method should

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **Send**
## Module `solver_statistics`

```rust
pub(in ::engine) mod solver_statistics { /* ... */ }
```

### Types

#### Struct `SolverStatistics`

Structure responsible for storing several statistics of the solving process of the
[`ConstraintSatisfactionSolver`].

```rust
pub(crate) struct SolverStatistics {
    pub(crate) engine_statistics: EngineStatistics,
    pub(crate) learned_clause_statistics: LearnedClauseStatistics,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `engine_statistics` | `EngineStatistics` | Core statistics of the solver engine (e.g. the number of decisions) |
| `learned_clause_statistics` | `LearnedClauseStatistics` | The statistics related to clause learning |

##### Implementations

###### Trait Implementations

- **IntoEither**
- **Send**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Copy**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **UnwindSafe**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Freeze**
- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> SolverStatistics { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> SolverStatistics { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: $crate::statistics::StatisticLogger) { /* ... */ }
    ```

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

#### Struct `EngineStatistics`

Core statistics of the solver engine (e.g. the number of decisions)

```rust
pub(crate) struct EngineStatistics {
    pub(crate) num_decisions: u64,
    pub(crate) num_conflicts: u64,
    pub(crate) num_restarts: u64,
    pub(crate) num_propagations: u64,
    pub(crate) time_spent_in_solver: u64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `num_decisions` | `u64` | The number of decisions taken by the solver |
| `num_conflicts` | `u64` | The number of conflicts encountered by the solver |
| `num_restarts` | `u64` | The number of times the solver has restarted |
| `num_propagations` | `u64` | The average number of (integer) propagations made by the solver |
| `time_spent_in_solver` | `u64` | The amount of time which is spent in the solver |

##### Implementations

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> EngineStatistics { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: $crate::statistics::StatisticLogger) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> EngineStatistics { /* ... */ }
    ```

- **Freeze**
- **RefUnwindSafe**
- **IntoEither**
- **Copy**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
#### Struct `LearnedClauseStatistics`

The statistics related to clause learning

```rust
pub(crate) struct LearnedClauseStatistics {
    pub(crate) average_conflict_size: cumulative_moving_average::CumulativeMovingAverage<u64>,
    pub(crate) average_number_of_removed_literals_recursive: cumulative_moving_average::CumulativeMovingAverage<u64>,
    pub(crate) average_number_of_removed_literals_semantic: cumulative_moving_average::CumulativeMovingAverage<u64>,
    pub(crate) num_unit_clauses_learned: u64,
    pub(crate) average_learned_clause_length: cumulative_moving_average::CumulativeMovingAverage<u64>,
    pub(crate) average_backtrack_amount: cumulative_moving_average::CumulativeMovingAverage<u64>,
    pub(crate) average_lbd: cumulative_moving_average::CumulativeMovingAverage<u64>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `average_conflict_size` | `cumulative_moving_average::CumulativeMovingAverage<u64>` | The average number of elements in the conflict explanation |
| `average_number_of_removed_literals_recursive` | `cumulative_moving_average::CumulativeMovingAverage<u64>` | The average number of literals removed by recursive minimisation during conflict analysis |
| `average_number_of_removed_literals_semantic` | `cumulative_moving_average::CumulativeMovingAverage<u64>` | The average number of literals removed by semantic minimisation during conflict analysis |
| `num_unit_clauses_learned` | `u64` | The number of learned clauses which have a size of 1 |
| `average_learned_clause_length` | `cumulative_moving_average::CumulativeMovingAverage<u64>` | The average length of the learned clauses |
| `average_backtrack_amount` | `cumulative_moving_average::CumulativeMovingAverage<u64>` | The average number of levels which have been backtracked by the solver (e.g. when a learned clause is created) |
| `average_lbd` | `cumulative_moving_average::CumulativeMovingAverage<u64>` | The average literal-block distance (LBD) metric for newly added learned nogoods |

##### Implementations

###### Trait Implementations

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: $crate::statistics::StatisticLogger) { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **Unpin**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Copy**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> LearnedClauseStatistics { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LearnedClauseStatistics { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Send**
## Module `termination`

A [`TerminationCondition`] is a condition which is polled by the solver during the search
process. It indicates when the solver should stop, even if no definitive conclusions have been
made. The most common example would be [`time_budget::TimeBudget`], which gives the solver a
certain time budget to complete its search.

```rust
pub(crate) mod termination { /* ... */ }
```

### Modules

## Module `combinator`

```rust
pub(crate) mod combinator { /* ... */ }
```

### Types

#### Struct `Combinator`

A [`TerminationCondition`] which triggers when one of two given [`TerminationCondition`]s
triggers.

```rust
pub struct Combinator<T1, T2> {
    pub(in ::engine::termination::combinator) t1: T1,
    pub(in ::engine::termination::combinator) t2: T2,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `t1` | `T1` |  |
| `t2` | `T2` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(t1: T1, t2: T2) -> Self { /* ... */ }
  ```
  Combine two [`TerminationCondition`]s into one.

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Combinator<T1, T2> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Copy**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TerminationCondition**
  - ```rust
    fn should_stop(self: &mut Self) -> bool { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **Freeze**
## Module `indefinite`

```rust
pub(crate) mod indefinite { /* ... */ }
```

### Types

#### Struct `Indefinite`

A [`TerminationCondition`] which never triggers. The solver can search forever.

```rust
pub struct Indefinite;
```

##### Implementations

###### Trait Implementations

- **Send**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Copy**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Indefinite { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TerminationCondition**
  - ```rust
    fn should_stop(self: &mut Self) -> bool { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Freeze**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Unpin**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **Sync**
## Module `os_signal`

```rust
pub(crate) mod os_signal { /* ... */ }
```

### Types

#### Struct `OsSignal`

A [`TerminationCondition`] which triggers due to a SIGINT signal.

```rust
pub struct OsSignal {
    pub(in ::engine::termination::os_signal) signal_received: std::sync::Arc<std::sync::atomic::AtomicBool>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `signal_received` | `std::sync::Arc<std::sync::atomic::AtomicBool>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn install() -> OsSignal { /* ... */ }
  ```
  Create a termination and install the event listeners.

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OsSignal { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Send**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **Freeze**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TerminationCondition**
  - ```rust
    fn should_stop(self: &mut Self) -> bool { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `time_budget`

```rust
pub(crate) mod time_budget { /* ... */ }
```

### Types

#### Struct `TimeBudget`

A [`TerminationCondition`] which triggers when the specified time budget has been exceeded.

```rust
pub struct TimeBudget {
    pub(in ::engine::termination::time_budget) started_at: std::time::Instant,
    pub(in ::engine::termination::time_budget) budget: std::time::Duration,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `started_at` | `std::time::Instant` | The point in time from which to measure the budget. |
| `budget` | `std::time::Duration` | The amount of time before [`TimeBudget::should_stop()`] becomes true. |

##### Implementations

###### Methods

- ```rust
  pub fn starting_now(budget: Duration) -> TimeBudget { /* ... */ }
  ```
  Give the solver a time budget, starting now.

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TerminationCondition**
  - ```rust
    fn should_stop(self: &mut Self) -> bool { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> TimeBudget { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

### Traits

#### Trait `TerminationCondition`

The central trait that defines a termination condition. A termination condition determines when
the solver should give up searching for solutions.

```rust
pub trait TerminationCondition {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `should_stop`: Returns `true` when the solver should stop, `false` otherwise.

##### Implementations

This trait is implemented for the following types:

- `Combinator<T1, T2>` with <T1: TerminationCondition, T2: TerminationCondition>
- `Indefinite`
- `OsSignal`
- `TimeBudget`
- `Option<T>` with <T: TerminationCondition>

## Module `variables`

A variable, in the context of the solver, is a view onto a domain. It may forward domain
information unaltered, or apply transformations which can be performed without the need of
constraints.

```rust
pub(crate) mod variables { /* ... */ }
```

### Modules

## Module `affine_view`

```rust
pub(in ::engine::variables) mod affine_view { /* ... */ }
```

### Types

#### Struct `AffineView`

Models the constraint `y = ax + b`, by expressing the domain of `y` as a transformation of the
domain of `x`.

```rust
pub struct AffineView<Inner> {
    pub(in ::engine::variables::affine_view) inner: Inner,
    pub(in ::engine::variables::affine_view) scale: i32,
    pub(in ::engine::variables::affine_view) offset: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `inner` | `Inner` |  |
| `scale` | `i32` |  |
| `offset` | `i32` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(inner: Inner, scale: i32, offset: i32) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::engine::variables::affine_view) fn invert(self: &Self, value: i32, rounding: Rounding) -> i32 { /* ... */ }
  ```
  Apply the inverse transformation of this view on a value, to go from the value in the domain

- ```rust
  pub(in ::engine::variables::affine_view) fn map(self: &Self, value: i32) -> i32 { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TransformableVariable**
  - ```rust
    fn scaled(self: &Self, scale: i32) -> AffineView<View> { /* ... */ }
    ```

  - ```rust
    fn offset(self: &Self, offset: i32) -> AffineView<View> { /* ... */ }
    ```

  - ```rust
    fn scaled(self: &Self, scale: i32) -> AffineView<DomainId> { /* ... */ }
    ```

  - ```rust
    fn offset(self: &Self, offset: i32) -> AffineView<DomainId> { /* ... */ }
    ```

  - ```rust
    fn scaled(self: &Self, scale: i32) -> AffineView<Literal> { /* ... */ }
    ```

  - ```rust
    fn offset(self: &Self, offset: i32) -> AffineView<Literal> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> AffineView<Inner> { /* ... */ }
    ```

- **Unpin**
- **IntegerVariable**
  - ```rust
    fn lower_bound(self: &Self, assignment: &Assignments) -> i32 { /* ... */ }
    ```

  - ```rust
    fn lower_bound_at_trail_position(self: &Self, assignment: &Assignments, trail_position: usize) -> i32 { /* ... */ }
    ```

  - ```rust
    fn upper_bound(self: &Self, assignment: &Assignments) -> i32 { /* ... */ }
    ```

  - ```rust
    fn upper_bound_at_trail_position(self: &Self, assignment: &Assignments, trail_position: usize) -> i32 { /* ... */ }
    ```

  - ```rust
    fn contains(self: &Self, assignment: &Assignments, value: i32) -> bool { /* ... */ }
    ```

  - ```rust
    fn contains_at_trail_position(self: &Self, assignment: &Assignments, value: i32, trail_position: usize) -> bool { /* ... */ }
    ```

  - ```rust
    fn iterate_domain(self: &Self, assignment: &Assignments) -> impl Iterator<Item = i32> { /* ... */ }
    ```

  - ```rust
    fn remove(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn set_lower_bound(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn set_upper_bound(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn watch_all(self: &Self, watchers: &mut Watchers<''_>, events: EnumSet<IntDomainEvent>) { /* ... */ }
    ```

  - ```rust
    fn watch_all_backtrack(self: &Self, watchers: &mut Watchers<''_>, events: EnumSet<IntDomainEvent>) { /* ... */ }
    ```

  - ```rust
    fn unpack_event(self: &Self, event: OpaqueDomainEvent) -> IntDomainEvent { /* ... */ }
    ```

- **Freeze**
- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: DomainId) -> Self { /* ... */ }
    ```

- **Eq**
- **StructuralPartialEq**
- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &AffineView<Inner>) -> bool { /* ... */ }
    ```

- **Copy**
- **PredicateConstructor**
  - ```rust
    fn lower_bound_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn upper_bound_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn equality_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn disequality_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

#### Enum `Rounding`

```rust
pub(in ::engine::variables::affine_view) enum Rounding {
    Up,
    Down,
}
```

##### Variants

###### `Up`

###### `Down`

##### Implementations

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **IntoEither**
## Module `domain_generator_iterator`

```rust
pub(in ::engine::variables) mod domain_generator_iterator { /* ... */ }
```

### Types

#### Struct `DomainGeneratorIterator`

```rust
pub struct DomainGeneratorIterator {
    pub(in ::engine::variables::domain_generator_iterator) current_index: u32,
    pub(in ::engine::variables::domain_generator_iterator) end_index: u32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `current_index` | `u32` |  |
| `end_index` | `u32` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(start_index: u32, end_index: u32) -> DomainGeneratorIterator { /* ... */ }
  ```

###### Trait Implementations

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **StructuralPartialEq**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Itertools**
- **IteratorRandom**
- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Copy**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Iterator**
  - ```rust
    fn next(self: &mut Self) -> Option<<Self as >::Item> { /* ... */ }
    ```

- **IntoIterator**
  - ```rust
    fn into_iter(self: Self) -> I { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &DomainGeneratorIterator) -> bool { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **Eq**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> DomainGeneratorIterator { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
## Module `domain_id`

```rust
pub(in ::engine::variables) mod domain_id { /* ... */ }
```

### Types

#### Struct `DomainId`

A structure which represents the most basic [`IntegerVariable`]; it is simply the id which links
to a domain (hence the name).

```rust
pub struct DomainId {
    pub id: u32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `id` | `u32` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(id: u32) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Clone**
  - ```rust
    fn clone(self: &Self) -> DomainId { /* ... */ }
    ```

- **PredicateConstructor**
  - ```rust
    fn lower_bound_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn upper_bound_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn equality_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn disequality_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(value: DomainId) -> Self { /* ... */ }
    ```

- **StructuralPartialEq**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn on_backtrack(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, _value: i32) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &DomainId) -> bool { /* ... */ }
    ```

- **Copy**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **Freeze**
- **StorageKey**
  - ```rust
    fn index(self: &Self) -> usize { /* ... */ }
    ```

  - ```rust
    fn create_from_index(index: usize) -> Self { /* ... */ }
    ```

- **Send**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Eq**
- **IntegerVariable**
  - ```rust
    fn lower_bound(self: &Self, assignment: &Assignments) -> i32 { /* ... */ }
    ```

  - ```rust
    fn lower_bound_at_trail_position(self: &Self, assignment: &Assignments, trail_position: usize) -> i32 { /* ... */ }
    ```

  - ```rust
    fn upper_bound(self: &Self, assignment: &Assignments) -> i32 { /* ... */ }
    ```

  - ```rust
    fn upper_bound_at_trail_position(self: &Self, assignment: &Assignments, trail_position: usize) -> i32 { /* ... */ }
    ```

  - ```rust
    fn contains(self: &Self, assignment: &Assignments, value: i32) -> bool { /* ... */ }
    ```

  - ```rust
    fn contains_at_trail_position(self: &Self, assignment: &Assignments, value: i32, trail_position: usize) -> bool { /* ... */ }
    ```

  - ```rust
    fn iterate_domain(self: &Self, assignment: &Assignments) -> impl Iterator<Item = i32> { /* ... */ }
    ```

  - ```rust
    fn remove(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn set_lower_bound(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn set_upper_bound(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn watch_all(self: &Self, watchers: &mut Watchers<''_>, events: EnumSet<IntDomainEvent>) { /* ... */ }
    ```

  - ```rust
    fn watch_all_backtrack(self: &Self, watchers: &mut Watchers<''_>, events: EnumSet<IntDomainEvent>) { /* ... */ }
    ```

  - ```rust
    fn unpack_event(self: &Self, event: OpaqueDomainEvent) -> IntDomainEvent { /* ... */ }
    ```

- **TransformableVariable**
  - ```rust
    fn scaled(self: &Self, scale: i32) -> AffineView<DomainId> { /* ... */ }
    ```

  - ```rust
    fn offset(self: &Self, offset: i32) -> AffineView<DomainId> { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
## Module `integer_variable`

```rust
pub(in ::engine::variables) mod integer_variable { /* ... */ }
```

### Traits

#### Trait `IntegerVariable`

A trait specifying the required behaviour of an integer variable such as retrieving a
lower-bound ([`IntegerVariable::lower_bound`]) or adjusting the bounds
([`IntegerVariable::set_lower_bound`]).

```rust
pub trait IntegerVariable: Clone + PredicateConstructor<Value = i32> + TransformableVariable<<Self as >::AffineView> {
    /* Associated items */
}
```

> This trait is not object-safe and cannot be used in dynamic trait objects.

##### Required Items

###### Associated Types

- `AffineView`

###### Required Methods

- `lower_bound`: Get the lower bound of the variable.
- `lower_bound_at_trail_position`: Get the lower bound of the variable at the given trail position.
- `upper_bound`: Get the upper bound of the variable.
- `upper_bound_at_trail_position`: Get the upper bound of the variable at the given trail position.
- `contains`: Determine whether the value is in the domain of this variable.
- `contains_at_trail_position`: Determine whether the value is in the domain of this variable at the given trail position.
- `iterate_domain`: Iterate over the values of the domain.
- `remove`: Remove a value from the domain of this variable.
- `set_lower_bound`: Tighten the lower bound of the domain of this variable.
- `set_upper_bound`: Tighten the upper bound of the domain of this variable.
- `watch_all`: Register a watch for this variable on the given domain events.
- `watch_all_backtrack`
- `unpack_event`: Decode a domain event for this variable.

##### Implementations

This trait is implemented for the following types:

- `AffineView<View>` with <View>
- `DomainId`
- `Literal`

## Module `literal`

```rust
pub(in ::engine::variables) mod literal { /* ... */ }
```

### Types

#### Struct `Literal`

```rust
pub struct Literal {
    pub(in ::engine::variables::literal) integer_variable: crate::engine::variables::AffineView<super::DomainId>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `integer_variable` | `crate::engine::variables::AffineView<super::DomainId>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(domain_id: DomainId) -> Literal { /* ... */ }
  ```

- ```rust
  pub fn get_integer_variable(self: &Self) -> AffineView<DomainId> { /* ... */ }
  ```

- ```rust
  pub fn get_true_predicate(self: &Self) -> Predicate { /* ... */ }
  ```

- ```rust
  pub fn get_false_predicate(self: &Self) -> Predicate { /* ... */ }
  ```

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Not**
  - ```rust
    fn not(self: Self) -> <Self as >::Output { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **Send**
- **Copy**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> Literal { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Literal) -> bool { /* ... */ }
    ```

- **PredicateConstructor**
  - ```rust
    fn lower_bound_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn upper_bound_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn equality_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn disequality_predicate(self: &Self, bound: <Self as >::Value) -> Predicate { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Literal) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TransformableVariable**
  - ```rust
    fn scaled(self: &Self, scale: i32) -> AffineView<Literal> { /* ... */ }
    ```

  - ```rust
    fn offset(self: &Self, offset: i32) -> AffineView<Literal> { /* ... */ }
    ```

- **IntegerVariable**
  - ```rust
    fn lower_bound(self: &Self, assignment: &Assignments) -> i32 { /* ... */ }
    ```
    Returns the lower bound represented as a 0-1 value.

  - ```rust
    fn lower_bound_at_trail_position(self: &Self, assignment: &Assignments, trail_position: usize) -> i32 { /* ... */ }
    ```

  - ```rust
    fn upper_bound(self: &Self, assignment: &Assignments) -> i32 { /* ... */ }
    ```
    Returns the upper bound represented as a 0-1 value.

  - ```rust
    fn upper_bound_at_trail_position(self: &Self, assignment: &Assignments, trail_position: usize) -> i32 { /* ... */ }
    ```

  - ```rust
    fn contains(self: &Self, assignment: &Assignments, value: i32) -> bool { /* ... */ }
    ```
    Returns whether the input value, when interpreted as a bool,

  - ```rust
    fn contains_at_trail_position(self: &Self, assignment: &Assignments, value: i32, trail_position: usize) -> bool { /* ... */ }
    ```

  - ```rust
    fn iterate_domain(self: &Self, assignment: &Assignments) -> impl Iterator<Item = i32> { /* ... */ }
    ```

  - ```rust
    fn remove(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn set_lower_bound(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn set_upper_bound(self: &Self, assignment: &mut Assignments, value: i32, reason: Option<ReasonRef>) -> Result<(), EmptyDomain> { /* ... */ }
    ```

  - ```rust
    fn watch_all(self: &Self, watchers: &mut Watchers<''_>, events: EnumSet<IntDomainEvent>) { /* ... */ }
    ```

  - ```rust
    fn unpack_event(self: &Self, event: OpaqueDomainEvent) -> IntDomainEvent { /* ... */ }
    ```

  - ```rust
    fn watch_all_backtrack(self: &Self, watchers: &mut Watchers<''_>, events: EnumSet<IntDomainEvent>) { /* ... */ }
    ```

- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Literal> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **UnwindSafe**
- **IntoEither**
- **Eq**
- **Freeze**
- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **Unpin**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **StructuralPartialEq**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `transformable_variable`

```rust
pub(in ::engine::variables) mod transformable_variable { /* ... */ }
```

### Traits

#### Trait `TransformableVariable`

Trait for transforming a variable.

At the moment this allows creating a scaled version of a
variable using [`TransformableVariable::scaled`] or creating a variable with a constant offset
based on the original variable using [`TransformableVariable::offset`].

```rust
pub trait TransformableVariable<View> {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `scaled`: Get a variable which domain is scaled compared to the domain of self.
- `offset`: Get a variable which domain has a constant offset to the domain of self.

##### Implementations

This trait is implemented for the following types:

- `AffineView<View>` with <View>
- `DomainId`
- `Literal`

### Re-exports

#### Re-export `AffineView`

```rust
pub use affine_view::AffineView;
```

#### Re-export `DomainId`

```rust
pub use domain_id::DomainId;
```

#### Re-export `IntegerVariable`

```rust
pub use integer_variable::IntegerVariable;
```

#### Re-export `Literal`

```rust
pub use literal::Literal;
```

#### Re-export `TransformableVariable`

```rust
pub use transformable_variable::TransformableVariable;
```

### Re-exports

#### Re-export `ConflictResolver`

```rust
pub use constraint_satisfaction_solver::ConflictResolver;
```

#### Re-export `SatisfactionSolverOptions`

```rust
pub use constraint_satisfaction_solver::SatisfactionSolverOptions;
```

#### Re-export `RestartOptions`

```rust
pub use restart_strategy::RestartOptions;
```

## Module `math`

```rust
pub(crate) mod math { /* ... */ }
```

### Modules

## Module `num_ext`

Extensions for numbers that are not present in the stable standard library.

```rust
pub(crate) mod num_ext { /* ... */ }
```

### Traits

#### Trait `NumExt`

```rust
pub(crate) trait NumExt {
    /* Associated items */
}
```

> This trait is not object-safe and cannot be used in dynamic trait objects.

##### Required Items

###### Required Methods

- `div_ceil`: Division with rounding up.
- `div_floor`: Division with rounding down.

##### Implementations

This trait is implemented for the following types:

- `i32`

## Module `propagators`

Contains propagator implementations that are used in Pumpkin.

See the [`crate::engine::cp::propagation`] for info on propagators.

```rust
pub(crate) mod propagators { /* ... */ }
```

### Modules

## Module `arithmetic`

```rust
pub(crate) mod arithmetic { /* ... */ }
```

### Modules

## Module `absolute_value`

```rust
pub(crate) mod absolute_value { /* ... */ }
```

### Types

#### Struct `AbsoluteValuePropagator`

Propagator for `absolute = |signed|`, where `absolute` and `signed` are integer variables.

The propagator is bounds consistent wrt signed. That means that if `signed \in {-2, -1, 1, 2}`,
the propagator will not propagate `[absolute >= 1]`.

```rust
pub(crate) struct AbsoluteValuePropagator<VA, VB> {
    pub(in ::propagators::arithmetic::absolute_value) signed: VA,
    pub(in ::propagators::arithmetic::absolute_value) absolute: VB,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `signed` | `VA` |  |
| `absolute` | `VB` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(signed: VA, absolute: VB) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), crate::predicates::PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **IntoEither**
- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **RefUnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> AbsoluteValuePropagator<VA, VB> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `division`

```rust
pub(crate) mod division { /* ... */ }
```

### Types

#### Struct `DivisionPropagator`

A propagator for maintaining the constraint `numerator / denominator = rhs`; note that this
propagator performs truncating division (i.e. rounding towards 0).

The propagator assumes that the `denominator` is a (non-zero) number.

The implementation is ported from [OR-tools](https://github.com/google/or-tools/blob/870edf6f7bff6b8ff0d267d936be7e331c5b8c2d/ortools/sat/integer_expr.cc#L1209C1-L1209C19).

```rust
pub(crate) struct DivisionPropagator<VA, VB, VC> {
    pub(in ::propagators::arithmetic::division) numerator: VA,
    pub(in ::propagators::arithmetic::division) denominator: VB,
    pub(in ::propagators::arithmetic::division) rhs: VC,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `numerator` | `VA` |  |
| `denominator` | `VB` |  |
| `rhs` | `VC` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(numerator: VA, denominator: VB, rhs: VC) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **Unpin**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> DivisionPropagator<VA, VB, VC> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Sync**
- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

### Functions

#### Function `perform_propagation`

```rust
pub(in ::propagators::arithmetic::division) fn perform_propagation<VA: IntegerVariable, VB: IntegerVariable, VC: IntegerVariable>(context: contexts::propagation_context::PropagationContextMut<''_>, numerator: &VA, denominator: &VB, rhs: &VC) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `propagate_positive_domains`

Propagates the domains of variables if all the domains are positive (if the variables are
sign-fixed then we simply transform them to positive domains using [`AffineView`]s); it performs
the following propagations:
- The minimum value that division can take on is the smallest value that `numerator /
  denominator` can take on
- The numerator is at least as large as the smallest value that `denominator * rhs` can take on
- The value of the denominator is smaller than the largest value that `numerator / rhs` can take
  on
- The denominator is at least as large as the ratio between the largest ceiled ratio between
  `numerator + 1` and `rhs + 1`

```rust
pub(in ::propagators::arithmetic::division) fn propagate_positive_domains<VA: IntegerVariable, VB: IntegerVariable, VC: IntegerVariable>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, numerator: &VA, denominator: &VB, rhs: &VC) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `propagate_upper_bounds`

Propagates the upper-bounds of the right-hand side and the numerator, it performs the following
propagations
- The maximum value of the right-hand side can only be as large as the largest value that
  `numerator / denominator` can take on
- The maximum value of the numerator is smaller than `(ub(rhs) + 1) * denominator - 1`, note
  that this might not be the most constrictive bound

```rust
pub(in ::propagators::arithmetic::division) fn propagate_upper_bounds<VA: IntegerVariable, VB: IntegerVariable, VC: IntegerVariable>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, numerator: &VA, denominator: &VB, rhs: &VC) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `propagate_signs`

Propagates the signs of the variables, more specifically, it performs the following propagations
(assuming that the denominator is always > 0):
- If the numerator is non-negative then the right-hand side must be non-negative as well
- If the right-hand side is positive then the numerator must be positive as well
- If the numerator is non-positive then the right-hand side must be non-positive as well
- If the right-hand is negative then the numerator must be negative as well

```rust
pub(in ::propagators::arithmetic::division) fn propagate_signs<VA: IntegerVariable, VB: IntegerVariable, VC: IntegerVariable>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, numerator: &VA, denominator: &VB, rhs: &VC) -> Result<(), Inconsistency> { /* ... */ }
```

### Constants and Statics

#### Constant `ID_NUMERATOR`

```rust
pub(in ::propagators::arithmetic::division) const ID_NUMERATOR: local_id::LocalId = _;
```

#### Constant `ID_DENOMINATOR`

```rust
pub(in ::propagators::arithmetic::division) const ID_DENOMINATOR: local_id::LocalId = _;
```

#### Constant `ID_RHS`

```rust
pub(in ::propagators::arithmetic::division) const ID_RHS: local_id::LocalId = _;
```

## Module `integer_multiplication`

```rust
pub(crate) mod integer_multiplication { /* ... */ }
```

### Types

#### Struct `IntegerMultiplicationPropagator`

A propagator for maintaining the constraint `a * b = c`. The propagator
(currently) only propagates the signs of the variables, the case where a, b, c >= 0, and detects
a conflict if the variables are fixed.

```rust
pub(crate) struct IntegerMultiplicationPropagator<VA, VB, VC> {
    pub(in ::propagators::arithmetic::integer_multiplication) a: VA,
    pub(in ::propagators::arithmetic::integer_multiplication) b: VB,
    pub(in ::propagators::arithmetic::integer_multiplication) c: VC,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `a` | `VA` |  |
| `b` | `VB` |  |
| `c` | `VC` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(a: VA, b: VB, c: VC) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> IntegerMultiplicationPropagator<VA, VB, VC> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Freeze**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **Propagator**
  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), crate::predicates::PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

### Functions

#### Function `perform_propagation`

```rust
pub(in ::propagators::arithmetic::integer_multiplication) fn perform_propagation<VA: IntegerVariable, VB: IntegerVariable, VC: IntegerVariable>(context: contexts::propagation_context::PropagationContextMut<''_>, a: &VA, b: &VB, c: &VC) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `propagate_signs`

Propagates the signs of the variables, it performs the following propagations:
- Propagating based on positive bounds
    - If a is positive and b is positive then c is positive
    - If a is positive and c is positive then b is positive
    - If b is positive and c is positive then a is positive
- Propagating based on negative bounds
    - If a is negative and b is negative then c is positive
    - If a is negative and c is negative then b is positive
    - If b is negative and c is negative then b is positive
- Propagating based on mixed bounds
    - Propagating c based on a and b
        - If a is negative and b is positive then c is negative
        - If a is positive and b is negative then c is negative
    - Propagating b based on a and c
        - If a is negative and c is positive then b is negative
        - If a is positive and c is negative then b is negative
    - Propagating a based on b and c
        - If b is negative and c is positive then a is negative
        - If b is positive and c is negative then a is negative

Note that this method does not propagate a value if 0 is in the domain as, for example, 0 * -3 =
0 and 0 * 3 = 0 are both equally valid.

```rust
pub(in ::propagators::arithmetic::integer_multiplication) fn propagate_signs<VA: IntegerVariable, VB: IntegerVariable, VC: IntegerVariable>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, a: &VA, b: &VB, c: &VC) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `div_ceil_pos`

**Attributes:**

- `#[inline]`

Compute `ceil(numerator / denominator)`.

Assumes `numerator, denominator > 0`.

```rust
pub(in ::propagators::arithmetic::integer_multiplication) fn div_ceil_pos(numerator: i32, denominator: i32) -> i32 { /* ... */ }
```

### Constants and Statics

#### Constant `ID_A`

```rust
pub(in ::propagators::arithmetic::integer_multiplication) const ID_A: local_id::LocalId = _;
```

#### Constant `ID_B`

```rust
pub(in ::propagators::arithmetic::integer_multiplication) const ID_B: local_id::LocalId = _;
```

#### Constant `ID_C`

```rust
pub(in ::propagators::arithmetic::integer_multiplication) const ID_C: local_id::LocalId = _;
```

## Module `linear_less_or_equal`

```rust
pub(crate) mod linear_less_or_equal { /* ... */ }
```

### Types

#### Struct `LinearLessOrEqualPropagator`

Propagator for the constraint `\sum x_i <= c`.

```rust
pub(crate) struct LinearLessOrEqualPropagator<Var> {
    pub(in ::propagators::arithmetic::linear_less_or_equal) x: Box<[Var]>,
    pub(in ::propagators::arithmetic::linear_less_or_equal) c: i32,
    pub(in ::propagators::arithmetic::linear_less_or_equal) lower_bound_left_hand_side: crate::engine::TrailedInt,
    pub(in ::propagators::arithmetic::linear_less_or_equal) current_bounds: Box<[crate::engine::TrailedInt]>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `x` | `Box<[Var]>` |  |
| `c` | `i32` |  |
| `lower_bound_left_hand_side` | `crate::engine::TrailedInt` | The lower bound of the sum of the left-hand side. This is incremental state. |
| `current_bounds` | `Box<[crate::engine::TrailedInt]>` | The value at index `i` is the bound for `x[i]`. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(x: Box<[Var]>, c: i32) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::arithmetic::linear_less_or_equal) fn create_conflict_reason(self: &Self, context: PropagationContext<''_>) -> PropositionalConjunction { /* ... */ }
  ```

###### Trait Implementations

- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Sync**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn detect_inconsistency(self: &Self, context: StatefulPropagationContext<''_>) -> Option<PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, _event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LinearLessOrEqualPropagator<Var> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `linear_not_equal`

```rust
pub(crate) mod linear_not_equal { /* ... */ }
```

### Types

#### Struct `LinearNotEqualPropagator`

Propagator for the constraint `\sum x_i != rhs`, where `x_i` are
integer variables and `rhs` is an integer constant.

```rust
pub(crate) struct LinearNotEqualPropagator<Var> {
    pub(in ::propagators::arithmetic::linear_not_equal) terms: std::rc::Rc<[Var]>,
    pub(in ::propagators::arithmetic::linear_not_equal) rhs: i32,
    pub(in ::propagators::arithmetic::linear_not_equal) number_of_fixed_terms: usize,
    pub(in ::propagators::arithmetic::linear_not_equal) fixed_lhs: i32,
    pub(in ::propagators::arithmetic::linear_not_equal) unfixed_variable_has_been_updated: bool,
    pub(in ::propagators::arithmetic::linear_not_equal) should_recalculate_lhs: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `terms` | `std::rc::Rc<[Var]>` | The terms of the sum |
| `rhs` | `i32` | The right-hand side of the sum |
| `number_of_fixed_terms` | `usize` | The number of fixed terms; note that this constraint can only propagate when there is a<br>single unfixed variable and can only detect conflicts if all variables are assigned |
| `fixed_lhs` | `i32` | The sum of the values of the fixed terms |
| `unfixed_variable_has_been_updated` | `bool` | Indicates whether the single unfixed variable has been updated; if this is the case then<br>the propagator is not scheduled again |
| `should_recalculate_lhs` | `bool` | Indicates whether the value of [`LinearNotEqualPropagator::fixed_lhs`] is invalid and<br>should be recalculated |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(terms: Box<[Var]>, rhs: i32) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::arithmetic::linear_not_equal) fn recalculate_fixed_variables(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
  ```
  This method is used to calculate the fixed left-hand side of the equation and keep track of

- ```rust
  pub(in ::propagators::arithmetic::linear_not_equal) fn check_for_conflict(self: &Self, context: PropagationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
  ```
  Determines whether a conflict has occurred and calculate the reason for the conflict

- ```rust
  pub(in ::propagators::arithmetic::linear_not_equal) fn is_propagator_state_consistent(self: &Self, context: PropagationContext<''_>) -> bool { /* ... */ }
  ```
  Checks whether the number of fixed terms is equal to the number of fixed terms in the

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, _event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn notify_backtrack(self: &mut Self, _context: PropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **UnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Send**
- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LinearNotEqualPropagator<Var> { /* ... */ }
    ```

## Module `maximum`

```rust
pub(crate) mod maximum { /* ... */ }
```

### Types

#### Struct `MaximumPropagator`

Bounds-consistent propagator which enforces `max(array) = rhs`. Can be constructed through
[`MaximumConstructor`].

```rust
pub(crate) struct MaximumPropagator<ElementVar, Rhs> {
    pub(in ::propagators::arithmetic::maximum) array: Box<[ElementVar]>,
    pub(in ::propagators::arithmetic::maximum) rhs: Rhs,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `array` | `Box<[ElementVar]>` |  |
| `rhs` | `Rhs` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(array: Box<[ElementVar]>, rhs: Rhs) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Propagator**
  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> MaximumPropagator<ElementVar, Rhs> { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
## Module `cumulative`

Contains the propagators for the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html)
constraint, currently it contains solely time-tabling propagators (see
[`crate::propagators::cumulative::time_table`] for an explanation).

# Theoretical

The cumulative constraint reasons over a set of [`Task`]s over a single resource
with a capacity. Each [`Task`] consists of the following parameters:
- A variable `s_i` representing the start time of the [`Task`]
- The duration of the [`Task`] `p_i` (which is the same for all resources) which cannot be
  interruped
- The constant resource usage `r_i` of the [`Task`] (which can differ for different resources)

Oftentimes the following notation is used to denote certain significant time points:
- `EST_i` - The earliest starting time, equal to `lb(s_i)`
- `ECT_i` - The earliest completion time, equal to `lb(s_i) + p_i`
- `LST_i` - The latest start time, equal to `ub(s_i)`
- `LCT_i` - The latest completion time, equal to `ub(s_i) + p_i`

A [`Task`] is said to execute at time point *t* if it holds that `s_i <= t < s_i + p_i`. The
constraint then ensures that at no time point *t* in the horizon (the latest time at which
any [`Task`] can execute) there is an overflow of the resource capacity by the cumulative
resource usage of the [`Task`]s which are being processed at point *t*.

A common problem which makes use of the Cumulative constraint is the [RCPSP](https://www.projectmanagement.ugent.be/research/project_scheduling/rcpsp)
problem. Which uses a combination of [Precedence](https://sofdem.github.io/gccat/gccat/Cprecedence.html)
and Cumulative constraints.

# Practical

The following example shows how one of the propagators for the Cumulative constraint
([`TimeTablePerPointPropagator`]) can be used:

```rust
// We construct three tasks for a resource with capacity 2:
// - Task 0: Start times: [0, 5], Processing time: 4, Resource usage: 1
// - Task 1: Start times: [0, 5], Processing time: 2, Resource usage: 1
// - Task 2: Start times: [0, 5], Processing time: 4, Resource usage: 2
// We can infer that Task 0 and Task 1 execute at the same time
// while Task 2 will start after them
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::SatisfactionResult;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
# use crate::pumpkin_solver::results::ProblemSolution;
let mut solver = Solver::default();

let start_0 = solver.new_bounded_integer(0, 4);
let start_1 = solver.new_bounded_integer(0, 4);
let start_2 = solver.new_bounded_integer(0, 5);

let start_times = [start_0, start_1, start_2];
let durations = [5, 2, 5];
let resource_requirements = [1, 1, 2];
let resource_capacity = 2;

solver
    .add_constraint(constraints::cumulative(
        start_times.clone(),
        durations.clone(),
        resource_requirements.clone(),
        resource_capacity,
    ))
    .post();

let mut termination = Indefinite;
let mut brancher = solver.default_brancher();

let result = solver.satisfy(&mut brancher, &mut termination);

// We check whether the result was feasible
if let SatisfactionResult::Satisfiable(solution) = result {
    let horizon = durations.iter().sum::<i32>();
    let start_times = [start_0, start_1, start_2];

    // Now we check whether the resource constraint is satisfied at each time-point t
    assert!((0..=horizon).all(|t| {
        // We gather all of the resource usages at the current time t
        let resource_usage_at_t = start_times
            .iter()
            .enumerate()
            .filter_map(|(task_index, start_time)| {
                if solution.get_integer_value(*start_time) <= t
                    && solution.get_integer_value(*start_time) + durations[task_index] > t
                {
                    Some(resource_requirements[task_index])
                } else {
                    None
                }
            })
            .sum::<i32>();
        // Then we check whether the resource usage at the current time point is lower than
        // the resource capacity
        resource_usage_at_t <= resource_capacity
    }));

    // Finally we check whether Task 2 starts after Task 0 and Task 1 and that Task 0 and
    // Task 1 overlap
    assert!(
        solution.get_integer_value(start_2)
            >= solution.get_integer_value(start_0) + durations[0]
            && solution.get_integer_value(start_2)
                >= solution.get_integer_value(start_1) + durations[1]
    );
    assert!(
        solution.get_integer_value(start_0)
            < solution.get_integer_value(start_1) + durations[1]
            && solution.get_integer_value(start_1)
                < solution.get_integer_value(start_0) + durations[0]
    );
}
```

```rust
pub(in ::propagators) mod cumulative { /* ... */ }
```

### Modules

## Module `time_table`

Contains the time-table propagators which use so-called time-table reasoning
for propagating the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) constraint.

# Theoretical

These time-table propagators reason about something called the **mandatory part** of a [`Task`];
informally, the mandatory part of a [`Task`] is the time points in which a [`Task`] *has* to
execute given its current bounds. Mathematically (see [`crate::propagators::cumulative`] for
notation details), the mandatory part of a [`Task`] *i* is the interval `[LST_i, ECT_i)`
(i.e. the time points between the latest start time of a task and its earliest completion time).

The so-called **time-table** is a data-structure which are used to track the cumulative
mandatory parts at different time-points. Our time-tables consist of [`ResourceProfile`]s which
represent the cumulative resource usage ([`height`][ResourceProfile::height]) across an interval
(\[[`start`][ResourceProfile::start], [`end`][ResourceProfile::end]\]) of a set of [`Task`]s
([`profile_tasks`][ResourceProfile::profile_tasks]).

Propagation oftentimes uses these time-tables to either update the bounds of the [`Task`]s or to
remove values from the domain. If a time-table has been built then for any [`Task`] which
overflows the resource capacity if it overlaps with a [`ResourceProfile`] (and is not part of
it) all start times which cause this task to overlap with any part of the [`ResourceProfile`]
can be removed from the domain.

The simplest example of this is if we have a resource with capacity 1 and we have the following
two [`Task`]s:
- Task 1: Start times: [0, 5], Processing time: 4, Resource usage: 1
- Task 2: Start times: [3, 3], Processing time: 2, Resource usage: 1

In this case the time-table would consist of a single [`ResourceProfile`] with
[`start`][ResourceProfile::start] 3 and [`end`][ResourceProfile::end] 4 signifying that Task 2
executes in the interval `[3, 4]` for 2 units of time. It can be seen that if Task 1 is
scheduled at the earliest possible starting time of 0 that there would be an overflow of the
resource, we could thus propagate the lower-bound on the start time of Task 1 to be 5.

There are several algorithms which perform time-table reasoning with varying complexities and
with varying strengths such as [\[2\]](https://pure.tue.nl/ws/portalfiles/portal/2374269/431902.pdf),
[\[3\]](https://www.diva-portal.org/smash/get/diva2:1041645/FULLTEXT01.pdf) and
[\[4\]](https://dial.uclouvain.be/pr/boreal/object/boreal%3A171186/datastream/PDF_01/view).
For more information about explanations for this type of reasoning see
[Sections 4.2.1, 4.5.2 and 4.6.1-4.6.3 of \[1\]](http://cp2013.a4cp.org/sites/default/files/andreas_schutt_-_improving_scheduling_by_learning.pdf)
for more information about time-table reasoning

# Practical

Certain common functions are stored in
[`crate::propagators::cumulative::time_table::time_table_util`] such as
[`should_enqueue`] which determines whether a time-table propagator has seen sufficient changes
to warrant being scheduled once more or [`propagate_based_on_timetable`] which goes over all
profiles and tasks and determines whether a propagation can take place and performs it if this
is the case. It should be noted that these methods assume that the provided [`ResourceProfile`]s
are maximal (i.e. there is no [`ResourceProfile`] adjacent to it with the same
[`ResourceProfile::profile_tasks`]) and that they are sorted in increasing order of start time;
not adhering to these guidelines could result in missed propagations.

# Bibliography

\[1\] A. Schutt, Improving scheduling by learning. University of Melbourne, Department of
Computer Science and Software Engineering, 2011.

\[2\] W. P. M. Nuijten, ‘Time and resource constrained scheduling: a constraint satisfaction
approach’, 1994.

\[3\] N. Beldiceanu and M. Carlsson, ‘A new multi-resource cumulatives constraint with negative
heights’, in International Conference on Principles and Practice of Constraint Programming,
2002, pp. 63–79.

\[4\] S. Gay, R. Hartert, and P. Schaus, ‘Simple and scalable time-table filtering for the
cumulative constraint’, in Principles and Practice of Constraint Programming: 21st International
Conference, CP 2015, Cork, Ireland, August 31--September 4, 2015, Proceedings 21, 2015, pp.
149–157.

```rust
pub(in ::propagators::cumulative) mod time_table { /* ... */ }
```

### Modules

## Module `explanations`

```rust
pub(in ::propagators::cumulative::time_table) mod explanations { /* ... */ }
```

### Modules

## Module `big_step`

```rust
pub(crate) mod big_step { /* ... */ }
```

### Functions

#### Function `create_big_step_propagation_explanation`

Creates the propagation explanation using the big-step approach (see
[`CumulativeExplanationType::BigStep`])

```rust
pub(crate) fn create_big_step_propagation_explanation<Var: IntegerVariable + ''static>(profile: &crate::propagators::ResourceProfile<Var>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

#### Function `create_big_step_conflict_explanation`

Creates the conflict explanation using the big-step approach (see
[`CumulativeExplanationType::BigStep`])

```rust
pub(crate) fn create_big_step_conflict_explanation<Var: IntegerVariable + ''static>(conflict_profile: &crate::propagators::ResourceProfile<Var>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

#### Function `create_big_step_predicate_propagating_task_lower_bound_propagation`

```rust
pub(crate) fn create_big_step_predicate_propagating_task_lower_bound_propagation<Var>(task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>) -> crate::predicates::Predicate
where
    Var: IntegerVariable + ''static { /* ... */ }
```

#### Function `create_big_step_predicate_propagating_task_upper_bound_propagation`

```rust
pub(crate) fn create_big_step_predicate_propagating_task_upper_bound_propagation<Var>(task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, context: contexts::propagation_context::PropagationContext<''_>) -> crate::predicates::Predicate
where
    Var: IntegerVariable + ''static { /* ... */ }
```

## Module `naive`

```rust
pub(crate) mod naive { /* ... */ }
```

### Functions

#### Function `create_naive_propagation_explanation`

Creates the propagation explanation using the naive approach (see
[`CumulativeExplanationType::Naive`])

```rust
pub(crate) fn create_naive_propagation_explanation<Var: IntegerVariable + ''static>(profile: &crate::propagators::ResourceProfile<Var>, context: contexts::propagation_context::PropagationContext<''_>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

#### Function `create_naive_conflict_explanation`

Creates the conflict explanation using the naive approach (see
[`CumulativeExplanationType::Naive`])

```rust
pub(crate) fn create_naive_conflict_explanation<Var, Context: ReadDomains + Copy>(conflict_profile: &crate::propagators::ResourceProfile<Var>, context: Context) -> crate::predicates::PropositionalConjunction
where
    Var: IntegerVariable + ''static { /* ... */ }
```

#### Function `create_naive_predicate_propagating_task_lower_bound_propagation`

```rust
pub(crate) fn create_naive_predicate_propagating_task_lower_bound_propagation<Var>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>) -> crate::predicates::Predicate
where
    Var: IntegerVariable + ''static { /* ... */ }
```

#### Function `create_naive_predicate_propagating_task_upper_bound_propagation`

```rust
pub(crate) fn create_naive_predicate_propagating_task_upper_bound_propagation<Var>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>) -> crate::predicates::Predicate
where
    Var: IntegerVariable + ''static { /* ... */ }
```

## Module `pointwise`

```rust
pub(crate) mod pointwise { /* ... */ }
```

### Functions

#### Function `propagate_lower_bounds_with_pointwise_explanations`

```rust
pub(crate) fn propagate_lower_bounds_with_pointwise_explanations<Var: IntegerVariable + ''static>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, profiles: &[&crate::propagators::ResourceProfile<Var>], propagating_task: &std::rc::Rc<crate::propagators::Task<Var>>) -> Result<(), assignments::EmptyDomain> { /* ... */ }
```

#### Function `propagate_upper_bounds_with_pointwise_explanations`

```rust
pub(crate) fn propagate_upper_bounds_with_pointwise_explanations<Var: IntegerVariable + ''static>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, profiles: &[&crate::propagators::ResourceProfile<Var>], propagating_task: &std::rc::Rc<crate::propagators::Task<Var>>) -> Result<(), assignments::EmptyDomain> { /* ... */ }
```

#### Function `create_pointwise_propagation_explanation`

Creates the propagation explanation using the point-wise approach (see
[`CumulativeExplanationType::PointWise`])

```rust
pub(crate) fn create_pointwise_propagation_explanation<Var: IntegerVariable + ''static>(time_point: i32, profile: &crate::propagators::ResourceProfile<Var>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

#### Function `create_pointwise_conflict_explanation`

Creates the conflict explanation using the point-wise approach (see
[`CumulativeExplanationType::PointWise`])

```rust
pub(crate) fn create_pointwise_conflict_explanation<Var: IntegerVariable + ''static>(conflict_profile: &crate::propagators::ResourceProfile<Var>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

#### Function `create_pointwise_predicate_propagating_task_lower_bound_propagation`

```rust
pub(crate) fn create_pointwise_predicate_propagating_task_lower_bound_propagation<Var>(task: &std::rc::Rc<crate::propagators::Task<Var>>, time_point: Option<i32>) -> crate::predicates::Predicate
where
    Var: IntegerVariable + ''static { /* ... */ }
```

#### Function `create_pointwise_predicate_propagating_task_upper_bound_propagation`

```rust
pub(crate) fn create_pointwise_predicate_propagating_task_upper_bound_propagation<Var>(task: &std::rc::Rc<crate::propagators::Task<Var>>, time_point: Option<i32>) -> crate::predicates::Predicate
where
    Var: IntegerVariable + ''static { /* ... */ }
```

### Types

#### Enum `CumulativeExplanationType`

Determines what type of explanation is used for the cumulative constraint based on the
explanations described in Section 4.5.1 and 4.5.2 of \[1\].

For the explanations of conflicts and conflicts, we different between 3 types of explanations:
- The naive explanation (see [`CumulativeExplanationType::Naive`])
- The bigstep explanation (see [CumulativeExplanationType::BigStep])
- The pointwise explanation (see [CumulativeExplanationType::Pointwise])

# Bibliography
\[1\] A. Schutt, Improving scheduling by learning. University of Melbourne, Department of
Computer Science and Software Engineering, 2011.

```rust
pub enum CumulativeExplanationType {
    Naive,
    BigStep,
    Pointwise,
}
```

##### Variants

###### `Naive`

The naive explanation approach simply uses the current bounds of the profile and the
propagated task in the explanation.

###### `BigStep`

The default; lifts the explanation to create an explanation which uses the bounds which
would cause the tasks in the profile to have mandatory parts in the range of the
propagating profile.

###### `Pointwise`

Creates an explanation over a set of time-points;

## Propagations
Note that we currently do not generate chains of profiles which cause a propagation. This
means that the explanation only concerns a single profile; the selected time-points for
a propagation of task i are constructed as follows in the case of a lower-bound
propagation: `[profile.start, profile.start + i.process_time, profile.start + (2 *
i.processing_time), ..., profile.end]`. Thus, if the profile is shorter than
`i.processing_time`, two explanations are generated for the time-points `profile.start`
and `profile.end`.

## Conflicts
For conflicts we follow the work by Schutt (see the documentation for
[`CumulativeExplanationType`]) and select the middle point in the profile as the point used
for the explanation.

##### Implementations

###### Trait Implementations

- **Sync**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> CumulativeExplanationType { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> CumulativeExplanationType { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **ValueEnum**
  - ```rust
    fn value_variants<''a>() -> &''a [Self] { /* ... */ }
    ```

  - ```rust
    fn to_possible_value<''a>(self: &Self) -> ::std::option::Option<clap::builder::PossibleValue> { /* ... */ }
    ```

- **Send**
### Functions

#### Function `create_predicate_propagating_task_lower_bound_propagation`

Creates the lower-bound [`Predicate`] of the `propagating_task` based on the `explanation_type`.

```rust
pub(crate) fn create_predicate_propagating_task_lower_bound_propagation<Var: IntegerVariable + ''static>(explanation_type: CumulativeExplanationType, context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, time_point: Option<i32>) -> crate::predicates::Predicate { /* ... */ }
```

#### Function `add_propagating_task_predicate_lower_bound`

Adds the lower-bound predicate of the propagating task to the provided `explanation`.

```rust
pub(crate) fn add_propagating_task_predicate_lower_bound<Var: IntegerVariable + ''static>(explanation: crate::predicates::PropositionalConjunction, explanation_type: CumulativeExplanationType, context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, time_point: Option<i32>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

#### Function `create_predicate_propagating_task_upper_bound_propagation`

Creates the upper-bound [`Predicate`] of the `propagating_task` based on the `explanation_type`.

```rust
pub(crate) fn create_predicate_propagating_task_upper_bound_propagation<Var: IntegerVariable + ''static>(explanation_type: CumulativeExplanationType, context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, time_point: Option<i32>) -> crate::predicates::Predicate { /* ... */ }
```

#### Function `add_propagating_task_predicate_upper_bound`

Adds the upper-bound predicate of the propagating task to the provided `explanation`.

```rust
pub(crate) fn add_propagating_task_predicate_upper_bound<Var: IntegerVariable + ''static>(explanation: crate::predicates::PropositionalConjunction, explanation_type: CumulativeExplanationType, context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, time_point: Option<i32>) -> crate::predicates::PropositionalConjunction { /* ... */ }
```

## Module `over_interval_incremental_propagator`

```rust
pub(in ::propagators::cumulative::time_table) mod over_interval_incremental_propagator { /* ... */ }
```

### Modules

## Module `checks`

Contains the checks which are done when a new mandatory part is added in the propagate method to
determine which profiles should be added and how existing profiles should be adjusted.

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator) mod checks { /* ... */ }
```

### Functions

#### Function `new_profile_before_first_profile`

Determines whether the added mandatory part causes a new profile before the first overapping
profile.

```rust
pub(crate) fn new_profile_before_first_profile<Var: IntegerVariable + ''static>(current_index: usize, start_index: usize, update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

#### Function `new_profile_between_profiles`

Determines whether a new profile should be inserted between the current profile (pointed to
by `current_index`) and the previous profile.

```rust
pub(crate) fn new_profile_between_profiles<Var: IntegerVariable + ''static>(time_table: &Vec<crate::propagators::ResourceProfile<Var>>, current_index: usize, start_index: usize, update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

#### Function `split_profile_added_part_starts_after_profile_start`

Determines whether the current profile is split by the added mandatory part due to the start
of the added mandatory part being after the start of the current profile.

Note that this function adds the unchanged part only (i.e. the part of the profile with
which the added mandatory part does **not** overlap), the updated part of this profile
is added in [`overlap_updated_profile`].

```rust
pub(crate) fn split_profile_added_part_starts_after_profile_start<Var: IntegerVariable + ''static>(update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>) { /* ... */ }
```

#### Function `overlap_updated_profile`

Determines whether a new profile which contains the overlap between `profile` and the added
mandatory part should be added.

```rust
pub(crate) fn overlap_updated_profile<Var: IntegerVariable + ''static>(update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, task: &std::rc::Rc<crate::propagators::Task<Var>>, capacity: i32) -> Result<(), crate::propagators::ResourceProfile<Var>> { /* ... */ }
```

#### Function `split_profile_added_part_ends_before_profile_end`

Determines whether the current profile is split by the added mandatory part due to the end
of the added mandatory part being before the end of the profile.

Note that this function adds the unchanged part only (i.e. the part of the profile with
which the added mandatory part does **not** overlap), the updated part of this profile
is added in [`overlap_updated_profile`].

```rust
pub(crate) fn split_profile_added_part_ends_before_profile_end<Var: IntegerVariable + ''static>(update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>) { /* ... */ }
```

#### Function `new_part_after_last_profile`

Determines whether the added mandatory part causes a new profile after the last overapping
profile.

```rust
pub(crate) fn new_part_after_last_profile<Var: IntegerVariable + ''static>(current_index: usize, end_index: usize, update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

## Module `debug`

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator) mod debug { /* ... */ }
```

### Functions

#### Function `time_tables_are_the_same_interval`

Determines whether the provided `time_table` is the same as the one creatd from scratch
using the following checks:
- The time-tables should contain the same number of profiles
- For each profile it should hold that
     - The start times are the same
     - The end times are the same
     - The heights are the same
     - The profile tasks should be the same; note that we do not check whether the order is the
       same!

```rust
pub(crate) fn time_tables_are_the_same_interval<Var: IntegerVariable + ''static, const SYNCHRONISE: bool>(context: contexts::propagation_context::PropagationContext<''_>, time_table: &Vec<crate::propagators::ResourceProfile<Var>>, parameters: &crate::propagators::CumulativeParameters<Var>) -> bool { /* ... */ }
```

#### Function `merge_profiles`

Merge all mergeable profiles (see [`are_mergeable`]) going from `[start_index, end_index]`
in the provided `time_table`.

```rust
pub(crate) fn merge_profiles<Var: IntegerVariable + ''static>(time_table: &mut Vec<crate::propagators::ResourceProfile<Var>>, start_index: usize, end_index: usize) { /* ... */ }
```

#### Function `are_mergeable`

Determines whether 2 profiles are mergeable (i.e. they are next to each other, consist of
the same tasks and have the same height); this method is used in debugging to compare to a
time-table created from scratch.

It is assumed that the profile tasks of both profiles do not contain duplicates

```rust
pub(crate) fn are_mergeable<Var: IntegerVariable + ''static>(first_profile: &crate::propagators::ResourceProfile<Var>, second_profile: &crate::propagators::ResourceProfile<Var>) -> bool { /* ... */ }
```

## Module `insertion`

Contains the functions necessary for inserting the appropriate profiles into the time-table
based on the added mandatory part.

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator) mod insertion { /* ... */ }
```

### Functions

#### Function `insert_profiles_overlapping_with_added_mandatory_part`

The new mandatory part added by `updated_task` (spanning `update_range`) overlaps with the
profiles in `[start_index, end_index]`. This function calculates the added, and updated
profiles and adds them to the `time-table` at the correct position.

```rust
pub(crate) fn insert_profiles_overlapping_with_added_mandatory_part<Var: IntegerVariable + ''static>(time_table: &mut Vec<crate::propagators::ResourceProfile<Var>>, start_index: usize, end_index: usize, update_range: &std::ops::Range<i32>, updated_task: &std::rc::Rc<crate::propagators::Task<Var>>, capacity: i32) -> Result<(), crate::propagators::ResourceProfile<Var>> { /* ... */ }
```

#### Function `insert_profile_new_mandatory_part`

The new mandatory part added by `updated_task` (spanning `update_range`) does not overlap
with any existing profile. This method inserts it at the position of `index_to_insert`
in the `time-table`.

```rust
pub(crate) fn insert_profile_new_mandatory_part<Var: IntegerVariable + ''static>(time_table: &mut Vec<crate::propagators::ResourceProfile<Var>>, index_to_insert: usize, update_range: &std::ops::Range<i32>, updated_task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

## Module `removal`

Contains the functions necessary for removing the appropriate profiles into the time-table
based on the reduced mandatory part.

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator) mod removal { /* ... */ }
```

### Functions

#### Function `reduce_profiles_overlapping_with_added_mandatory_part`

The reduced mandatory part of `updated_task` (spanning `update_range`) overlaps with the
profiles in `[start_index, end_index]`. This function calculates the added, and updated
profiles and adds them to the `time-table` at the correct position.

```rust
pub(crate) fn reduce_profiles_overlapping_with_added_mandatory_part<Var: IntegerVariable + ''static>(time_table: &mut Vec<crate::propagators::ResourceProfile<Var>>, start_index: usize, end_index: usize, update_range: &std::ops::Range<i32>, updated_task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

#### Function `remove_task_from_profile`

Returns the provided `profile` with the provided `updated_task` removed.

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::removal) fn remove_task_from_profile<Var: IntegerVariable + ''static>(updated_task: &std::rc::Rc<crate::propagators::Task<Var>>, start: i32, end: i32, profile: &crate::propagators::ResourceProfile<Var>) -> crate::propagators::ResourceProfile<Var> { /* ... */ }
```

#### Function `split_first_profile`

If there is a partial overlap, this method creates a profile consisting of the original
profile before the overlap.

```rust
pub(crate) fn split_first_profile<Var: IntegerVariable + ''static>(to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, update_range: &std::ops::Range<i32>, first_profile: &crate::propagators::ResourceProfile<Var>) { /* ... */ }
```

#### Function `split_last_profile`

```rust
pub(crate) fn split_last_profile<Var: IntegerVariable + ''static>(to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, update_range: &std::ops::Range<i32>, last_profile: &crate::propagators::ResourceProfile<Var>) { /* ... */ }
```

#### Function `overlap_updated_profile`

This method creates a new profile based on the overlap with the provided `profile`.

```rust
pub(crate) fn overlap_updated_profile<Var: IntegerVariable + ''static>(update_range: &std::ops::Range<i32>, profile: &crate::propagators::ResourceProfile<Var>, to_add: &mut Vec<crate::propagators::ResourceProfile<Var>>, updated_task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

## Module `synchronisation`

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator) mod synchronisation { /* ... */ }
```

### Functions

#### Function `find_synchronised_conflict`

Finds the conflicting profile which would have been found by the
[`TimeTableOverIntervalPropagator`]; this is the first conflicting profile in terms of start
time, however, the returned profile should be merged with adjacent profiles to create the
returned conflict profile.

```rust
pub(crate) fn find_synchronised_conflict<Var: IntegerVariable + ''static>(time_table: &mut Vec<crate::propagators::ResourceProfile<Var>>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Option<crate::propagators::ResourceProfile<Var>> { /* ... */ }
```

#### Function `check_synchronisation_conflict_explanation_over_interval`

Returns whether the synchronised conflict explanation created by
[`TimeTableOverIntervalIncrementalPropgator`] is the same as that created by
[`TimeTableOverIntervalPropagator`].

```rust
pub(crate) fn check_synchronisation_conflict_explanation_over_interval<Var: IntegerVariable + ''static>(synchronised_conflict_explanation: &Result<(), Inconsistency>, context: contexts::propagation_context::PropagationContext<''_>, parameters: &crate::propagators::CumulativeParameters<Var>) -> bool { /* ... */ }
```

#### Function `create_synchronised_conflict_explanation`

Given the `conflicting_profile` (which is the same conflict profile which would have been found
by [`TimeTableOverIntervalPropagator`]), this function calculates the error which would have
been reported by [`TimeTableOverIntervalPropagator`] by finding the tasks which should be
included in the profile and sorting them in the same order.

```rust
pub(crate) fn create_synchronised_conflict_explanation<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, conflicting_profile: &mut crate::propagators::ResourceProfile<Var>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `synchronise_time_table`

Synchronises the time-table; two actions are performed:
1. Adjacent profiles are merged which have been split due to the incremental updates
2. Each profile is sorted such that it corresponds to the order in which
   [`TimeTableOverIntervalPropagator`] would have found them

```rust
pub(crate) fn synchronise_time_table<Var: IntegerVariable + ''static>(time_table: &mut Vec<crate::propagators::ResourceProfile<Var>>, context: contexts::propagation_context::PropagationContext<''_>) { /* ... */ }
```

#### Function `sort_profile_based_on_upper_bound_and_id`

Sorts the provided `profile` on non-decreasing order of upper-bound while tie-breaking in
non-decreasing order of ID

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::synchronisation) fn sort_profile_based_on_upper_bound_and_id<Var: IntegerVariable + ''static>(profile: &mut crate::propagators::ResourceProfile<Var>, context: contexts::propagation_context::PropagationContext<''_>) { /* ... */ }
```

## Module `time_table_over_interval_incremental`

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator) mod time_table_over_interval_incremental { /* ... */ }
```

### Types

#### Struct `TimeTableOverIntervalIncrementalPropagator`

[`Propagator`] responsible for using time-table reasoning to propagate the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) constraint
where a time-table is a structure which stores the mandatory resource usage of the tasks at
different time-points - This method creates a resource profile over an interval rather than
creating one per time-point (hence the name). Furthermore, the
[`TimeTableOverIntervalPropagator`] has a generic argument which represents the type of variable
used for modelling the start variables, this will be an implementation of [`IntegerVariable`].

The difference between the [`TimeTableOverIntervalIncrementalPropagator`] and
[`TimeTableOverIntervalPropagator`] is that the [`TimeTableOverIntervalIncrementalPropagator`]
does not recalculate the time-table from scratch whenever the
[`Propagator::propagate`] method is called but it utilises the
[`Propagator::notify`] method to determine when a mandatory part is added
and only updates the structure based on these updated mandatory parts.

See [Sections 4.2.1, 4.5.2 and 4.6.1-4.6.3 of \[1\]](http://cp2013.a4cp.org/sites/default/files/andreas_schutt_-_improving_scheduling_by_learning.pdf)
 for more information about time-table reasoning.

\[1\] A. Schutt, Improving scheduling by learning. University of Melbourne, Department of
Computer Science and Software Engineering, 2011.

```rust
pub(crate) struct TimeTableOverIntervalIncrementalPropagator<Var, const SYNCHRONISE: bool> {
    pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) time_table: Vec<crate::propagators::ResourceProfile<Var>>,
    pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) parameters: crate::propagators::CumulativeParameters<Var>,
    pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) updatable_structures: crate::propagators::UpdatableStructures<Var>,
    pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) found_previous_conflict: bool,
    pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) is_time_table_outdated: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `time_table` | `Vec<crate::propagators::ResourceProfile<Var>>` | The key `t` (representing a time-point) holds the mandatory resource consumption of<br>[`Task`]s at that time (stored in a [`ResourceProfile`]); the [`ResourceProfile`]s are<br>sorted based on start time and they are assumed to be non-overlapping |
| `parameters` | `crate::propagators::CumulativeParameters<Var>` | Stores the input parameters to the cumulative constraint |
| `updatable_structures` | `crate::propagators::UpdatableStructures<Var>` | Stores structures which change during the search; either to store bounds or when applying<br>incrementality |
| `found_previous_conflict` | `bool` | Stores whether the propagator found a conflict in the previous call<br><br>This is stored to deal with the case where the same conflict can be created via two<br>distinct propagation chains; to the propagator it appears that nothing has changed (since<br>the bounds on the variables remain the same) but there is still a conflicting profile in<br>the time-table |
| `is_time_table_outdated` | `bool` | Indicates whether the current time-table is outdated and should be recalculated from<br>scratch or not; note that this variable is only used if<br>[`CumulativePropagatorOptions::incremental_backtracking`] is set to false. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(arg_tasks: &[ArgTask<Var>], capacity: i32, cumulative_options: CumulativePropagatorOptions) -> TimeTableOverIntervalIncrementalPropagator<Var, SYNCHRONISE> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) fn add_to_time_table(self: &mut Self, context: PropagationContext<''_>, mandatory_part_adjustments: &MandatoryPartAdjustments, task: &Rc<Task<Var>>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Adds the added parts in the provided [`MandatoryPartAdjustments`] to the time-table; note

- ```rust
  pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) fn remove_from_time_table(self: &mut Self, mandatory_part_adjustments: &MandatoryPartAdjustments, task: &Rc<Task<Var>>) { /* ... */ }
  ```
  Removes the removed parts in the provided [`MandatoryPartAdjustments`] from the time-table

- ```rust
  pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) fn update_time_table(self: &mut Self, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Updates the stored time-table based on the updates stored in

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **Unpin**
- **RefUnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn notify_backtrack(self: &mut Self, context: PropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **Sync**
- **Send**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> TimeTableOverIntervalIncrementalPropagator<Var, SYNCHRONISE> { /* ... */ }
    ```

### Functions

#### Function `determine_profiles_to_update`

Determines which profiles are required to be updated given a range of times which now
include a mandatory part (i.e. determine the profiles which overlap with the update_range).
It returns two indices into
[time_table][TimeTableOverIntervalIncrementalPropagator::time_table] representing the
index of the first profile which overlaps with the update_range (inclusive)
and the index of the last profile which overlaps with the update_range (inclusive) or [None]
if there are no overlapping profiles

Note that the lower-bound of the range is inclusive and the upper-bound is exclusive

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) fn determine_profiles_to_update<Var: IntegerVariable + ''static>(time_table: &Vec<crate::propagators::ResourceProfile<Var>>, update_range: &std::ops::Range<i32>) -> Result<(usize, usize), usize> { /* ... */ }
```

#### Function `find_overlapping_profile`

Performs a binary search on the
[time-table][TimeTableOverIntervalIncrementalPropagator::time_table] to find *an* element
which overlaps with the `update_range`. If such an element can be found then it returns
[Ok] containing the index of the overlapping profile. If no such element could be found,
it returns [Err] containing the index at which the element should be inserted to
preserve the ordering

```rust
pub(in ::propagators::cumulative::time_table::over_interval_incremental_propagator::time_table_over_interval_incremental) fn find_overlapping_profile<Var: IntegerVariable + ''static>(time_table: &Vec<crate::propagators::ResourceProfile<Var>>, update_range: &std::ops::Range<i32>) -> Result<usize, usize> { /* ... */ }
```

## Module `per_point_incremental_propagator`

```rust
pub(in ::propagators::cumulative::time_table) mod per_point_incremental_propagator { /* ... */ }
```

### Modules

## Module `synchronisation`

```rust
pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator) mod synchronisation { /* ... */ }
```

### Functions

#### Function `check_synchronisation_conflict_explanation_per_point`

Returns whether the synchronised conflict explanation created by
[`TimeTablePerPointIncrementalPropgator`] is the same as that created by
[`TimeTablePerPointPropagator`].

```rust
pub(crate) fn check_synchronisation_conflict_explanation_per_point<Var: IntegerVariable + ''static>(synchronised_conflict_explanation: &Result<(), Inconsistency>, context: contexts::propagation_context::PropagationContext<''_>, parameters: &crate::propagators::CumulativeParameters<Var>) -> bool { /* ... */ }
```

#### Function `find_synchronised_conflict`

Finds the conflicting profile which would have been found by the
[`TimeTablePerPointPropagator`]; this is the conflicting profile which has the minimum maximum
ID in set of the first `n` profile tasks (when sorted on ID) which overflow the capacity

```rust
pub(crate) fn find_synchronised_conflict<Var: IntegerVariable + ''static>(time_table: &mut std::collections::BTreeMap<u32, crate::propagators::ResourceProfile<Var>>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Option<u32> { /* ... */ }
```

#### Function `get_minimum_set_of_tasks_which_overflow_capacity`

Sorts the profile based on ID and then finds the minimum set of consecutive tasks starting from
the first profile which would have overflown the resource capacity.

The sum of the heights of the tasks is stored in the provided `output_height`; note that this
means that the iterator should be consumed before reading the `output_height`

```rust
pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::synchronisation) fn get_minimum_set_of_tasks_which_overflow_capacity<''a, Var: IntegerVariable + ''static>(profile: &''a mut crate::propagators::ResourceProfile<Var>, parameters: &''a crate::propagators::CumulativeParameters<Var>, output_height: &''a mut i32) -> impl Iterator<Item = std::rc::Rc<crate::propagators::Task<Var>>> + ''a { /* ... */ }
```

#### Function `create_synchronised_conflict_explanation`

Given the `conflicting_profile` (which is the same conflict profile which would have been found
by [`TimeTablePerPointPropagator`]), this function calculates the error which would have been
reported by [`TimeTablePerPointPropagator`] by finding the tasks which should be included in the
profile and sorting them in the same order.

```rust
pub(crate) fn create_synchronised_conflict_explanation<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, conflicting_profile: &mut crate::propagators::ResourceProfile<Var>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `synchronise_time_table`

Synchronises the time-table; one action is performed:
1. Each profile is sorted such that it corresponds to the order in which
   [`TimeTableOverIntervalPropagator`] would have found them

```rust
pub(crate) fn synchronise_time_table<''a, Var: IntegerVariable + ''static, /* synthetic */ impl Iterator<Item = &'a mut ResourceProfile<Var>>: Iterator<Item = &''a mut crate::propagators::ResourceProfile<Var>>>(time_table: impl Iterator<Item = &''a mut crate::propagators::ResourceProfile<Var>>) { /* ... */ }
```

#### Function `sort_profile_based_on_id`

Sorts the provided `profile` on non-decreasing order of ID

```rust
pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::synchronisation) fn sort_profile_based_on_id<Var: IntegerVariable + ''static>(profile: &mut crate::propagators::ResourceProfile<Var>) { /* ... */ }
```

## Module `time_table_per_point_incremental`

```rust
pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator) mod time_table_per_point_incremental { /* ... */ }
```

### Modules

## Module `debug`

Contains functions related to debugging

```rust
pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) mod debug { /* ... */ }
```

### Functions

#### Function `time_tables_are_the_same_point`

Determines whether the provided `time_table` is the same as the one creatd from scratch
using the following checks:
- The time-tables should contain the same number of profiles
- For each profile it should hold that
     - The start times are the same
     - The end times are the same
     - The heights are the same
     - The profile tasks should be the same; note that we do not check whether the order is
       the same!

```rust
pub(crate) fn time_tables_are_the_same_point<Var: IntegerVariable + ''static, const SYNCHRONISE: bool>(context: contexts::propagation_context::PropagationContext<''_>, time_table: &std::collections::BTreeMap<u32, crate::propagators::ResourceProfile<Var>>, parameters: &crate::propagators::CumulativeParameters<Var>) -> bool { /* ... */ }
```

### Types

#### Struct `TimeTablePerPointIncrementalPropagator`

[`Propagator`] responsible for using time-table reasoning to propagate the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) constraint
where a time-table is a structure which stores the mandatory resource usage of the tasks at
different time-points - This method creates a resource profile per time point rather than
creating one over an interval (hence the name). Furthermore, the [`TimeTablePerPointPropagator`]
has a generic argument which represents the type of variable used for modelling the start
variables, this will be an implementation of [`IntegerVariable`].

The difference between the [`TimeTablePerPointIncrementalPropagator`] and
[`TimeTablePerPointPropagator`] is that the [`TimeTablePerPointIncrementalPropagator`] does not
recalculate the time-table from scratch whenever the
[`Propagator::propagate`] method is called but it utilises the
[`Propagator::notify`] method to determine when a mandatory part is added
and only updates the structure based on these updated mandatory parts.

See [Sections 4.2.1, 4.5.2 and 4.6.1-4.6.3 of \[1\]](http://cp2013.a4cp.org/sites/default/files/andreas_schutt_-_improving_scheduling_by_learning.pdf)
 for more information about time-table reasoning.

\[1\] A. Schutt, Improving scheduling by learning. University of Melbourne, Department of
Computer Science and Software Engineering, 2011.

```rust
pub(crate) struct TimeTablePerPointIncrementalPropagator<Var, const SYNCHRONISE: bool> {
    pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) time_table: std::collections::BTreeMap<u32, crate::propagators::ResourceProfile<Var>>,
    pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) parameters: crate::propagators::CumulativeParameters<Var>,
    pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) updatable_structures: crate::propagators::UpdatableStructures<Var>,
    pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) found_previous_conflict: bool,
    pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) is_time_table_outdated: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `time_table` | `std::collections::BTreeMap<u32, crate::propagators::ResourceProfile<Var>>` | The key `t` (representing a time-point) holds the mandatory resource consumption of<br>[`Task`]s at that time (stored in a [`ResourceProfile`]); the [`ResourceProfile`]s are<br>sorted based on start time and they are assumed to be non-overlapping |
| `parameters` | `crate::propagators::CumulativeParameters<Var>` | Stores the input parameters to the cumulative constraint |
| `updatable_structures` | `crate::propagators::UpdatableStructures<Var>` | Stores structures which change during the search; either to store bounds or when applying<br>incrementality |
| `found_previous_conflict` | `bool` | Stores whether the propagator found a conflict in the previous call<br><br>This is stored to deal with the case where the same conflict can be created via two<br>distinct propagation chains; to the propagator it appears that nothing has changed (since<br>the bounds on the variables remain the same) but there is still a conflicting profile in<br>the time-table |
| `is_time_table_outdated` | `bool` | Indicates whether the current time-table is outdated and should be recalculated from<br>scratch or not; note that this variable is only used if<br>[`CumulativePropagatorOptions::incremental_backtracking`] is set to false. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(arg_tasks: &[ArgTask<Var>], capacity: i32, cumulative_options: CumulativePropagatorOptions) -> TimeTablePerPointIncrementalPropagator<Var, SYNCHRONISE> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) fn add_to_time_table(self: &mut Self, context: PropagationContext<''_>, mandatory_part_adjustments: &MandatoryPartAdjustments, task: &Rc<Task<Var>>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Adds the added parts in the provided [`MandatoryPartAdjustments`] to the time-table; note

- ```rust
  pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) fn remove_from_time_table(self: &mut Self, mandatory_part_adjustments: &MandatoryPartAdjustments, task: &Rc<Task<Var>>) { /* ... */ }
  ```
  Removes the removed parts in the provided [`MandatoryPartAdjustments`] from the time-table

- ```rust
  pub(in ::propagators::cumulative::time_table::per_point_incremental_propagator::time_table_per_point_incremental) fn update_time_table(self: &mut Self, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Updates the stored time-table based on the updates stored in

###### Trait Implementations

- **Freeze**
- **Send**
- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn notify_backtrack(self: &mut Self, context: PropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **UnwindSafe**
## Module `propagation_handler`

```rust
pub(in ::propagators::cumulative::time_table) mod propagation_handler { /* ... */ }
```

### Types

#### Struct `CumulativePropagationHandler`

Structure for handling the creation of propagations and their explanations.

```rust
pub(crate) struct CumulativePropagationHandler {
    pub(in ::propagators::cumulative::time_table::propagation_handler) explanation_type: super::CumulativeExplanationType,
    pub(in ::propagators::cumulative::time_table::propagation_handler) stored_profile_explanation: std::cell::OnceCell<std::rc::Rc<crate::predicates::PropositionalConjunction>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `explanation_type` | `super::CumulativeExplanationType` | The type of explanation which is used |
| `stored_profile_explanation` | `std::cell::OnceCell<std::rc::Rc<crate::predicates::PropositionalConjunction>>` | If the same profile propagates multiple tasks then it is beneficial to cache that<br>explanation and re-use it. Note that this will only be used for<br>[`CumulativeExplanationType::Naive`] and [`CumulativeExplanationType::BigStep`]. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(explanation_type: CumulativeExplanationType) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn propagate_chain_of_lower_bounds_with_explanations<Var>(self: &mut Self, context: &mut PropagationContextMut<''_>, profiles: &[&ResourceProfile<Var>], propagating_task: &Rc<Task<Var>>) -> Result<(), EmptyDomain>
where
    Var: IntegerVariable + ''static { /* ... */ }
  ```
  Propagates the lower-bound of the `propagating_task` to not conflict with all of the

- ```rust
  pub(crate) fn propagate_chain_of_upper_bounds_with_explanations<Var>(self: &mut Self, context: &mut PropagationContextMut<''_>, profiles: &[&ResourceProfile<Var>], propagating_task: &Rc<Task<Var>>) -> Result<(), EmptyDomain>
where
    Var: IntegerVariable + ''static { /* ... */ }
  ```
  Propagates the upper-bound of the `propagating_task` to not conflict with all of the

- ```rust
  pub(crate) fn propagate_lower_bound_with_explanations<Var>(self: &mut Self, context: &mut PropagationContextMut<''_>, profile: &ResourceProfile<Var>, propagating_task: &Rc<Task<Var>>) -> Result<(), EmptyDomain>
where
    Var: IntegerVariable + ''static { /* ... */ }
  ```
  Propagates the lower-bound of the `propagating_task` to not conflict with `profile` anymore.

- ```rust
  pub(crate) fn propagate_upper_bound_with_explanations<Var>(self: &mut Self, context: &mut PropagationContextMut<''_>, profile: &ResourceProfile<Var>, propagating_task: &Rc<Task<Var>>) -> Result<(), EmptyDomain>
where
    Var: IntegerVariable + ''static { /* ... */ }
  ```
  Propagates the upper-bound of the `propagating_task` to not conflict with `profile` anymore.

- ```rust
  pub(crate) fn propagate_holes_in_domain<Var>(self: &mut Self, context: &mut PropagationContextMut<''_>, profile: &ResourceProfile<Var>, propagating_task: &Rc<Task<Var>>) -> Result<(), EmptyDomain>
where
    Var: IntegerVariable + ''static { /* ... */ }
  ```
  Propagates a hole in the domain; note that this explanation does not contain any of the

- ```rust
  pub(crate) fn next_profile(self: &mut Self) { /* ... */ }
  ```
  Signifies that we are moving to another profile and we cannot re-use the cached explanation

- ```rust
  pub(in ::propagators::cumulative::time_table::propagation_handler) fn get_stored_profile_explanation_or_init<Var>(self: &mut Self, context: &mut PropagationContextMut<''_>, profile: &ResourceProfile<Var>) -> Rc<PropositionalConjunction>
where
    Var: IntegerVariable + ''static { /* ... */ }
  ```
  Either we get the stored stored profile explanation or we initialize it.

###### Trait Implementations

- **UnwindSafe**
- **Unpin**
- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

### Functions

#### Function `check_explanation`

```rust
pub(in ::propagators::cumulative::time_table::propagation_handler) fn check_explanation(explanation: &crate::predicates::PropositionalConjunction, context: contexts::propagation_context::PropagationContext<''_>) -> bool { /* ... */ }
```

#### Function `create_conflict_explanation`

Creates an explanation of the conflict caused by `conflict_profile` based on the provided
`explanation_type`.

```rust
pub(crate) fn create_conflict_explanation<Var, Context: ReadDomains + Copy>(context: Context, conflict_profile: &crate::propagators::ResourceProfile<Var>, explanation_type: super::CumulativeExplanationType) -> crate::predicates::PropositionalConjunction
where
    Var: IntegerVariable + ''static { /* ... */ }
```

## Module `time_table_over_interval`

```rust
pub(in ::propagators::cumulative::time_table) mod time_table_over_interval { /* ... */ }
```

### Types

#### Struct `Event`

An event storing the start and end of mandatory parts used for creating the time-table

```rust
pub(crate) struct Event<Var> {
    pub(in ::propagators::cumulative::time_table::time_table_over_interval) time_stamp: i32,
    pub(in ::propagators::cumulative::time_table::time_table_over_interval) change_in_resource_usage: i32,
    pub(in ::propagators::cumulative::time_table::time_table_over_interval) task: std::rc::Rc<crate::propagators::Task<Var>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `time_stamp` | `i32` | The time-point at which the [`Event`] took place |
| `change_in_resource_usage` | `i32` | Change in resource usage at [time_stamp][Event::time_stamp], positive if it is the start of<br>a mandatory part and negative otherwise |
| `task` | `std::rc::Rc<crate::propagators::Task<Var>>` | The [`Task`] which has caused the event to take place |

##### Implementations

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **IntoEither**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
#### Struct `TimeTableOverIntervalPropagator`

[`Propagator`] responsible for using time-table reasoning to propagate the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) constraint
where a time-table is a structure which stores the mandatory resource usage of the tasks at
different time-points - This method creates a resource profile over an interval rather than
creating one per time-point (as is done in [`TimeTablePerPointPropagator`]).

See [Sections 4.2.1, 4.5.2 and 4.6.1-4.6.3 of \[1\]](http://cp2013.a4cp.org/sites/default/files/andreas_schutt_-_improving_scheduling_by_learning.pdf)
 for more information about time-table reasoning.

\[1\] A. Schutt, Improving scheduling by learning. University of Melbourne, Department of
Computer Science and Software Engineering, 2011.

```rust
pub(crate) struct TimeTableOverIntervalPropagator<Var> {
    pub(in ::propagators::cumulative::time_table::time_table_over_interval) is_time_table_empty: bool,
    pub(in ::propagators::cumulative::time_table::time_table_over_interval) parameters: crate::propagators::CumulativeParameters<Var>,
    pub(in ::propagators::cumulative::time_table::time_table_over_interval) updatable_structures: crate::propagators::UpdatableStructures<Var>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `is_time_table_empty` | `bool` | Stores whether the time-table is empty |
| `parameters` | `crate::propagators::CumulativeParameters<Var>` | Stores the input parameters to the cumulative constraint |
| `updatable_structures` | `crate::propagators::UpdatableStructures<Var>` | Stores structures which change during the search; used to store the bounds |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(arg_tasks: &[ArgTask<Var>], capacity: i32, cumulative_options: CumulativePropagatorOptions) -> TimeTableOverIntervalPropagator<Var> { /* ... */ }
  ```

###### Trait Implementations

- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **Propagator**
  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **Freeze**
- **Send**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

#### Type Alias `OverIntervalTimeTableType`

The type of the time-table used by propagators which use time-table reasoning over intervals.

The [ResourceProfile]s are sorted based on start time and they are non-overlapping; each entry
in the [`Vec`] represents the mandatory resource usage across an interval.

```rust
pub(crate) type OverIntervalTimeTableType<Var> = Vec<crate::propagators::ResourceProfile<Var>>;
```

### Functions

#### Function `create_time_table_over_interval_from_scratch`

Creates a time-table consisting of [`ResourceProfile`]s which represent rectangles with a
start and end (both inclusive) consisting of tasks with a cumulative height.

**Assumptions:**
The time-table is sorted based on start time and none of the profiles overlap - it is
assumed that the calculated [`ResourceProfile`]s are maximal

The result of this method is either the time-table of type
[`OverIntervalTimeTableType`] or the tasks responsible for the
conflict in the form of an [`Inconsistency`].

```rust
pub(crate) fn create_time_table_over_interval_from_scratch<Var: IntegerVariable + ''static, Context: ReadDomains + Copy>(context: Context, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<Vec<crate::propagators::ResourceProfile<Var>>, crate::predicates::PropositionalConjunction> { /* ... */ }
```

#### Function `create_events`

Creates a list of all the events (for the starts and ends of mandatory parts) of all the
tasks defined in `parameters`.

The events are returned in chonological order, if a tie between time points occurs then this
is resolved by placing the events which signify the ends of mandatory parts first (if the
tie is between events of the same type then the tie-breaking is done on the id in
non-decreasing order).

```rust
pub(in ::propagators::cumulative::time_table::time_table_over_interval) fn create_events<Var: IntegerVariable + ''static, Context: ReadDomains + Copy>(context: Context, parameters: &crate::propagators::CumulativeParameters<Var>) -> Vec<Event<Var>> { /* ... */ }
```

#### Function `create_time_table_from_events`

Creates a time-table based on the provided `events` (which are assumed to be sorted
chronologically, with tie-breaking performed in such a way that the ends of mandatory parts
are before the starts of mandatory parts).

```rust
pub(in ::propagators::cumulative::time_table::time_table_over_interval) fn create_time_table_from_events<Var: IntegerVariable + ''static, Context: ReadDomains + Copy>(events: Vec<Event<Var>>, context: Context, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<Vec<crate::propagators::ResourceProfile<Var>>, crate::predicates::PropositionalConjunction> { /* ... */ }
```

#### Function `check_starting_new_profile_invariants`

```rust
pub(in ::propagators::cumulative::time_table::time_table_over_interval) fn check_starting_new_profile_invariants<Var: IntegerVariable + ''static>(event: &Event<Var>, current_resource_usage: i32, current_profile_tasks: &[std::rc::Rc<crate::propagators::Task<Var>>]) -> bool { /* ... */ }
```

#### Function `debug_propagate_from_scratch_time_table_interval`

```rust
pub(crate) fn debug_propagate_from_scratch_time_table_interval<Var: IntegerVariable + ''static>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, parameters: &crate::propagators::CumulativeParameters<Var>, updatable_structures: &crate::propagators::UpdatableStructures<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

## Module `time_table_per_point`

[`Propagator`] for the Cumulative constraint; it
reasons over individual time-points instead of intervals. See [`TimeTablePerPointPropagator`]
for more information.

```rust
pub(in ::propagators::cumulative::time_table) mod time_table_per_point { /* ... */ }
```

### Types

#### Struct `TimeTablePerPointPropagator`

[`Propagator`] responsible for using time-table reasoning to propagate the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) constraint
where a time-table is a structure which stores the mandatory resource usage of the tasks at
different time-points - This method creates a resource profile per time point rather than
creating one over an interval (hence the name). Furthermore, the [`TimeTablePerPointPropagator`]
has a generic argument which represents the type of variable used for modelling the start
variables, this will be an implementation of [`IntegerVariable`].

See [Sections 4.2.1, 4.5.2 and 4.6.1-4.6.3 of \[1\]](http://cp2013.a4cp.org/sites/default/files/andreas_schutt_-_improving_scheduling_by_learning.pdf)
 for more information about time-table reasoning.

\[1\] A. Schutt, Improving scheduling by learning. University of Melbourne, Department of
Computer Science and Software Engineering, 2011.

```rust
pub(crate) struct TimeTablePerPointPropagator<Var> {
    pub(in ::propagators::cumulative::time_table::time_table_per_point) is_time_table_empty: bool,
    pub(in ::propagators::cumulative::time_table::time_table_per_point) parameters: crate::propagators::CumulativeParameters<Var>,
    pub(in ::propagators::cumulative::time_table::time_table_per_point) updatable_structures: crate::propagators::UpdatableStructures<Var>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `is_time_table_empty` | `bool` | Stores whether the time-table is empty |
| `parameters` | `crate::propagators::CumulativeParameters<Var>` | Stores the input parameters to the cumulative constraint |
| `updatable_structures` | `crate::propagators::UpdatableStructures<Var>` | Stores structures which change during the search; used to store the bounds |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(arg_tasks: &[ArgTask<Var>], capacity: i32, cumulative_options: CumulativePropagatorOptions) -> TimeTablePerPointPropagator<Var> { /* ... */ }
  ```

###### Trait Implementations

- **Propagator**
  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Send**
- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
#### Type Alias `PerPointTimeTableType`

The type of the time-table used by propagators which use time-table reasoning per time-point;
using a [`ResourceProfile`] is more complex than necessary (as [`ResourceProfile::start`] =
[`ResourceProfile::end`]) but it allows for a more unified implementation of methods.

The key t (representing a time-point) holds the mandatory resource consumption of tasks at
that time (stored in a [`ResourceProfile`]); the [ResourceProfile]s are sorted based on
start time and they are non-overlapping

```rust
pub(crate) type PerPointTimeTableType<Var> = std::collections::BTreeMap<u32, crate::propagators::ResourceProfile<Var>>;
```

### Functions

#### Function `create_time_table_per_point_from_scratch`

Creates a time-table consisting of [`ResourceProfile`]s which represent rectangles with a
start and end (both inclusive) consisting of tasks with a cumulative height Assumptions:
The time-table is sorted based on start time and none of the profiles overlap - generally,
it is assumed that the calculated [`ResourceProfile`]s are maximal

The result of this method is either the time-table of type
[`PerPointTimeTableType`] or the tasks responsible for the
conflict in the form of an [`Inconsistency`].

```rust
pub(crate) fn create_time_table_per_point_from_scratch<Var: IntegerVariable + ''static, Context: ReadDomains + Copy>(context: Context, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<std::collections::BTreeMap<u32, crate::propagators::ResourceProfile<Var>>, crate::predicates::PropositionalConjunction> { /* ... */ }
```

#### Function `debug_propagate_from_scratch_time_table_point`

```rust
pub(crate) fn debug_propagate_from_scratch_time_table_point<Var: IntegerVariable + ''static>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, parameters: &crate::propagators::CumulativeParameters<Var>, updatable_structures: &crate::propagators::UpdatableStructures<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

## Module `time_table_util`

Defines common methods for [`Propagator`]s which make use of time-table
reasoning (see [`crate::propagators::cumulative::time_table`] for more information) such as
[`should_enqueue`] or [`propagate_based_on_timetable`].

```rust
pub(in ::propagators::cumulative::time_table) mod time_table_util { /* ... */ }
```

### Types

#### Struct `ShouldEnqueueResult`

The result of [`should_enqueue`], contains the [`EnqueueDecision`] whether the propagator should
currently be enqueued and potentially the updated [`Task`] (in the form of a
[`UpdatedTaskInfo`]) if the mandatory part of this [`Task`] has changed.

```rust
pub(crate) struct ShouldEnqueueResult<Var> {
    pub(crate) decision: propagator::EnqueueDecision,
    pub(crate) update: Option<crate::propagators::UpdatedTaskInfo<Var>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `decision` | `propagator::EnqueueDecision` | Whether the propagator which called this method should be enqueued |
| `update` | `Option<crate::propagators::UpdatedTaskInfo<Var>>` | If the mandatory part of the task passed to [`should_enqueue`] has changed then this field<br>will contain the corresponding [`UpdatedTaskInfo`] otherwise it will be [`None`].<br><br>In general, non-incremental propagators will not make use of this field since they will<br>propagate from scratch anyways. |

##### Implementations

###### Trait Implementations

- **UnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Freeze**
- **Unpin**
- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

#### Enum `CanUpdate`

An enum which represents which values can be updated by a profile

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) enum CanUpdate {
    LowerBound,
    UpperBound,
    Holes,
}
```

##### Variants

###### `LowerBound`

###### `UpperBound`

###### `Holes`

##### Implementations

###### Trait Implementations

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Sync**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **UnwindSafe**
- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

### Functions

#### Function `should_enqueue`

Determines whether a time-table propagator should enqueue and returns a structure containing the
[`EnqueueDecision`] and the info of the task with the extended mandatory part (or [`None`] if no
such task exists). This method should be called in the
[`ConstraintProgrammingPropagator::notify`] method.

```rust
pub(crate) fn should_enqueue<Var: IntegerVariable + ''static>(parameters: &crate::propagators::CumulativeParameters<Var>, updatable_structures: &crate::propagators::UpdatableStructures<Var>, updated_task: &std::rc::Rc<crate::propagators::Task<Var>>, context: contexts::propagation_context::PropagationContext<''_>, empty_time_table: bool) -> ShouldEnqueueResult<Var> { /* ... */ }
```

#### Function `has_mandatory_part`

```rust
pub(crate) fn has_mandatory_part<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>) -> bool { /* ... */ }
```

#### Function `has_mandatory_part_in_interval`

Checks whether a specific task (indicated by id) has a mandatory part which overlaps with the
interval [start, end]

```rust
pub(crate) fn has_mandatory_part_in_interval<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, start: i32, end: i32) -> bool { /* ... */ }
```

#### Function `task_has_overlap_with_interval`

Checks whether the lower and upper bound of a task overlap with the provided interval

```rust
pub(crate) fn task_has_overlap_with_interval<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, start: i32, end: i32) -> bool { /* ... */ }
```

#### Function `has_overlap_with_interval`

Determines whether the interval \[lower_bound, upper_bound\) overlaps with the interval \[start,
end\]

```rust
pub(crate) fn has_overlap_with_interval(lower_bound: i32, upper_bound: i32, start: i32, end: i32) -> bool { /* ... */ }
```

#### Function `debug_check_whether_profiles_are_maximal_and_sorted`

A method which checks whether the time-table (provided in the form of an iterator) is sorted
based on start time and that the profiles are maximal (i.e. the [`ResourceProfile::start`] and
[`ResourceProfile::end`] cannot be increased or decreased, respectively). It returns true if
both of these invariants hold and false otherwise.

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn debug_check_whether_profiles_are_maximal_and_sorted<''a, Var: IntegerVariable + ''static, /* synthetic */ impl Iterator<Item = &'a ResourceProfile<Var>> + Clone: Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone>(time_table: impl Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone) -> bool { /* ... */ }
```

#### Function `propagate_based_on_timetable`

Checks whether propagations should occur based on the current state of the time-table.

It goes over all profiles and all tasks and determines which ones should be propagated;
Note that this method is not idempotent and that it assumes that the [`ResourceProfile`]s are
sorted in increasing order in terms of [`ResourceProfile::start`] and that the
[`ResourceProfile`] is maximal (i.e. the [`ResourceProfile::start`] and [`ResourceProfile::end`]
cannot be increased or decreased, respectively).

```rust
pub(crate) fn propagate_based_on_timetable<''a, Var: IntegerVariable + ''static, /* synthetic */ impl Iterator<Item = &'a ResourceProfile<Var>> + Clone: Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, time_table: impl Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone, parameters: &crate::propagators::CumulativeParameters<Var>, updatable_structures: &mut crate::propagators::UpdatableStructures<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `propagate_single_profiles`

For each profile in chronological order, this method goes through the tasks and checks whether
the profile can propagate the domain of the task.

If it can then it will immediately propagate it even if this propagation would cause subsequent
propagations by the next profile. For a method which propagates based on a sequence of profiles
see [`propagate_sequence_of_profiles`].

This type of propagation is likely to be less beneficial for the explanation
[`CumulativeExplanationType::Pointwise`].

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn propagate_single_profiles<''a, Var: IntegerVariable + ''static, /* synthetic */ impl Iterator<Item = &'a ResourceProfile<Var>> + Clone: Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, time_table: impl Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone, updatable_structures: &mut crate::propagators::UpdatableStructures<Var>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `propagate_sequence_of_profiles`

For each task this method goes through the profiles in chronological order to find one which can
update the task's bounds.

If it can find such a profile then it proceeds to generate a sequence of profiles
which can propagate the bound of the task and uses these to explain the propagation rather than
the individual profiles (for propagating individual profiles see [`propagate_single_profiles`]).

Especially in the case of [`CumulativeExplanationType::Pointwise`] this is likely to be
beneficial.

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn propagate_sequence_of_profiles<''a, Var: IntegerVariable + ''static, /* synthetic */ impl Iterator<Item = &'a ResourceProfile<Var>> + Clone: Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, time_table: impl Iterator<Item = &''a crate::propagators::ResourceProfile<Var>> + Clone, updatable_structures: &crate::propagators::UpdatableStructures<Var>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Result<(), Inconsistency> { /* ... */ }
```

#### Function `find_index_last_profile_which_propagates_lower_bound`

Returns the index of the profile which cannot propagate the lower-bound of the provided task any
further based on the propagation of the upper-bound due to `time_table[profile_index]`.

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn find_index_last_profile_which_propagates_lower_bound<Var: IntegerVariable + ''static>(profile_index: usize, time_table: &[&crate::propagators::ResourceProfile<Var>], context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, capacity: i32) -> usize { /* ... */ }
```

#### Function `find_index_last_profile_which_propagates_upper_bound`

Returns the index of the last profile which could propagate the upper-bound of the task based on
the propagation of the upper-bound due to `time_table[profile_index]`.

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn find_index_last_profile_which_propagates_upper_bound<Var: IntegerVariable + ''static>(profile_index: usize, time_table: &[&crate::propagators::ResourceProfile<Var>], context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, capacity: i32) -> usize { /* ... */ }
```

#### Function `lower_bound_can_be_propagated_by_profile`

Determines whether the lower bound of a task can be propagated by a [`ResourceProfile`] with the
provided start time and end time; This method checks the following conditions:
    * lb(s) + p > start, i.e. the earliest completion time of the task is after the start of the
      [`ResourceProfile`]
    * lb(s) <= end, i.e. the earliest start time is before the end of the [`ResourceProfile`]

Note: It is assumed that task.resource_usage + height > capacity (i.e. the task has the
potential to overflow the capacity in combination with the profile)

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn lower_bound_can_be_propagated_by_profile<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, capacity: i32) -> bool { /* ... */ }
```

#### Function `upper_bound_can_be_propagated_by_profile`

Determines whether the upper bound of a task can be propagated by a [`ResourceProfile`] with the
provided start time and end time This method checks the following conditions:
    * ub(s) + p > start, i.e. the latest completion time is after the start of the
      [`ResourceProfile`]
    * ub(s) <= end, i.e. the latest start time is before the end of the [`ResourceProfile`]
Note: It is assumed that the task is known to overflow the [`ResourceProfile`]

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn upper_bound_can_be_propagated_by_profile<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, capacity: i32) -> bool { /* ... */ }
```

#### Function `can_be_updated_by_profile`

Returns whether the provided `task` can be updated by the profile by checking the following:
1. Whether the task and the profile together would overflow the resource capacity
2. Whether the task has a mandatory part in the profile
3. Whether the bounds of the task overlap with the profile

If the first condition is true, the second false and the third true then this method returns
true (otherwise it returns false)

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn can_be_updated_by_profile<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, capacity: i32) -> bool { /* ... */ }
```

#### Function `overflows_capacity_and_is_not_part_of_profile`

Returns whether the provided `task` passes the following checks:
1. Whether the task and the profile together would overflow the resource capacity
2. Whether the task has a mandatory part in the profile

If the first condition is true, and the second false then this method returns
true (otherwise it returns false)

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn overflows_capacity_and_is_not_part_of_profile<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, capacity: i32) -> bool { /* ... */ }
```

#### Function `find_possible_updates`

The method checks whether the current task can be propagated by the provided profile and (if
appropriate) performs the propagation. It then returns whether any of the propagations led to a
conflict or whether all propagations were succesful.

Note that this method can only find [`Inconsistency::EmptyDomain`] conflicts which means that we
handle that error in the parent function

```rust
pub(in ::propagators::cumulative::time_table::time_table_util) fn find_possible_updates<Var: IntegerVariable + ''static>(context: &mut contexts::propagation_context::PropagationContextMut<''_>, task: &std::rc::Rc<crate::propagators::Task<Var>>, profile: &crate::propagators::ResourceProfile<Var>, parameters: &crate::propagators::CumulativeParameters<Var>) -> Vec<CanUpdate> { /* ... */ }
```

#### Function `insert_update`

```rust
pub(crate) fn insert_update<Var: IntegerVariable + ''static>(updated_task: &std::rc::Rc<crate::propagators::Task<Var>>, updatable_structures: &mut crate::propagators::UpdatableStructures<Var>, potential_update: Option<crate::propagators::UpdatedTaskInfo<Var>>) { /* ... */ }
```

#### Function `backtrack_update`

```rust
pub(crate) fn backtrack_update<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, updatable_structures: &mut crate::propagators::UpdatableStructures<Var>, updated_task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

### Re-exports

#### Re-export `CumulativeExplanationType`

```rust
pub use explanations::CumulativeExplanationType;
```

## Module `options`

```rust
pub(in ::propagators::cumulative) mod options { /* ... */ }
```

### Types

#### Struct `CumulativePropagatorOptions`

```rust
pub(crate) struct CumulativePropagatorOptions {
    pub(crate) allow_holes_in_domain: bool,
    pub(crate) explanation_type: super::CumulativeExplanationType,
    pub(crate) generate_sequence: bool,
    pub(crate) incremental_backtracking: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `allow_holes_in_domain` | `bool` | Specifies whether it is allowed to create holes in the domain; if this parameter is set to<br>false then it will only adjust the bounds when appropriate rather than removing values from<br>the domain |
| `explanation_type` | `super::CumulativeExplanationType` | The type of explanation which is used by the cumulative to explain propagations and<br>conflicts. |
| `generate_sequence` | `bool` | Determines whether a sequence of profiles is generated when explaining a propagation. |
| `incremental_backtracking` | `bool` | Determines whether to incrementally backtrack or to calculate from scratch |

##### Implementations

###### Trait Implementations

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> CumulativePropagatorOptions { /* ... */ }
    ```

- **Copy**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> CumulativePropagatorOptions { /* ... */ }
    ```

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Unpin**
#### Struct `CumulativeOptions`

```rust
pub struct CumulativeOptions {
    pub(crate) propagation_method: CumulativePropagationMethod,
    pub(crate) propagator_options: CumulativePropagatorOptions,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `propagation_method` | `CumulativePropagationMethod` | The propagation method which is used for the cumulative constraints; currently all of them<br>are variations of time-tabling. The default is incremental time-tabling reasoning over<br>intervals. |
| `propagator_options` | `CumulativePropagatorOptions` | The options which are passed to the propagator itself |

##### Implementations

###### Methods

- ```rust
  pub fn new(allow_holes_in_domain: bool, explanation_type: CumulativeExplanationType, generate_sequence: bool, propagation_method: CumulativePropagationMethod, incremental_backtracking: bool) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Copy**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> CumulativeOptions { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> CumulativeOptions { /* ... */ }
    ```

- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Sync**
- **Unpin**
- **Freeze**
- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

#### Enum `CumulativePropagationMethod`

```rust
pub enum CumulativePropagationMethod {
    TimeTablePerPoint,
    TimeTablePerPointIncremental,
    TimeTablePerPointIncrementalSynchronised,
    TimeTableOverInterval,
    TimeTableOverIntervalIncremental,
    TimeTableOverIntervalIncrementalSynchronised,
}
```

##### Variants

###### `TimeTablePerPoint`

###### `TimeTablePerPointIncremental`

###### `TimeTablePerPointIncrementalSynchronised`

###### `TimeTableOverInterval`

###### `TimeTableOverIntervalIncremental`

###### `TimeTableOverIntervalIncrementalSynchronised`

##### Implementations

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Sync**
- **Copy**
- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **UnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> CumulativePropagationMethod { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> CumulativePropagationMethod { /* ... */ }
    ```

- **ValueEnum**
  - ```rust
    fn value_variants<''a>() -> &''a [Self] { /* ... */ }
    ```

  - ```rust
    fn to_possible_value<''a>(self: &Self) -> ::std::option::Option<clap::builder::PossibleValue> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Send**
## Module `utils`

Utilities for propagators of the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html)
constraint which are generalisable enough to be useful for different types of cumulative
propagators

```rust
pub(in ::propagators::cumulative) mod utils { /* ... */ }
```

### Modules

## Module `structs`

```rust
pub(in ::propagators::cumulative::utils) mod structs { /* ... */ }
```

### Modules

## Module `mandatory_part_adjustments`

```rust
pub(in ::propagators::cumulative::utils::structs) mod mandatory_part_adjustments { /* ... */ }
```

### Types

#### Struct `MandatoryPartAdjustments`

Represents adjustments to a mandatory part due to bound changes.

It contains both the additions to the mandatory part (stored in
[`MandatoryPartAdjustments::added_parts`]) and the removals from the mandatory part
[`MandatoryPartAdjustments::removed_parts`].

```rust
pub(crate) struct MandatoryPartAdjustments {
    pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) added_parts: Vec<std::ops::Range<i32>>,
    pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) removed_parts: Vec<std::ops::Range<i32>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `added_parts` | `Vec<std::ops::Range<i32>>` | The additions to the mandatory part |
| `removed_parts` | `Vec<std::ops::Range<i32>>` | The removals from the mandatory part |

##### Implementations

###### Methods

- ```rust
  pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) fn new(added_parts: Vec<Range<i32>>, removed_parts: Vec<Range<i32>>) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_removed_parts(self: &Self) -> impl Iterator<Item = Range<i32>> + ''_ { /* ... */ }
  ```
  Returns an iterator over the removed ranges of the mandatory part; only returns non-empty

- ```rust
  pub(crate) fn get_added_parts(self: &Self) -> impl Iterator<Item = Range<i32>> + ''_ { /* ... */ }
  ```
  Returns an iterator over the added ranges of the mandatory part; only returns non-mepty

- ```rust
  pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) fn empty() -> Self { /* ... */ }
  ```
  Creates an empty [`MandatoryPartAdjustments`] (i.e. with no added parts and with no removed

- ```rust
  pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) fn from_added_part(added_part: Range<i32>) -> Self { /* ... */ }
  ```
  Creates a [`MandatoryPartAdjustments`] containing a single added part.

- ```rust
  pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) fn from_removed_part(removed_part: Range<i32>) -> Self { /* ... */ }
  ```
  Creates a [`MandatoryPartAdjustments`] containing a single removed part.

- ```rust
  pub(in ::propagators::cumulative::utils::structs::mandatory_part_adjustments) fn from_added_and_removed_part(added_part: Range<i32>, removed_part: Range<i32>) -> Self { /* ... */ }
  ```
  Creates a [`MandatoryPartAdjustments`] containing a single added part and a single removed

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `parameters`

```rust
pub(in ::propagators::cumulative::utils::structs) mod parameters { /* ... */ }
```

### Types

#### Struct `CumulativeParameters`

Holds the data for the cumulative constraint; more specifically it holds:
- The tasks
- The capacity of the resource
- The options for propagating the cumulative constraint

```rust
pub(crate) struct CumulativeParameters<Var> {
    pub(crate) tasks: Box<[std::rc::Rc<super::Task<Var>>]>,
    pub(crate) capacity: i32,
    pub(crate) options: crate::propagators::CumulativePropagatorOptions,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `tasks` | `Box<[std::rc::Rc<super::Task<Var>>]>` | The Set of [`Task`]s; for each [`Task`], the [`Task::id`] is assumed to correspond to its<br>index in this [`Vec`]; this is stored as a [`Box`] of [`Rc`]'s to accomodate the<br>sharing of the tasks |
| `capacity` | `i32` | The capacity of the resource (i.e. how much resource consumption can be maximally<br>accomodated at each time point) |
| `options` | `crate::propagators::CumulativePropagatorOptions` | The [`CumulativeOptions`] which influence the behaviour of the cumulative propagator(s). |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(tasks: Vec<Task<Var>>, capacity: i32, options: CumulativePropagatorOptions) -> CumulativeParameters<Var> { /* ... */ }
  ```

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **UnwindSafe**
- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> CumulativeParameters<Var> { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

## Module `resource_profile`

```rust
pub(in ::propagators::cumulative::utils::structs) mod resource_profile { /* ... */ }
```

### Types

#### Struct `ResourceProfile`

Structures used for storing the data related to resource profiles;
A [`ResourceProfile`] represents a rectangle where the height is the cumulative mandatory
resource usage of the [`profile tasks`][ResourceProfile::profile_tasks]

```rust
pub(crate) struct ResourceProfile<Var> {
    pub(crate) start: i32,
    pub(crate) end: i32,
    pub(crate) profile_tasks: Vec<std::rc::Rc<super::Task<Var>>>,
    pub(crate) height: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `start` | `i32` | The start time of the [`ResourceProfile`] (inclusive) |
| `end` | `i32` | The end time of the [`ResourceProfile`] (inclusive) |
| `profile_tasks` | `Vec<std::rc::Rc<super::Task<Var>>>` | The IDs of the tasks which are part of the profile |
| `height` | `i32` | The amount of cumulative resource usage of all [`profile<br>tasks`][ResourceProfile::profile_tasks] (i.e. the height of the rectangle) |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn default(time: i32) -> ResourceProfile<Var> { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ResourceProfile<Var> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

## Module `task`

```rust
pub(in ::propagators::cumulative::utils::structs) mod task { /* ... */ }
```

### Types

#### Struct `Task`

Structure which stores the variables related to a task; for now, only the start times are
assumed to be variable

```rust
pub(crate) struct Task<Var> {
    pub(crate) start_variable: Var,
    pub(crate) processing_time: i32,
    pub(crate) resource_usage: i32,
    pub(crate) id: local_id::LocalId,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `start_variable` | `Var` | The variable representing the start time of a task |
| `processing_time` | `i32` | The processing time of the `start_variable` (also referred to as duration of a task) |
| `resource_usage` | `i32` | How much of the resource the given task uses during its non-preemptive execution |
| `id` | `local_id::LocalId` | The [`LocalId`] of the task |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn get_id(task: &Rc<Task<Var>>) -> usize { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Self) -> bool { /* ... */ }
    ```

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Send**
- **Sync**
- **Unpin**
- **Eq**
- **UnwindSafe**
- **Hash**
  - ```rust
    fn hash<H: std::hash::Hasher>(self: &Self, state: &mut H) { /* ... */ }
    ```

- **IntoEither**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

#### Struct `ArgTask`

The task which is passed as argument

```rust
pub(crate) struct ArgTask<Var> {
    pub(crate) start_time: Var,
    pub(crate) processing_time: i32,
    pub(crate) resource_usage: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `start_time` | `Var` | The [`IntegerVariable`] representing the start time of a task |
| `processing_time` | `i32` | The processing time of the [`start_time`][ArgTask::start_time] (also referred to as<br>duration of a task) |
| `resource_usage` | `i32` | How much of the resource the given task uses during its non-preemptive execution |

##### Implementations

###### Trait Implementations

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ArgTask<Var> { /* ... */ }
    ```

## Module `updatable_structures`

```rust
pub(in ::propagators::cumulative::utils::structs) mod updatable_structures { /* ... */ }
```

### Types

#### Struct `UpdatableStructures`

Structures which are adjusted during search; either due to incrementality or to keep track of
bounds.

```rust
pub(crate) struct UpdatableStructures<Var> {
    pub(in ::propagators::cumulative::utils::structs::updatable_structures) bounds: Vec<(i32, i32)>,
    pub(in ::propagators::cumulative::utils::structs::updatable_structures) updates: Vec<super::UpdatedTaskInfo<Var>>,
    pub(in ::propagators::cumulative::utils::structs::updatable_structures) updated_tasks: sparse_set::SparseSet<std::rc::Rc<super::Task<Var>>>,
    pub(in ::propagators::cumulative::utils::structs::updatable_structures) unfixed_tasks: sparse_set::SparseSet<std::rc::Rc<super::Task<Var>>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `bounds` | `Vec<(i32, i32)>` | The current known bounds of the different [tasks][CumulativeParameters::tasks]; stored as<br>(lower bound, upper bound)<br><br>`bounds[i]` represents the currently known bounds of task i |
| `updates` | `Vec<super::UpdatedTaskInfo<Var>>` | The [`Task`]s which have been updated since the last round of propagation, this structure<br>is updated by the (incremental) propagator |
| `updated_tasks` | `sparse_set::SparseSet<std::rc::Rc<super::Task<Var>>>` | The tasks which have been updated since the last iteration |
| `unfixed_tasks` | `sparse_set::SparseSet<std::rc::Rc<super::Task<Var>>>` | The tasks which are unfixed |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(parameters: &CumulativeParameters<Var>) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn has_updates(self: &Self) -> bool { /* ... */ }
  ```
  Returns whether there are any updates stored which have not been processed

- ```rust
  pub(crate) fn pop_next_updated_task(self: &mut Self) -> Option<Rc<Task<Var>>> { /* ... */ }
  ```
  Returns the next updated task and removes it from the updated list

- ```rust
  pub(crate) fn get_update_for_task(self: &mut Self, updated_task: &Rc<Task<Var>>) -> UpdatedTaskInfo<Var> { /* ... */ }
  ```
  Get the update info for the provided task (note that this method does not actually check

- ```rust
  pub(crate) fn reset_update_for_task(self: &mut Self, updated_task: &Rc<Task<Var>>) { /* ... */ }
  ```
  Resets the stored update for the current task to be equal to the current scenario; i.e.

- ```rust
  pub(crate) fn get_stored_bounds(self: &Self) -> &[(i32, i32)] { /* ... */ }
  ```
  Returns the bounds which are stored for each tasks.

- ```rust
  pub(crate) fn get_stored_bounds_mut(self: &mut Self) -> &mut [(i32, i32)] { /* ... */ }
  ```
  Returns a mutable reference to the bounds which are stored for each task.

- ```rust
  pub(crate) fn get_stored_lower_bound(self: &Self, task: &Rc<Task<Var>>) -> i32 { /* ... */ }
  ```
  Returns the stored lower-bound for a task.

- ```rust
  pub(crate) fn get_stored_upper_bound(self: &Self, task: &Rc<Task<Var>>) -> i32 { /* ... */ }
  ```
  Returns the stored upper-bound for a task.

- ```rust
  pub(crate) fn fix_task(self: &mut Self, updated_task: &Rc<Task<Var>>) { /* ... */ }
  ```
  Fixes a task in the internal structure(s).

- ```rust
  pub(crate) fn unfix_task(self: &mut Self, updated_task: Rc<Task<Var>>) { /* ... */ }
  ```
  Unfixes a task in the internal structure(s).

- ```rust
  pub(crate) fn remove_fixed(self: &mut Self, context: PropagationContext<''_>, parameters: &CumulativeParameters<Var>) { /* ... */ }
  ```
  Removes the fixed tasks from the internal structure(s).

- ```rust
  pub(crate) fn reset_all_bounds_and_remove_fixed(self: &mut Self, context: PropagationContext<''_>, parameters: &CumulativeParameters<Var>) { /* ... */ }
  ```
  Resets all of the bounds to the current values in the context and removes all of the fixed

- ```rust
  pub(crate) fn initialise_bounds_and_remove_fixed(self: &mut Self, context: PropagationContext<''_>, parameters: &CumulativeParameters<Var>) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_unfixed_tasks(self: &Self) -> impl Iterator<Item = &Rc<Task<Var>>> { /* ... */ }
  ```
  Returns all of the tasks which are not currently fixed

- ```rust
  pub(crate) fn get_fixed_tasks(self: &Self) -> impl Iterator<Item = &Rc<Task<Var>>> { /* ... */ }
  ```

- ```rust
  pub(crate) fn number_of_unfixed_tasks(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn has_no_unfixed_tasks(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn temporarily_remove_task_from_unfixed(self: &mut Self, task: &Rc<Task<Var>>) { /* ... */ }
  ```

- ```rust
  pub(crate) fn restore_temporarily_removed(self: &mut Self) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_unfixed_task_at_index(self: &Self, index: usize) -> Rc<Task<Var>> { /* ... */ }
  ```

- ```rust
  pub(crate) fn task_has_been_updated(self: &mut Self, task: &Rc<Task<Var>>) { /* ... */ }
  ```

- ```rust
  pub(crate) fn insert_update_for_task(self: &mut Self, task: &Rc<Task<Var>>, updated_task_info: UpdatedTaskInfo<Var>) { /* ... */ }
  ```

- ```rust
  pub(crate) fn recreate_from_context(self: &Self, context: PropagationContext<''_>, parameters: &CumulativeParameters<Var>) -> Self { /* ... */ }
  ```
  Used for creating the dynamic structures from the provided context

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> UpdatableStructures<Var> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

## Module `updated_task_info`

```rust
pub(in ::propagators::cumulative::utils::structs) mod updated_task_info { /* ... */ }
```

### Types

#### Struct `UpdatedTaskInfo`

Stores the information of an updated task; for example in the context of
[`TimeTablePerPointPropagator`] this is a task whose mandatory part has changed.

```rust
pub(crate) struct UpdatedTaskInfo<Var> {
    pub(crate) task: std::rc::Rc<super::Task<Var>>,
    pub(crate) old_lower_bound: i32,
    pub(crate) old_upper_bound: i32,
    pub(crate) new_lower_bound: i32,
    pub(crate) new_upper_bound: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `task` | `std::rc::Rc<super::Task<Var>>` | The task which has been updated (where "updated" is according to some context-dependent<br>definition) |
| `old_lower_bound` | `i32` | The lower-bound of the [`Task`] before the update |
| `old_upper_bound` | `i32` | The upper-bound of the [`Task`] before the update |
| `new_lower_bound` | `i32` | The lower-bound of the [`Task`] after the update |
| `new_upper_bound` | `i32` | The upper-bound of the [`Task`] after the update |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn get_mandatory_part_adjustments(self: &Self) -> MandatoryPartAdjustments { /* ... */ }
  ```
  Returns the adjustments which need to be made to the time-table in the form of a

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> UpdatedTaskInfo<Var> { /* ... */ }
    ```

- **Send**
- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `util`

Contains common methods for all of the propagators of the cumulative constraint; this includes
methods for propagating but also methods related to creating the
input parameters.

```rust
pub(crate) mod util { /* ... */ }
```

### Functions

#### Function `create_tasks`

Based on the [`ArgTask`]s which are passed, it creates and returns [`Task`]s which have been
registered for [`DomainEvents`].

It sorts [`Task`]s on non-decreasing resource usage and removes [`Task`]s with resource usage 0.

```rust
pub(crate) fn create_tasks<Var: IntegerVariable + ''static>(arg_tasks: &[crate::propagators::ArgTask<Var>]) -> Vec<crate::propagators::Task<Var>> { /* ... */ }
```

#### Function `register_tasks`

```rust
pub(crate) fn register_tasks<Var: IntegerVariable + ''static>(tasks: &[std::rc::Rc<crate::propagators::Task<Var>>], context: &mut contexts::propagator_initialisation_context::PropagatorInitialisationContext<''_>, register_backtrack: bool) { /* ... */ }
```

#### Function `update_bounds_task`

Updates the bounds of the provided [`Task`] to those stored in
`context`.

```rust
pub(crate) fn update_bounds_task<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, bounds: &mut [(i32, i32)], task: &std::rc::Rc<crate::propagators::Task<Var>>) { /* ... */ }
```

#### Function `check_bounds_equal_at_propagation`

Determines whether the stored bounds are equal when propagation occurs

```rust
pub(crate) fn check_bounds_equal_at_propagation<Var: IntegerVariable + ''static>(context: contexts::propagation_context::PropagationContext<''_>, tasks: &[std::rc::Rc<crate::propagators::Task<Var>>], bounds: &[(i32, i32)]) -> bool { /* ... */ }
```

### Re-exports

#### Re-export `CumulativeExplanationType`

```rust
pub use time_table::CumulativeExplanationType;
```

#### Re-export `options::*`

```rust
pub use options::*;
```

## Module `element`

```rust
pub(crate) mod element { /* ... */ }
```

### Types

#### Struct `ElementPropagator`

Arc-consistent propagator for constraint `element([x_1, \ldots, x_n], i, e)`, where `x_j` are
 variables, `i` is an integer variable, and `e` is a variable, which holds iff `x_i = e`

Note that this propagator is 0-indexed

```rust
pub(crate) struct ElementPropagator<VX, VI, VE> {
    pub(in ::propagators::element) array: Box<[VX]>,
    pub(in ::propagators::element) index: VI,
    pub(in ::propagators::element) rhs: VE,
    pub(in ::propagators::element) rhs_reason_buffer: Vec<crate::predicates::Predicate>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `array` | `Box<[VX]>` |  |
| `index` | `VI` |  |
| `rhs` | `VE` |  |
| `rhs_reason_buffer` | `Vec<crate::predicates::Predicate>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(array: Box<[VX]>, index: VI, rhs: VE) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) fn propagate_index_bounds_within_array(self: &Self, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Propagate the bounds of `self.index` to be in the range `[0, self.array.len())`.

- ```rust
  pub(in ::propagators::element) fn propagate_rhs_bounds_based_on_array(self: &Self, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  The lower bound (resp. upper bound) of the right-hand side can be the minimum lower

- ```rust
  pub(in ::propagators::element) fn propagate_index_based_on_domain_intersection_with_rhs(self: &Self, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Go through the array. For every element for which the domain does not intersect with the

- ```rust
  pub(in ::propagators::element) fn propagate_equality(self: &Self, context: &mut PropagationContextMut<''_>, index: i32) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Propagate equality between lhs and rhs. This assumes the bounds of rhs have already been

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **UnwindSafe**
- **Sync**
- **Propagator**
  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn lazy_explanation(self: &mut Self, code: u64, context: ExplanationContext<''_>) -> &[Predicate] { /* ... */ }
    ```

- **Freeze**
- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Send**
- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ElementPropagator<VX, VI, VE> { /* ... */ }
    ```

#### Enum `Bound`

**Attributes:**

- `#[repr(u8)]`

```rust
pub(in ::propagators::element) enum Bound {
    Lower = 0,
    Upper = 1,
}
```

##### Variants

###### `Lower`

Discriminant: `0`

Discriminant value: `0`

###### `Upper`

Discriminant: `1`

Discriminant value: `1`

##### Implementations

###### Methods

- ```rust
  pub(in ::propagators::element) const fn into_bits(self: Self) -> u8 { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) const fn from_bits(value: u8) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **RefUnwindSafe**
- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Bound) -> bool { /* ... */ }
    ```

- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Eq**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Bound { /* ... */ }
    ```

- **StructuralPartialEq**
- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Copy**
#### Struct `RightHandSideReason`

**Attributes:**

- `#[repr(transparent)]`

```rust
pub(in ::propagators::element) struct RightHandSideReason(pub(in ::propagators::element) u64);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `u64` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::propagators::element) const fn new() -> Self { /* ... */ }
  ```
  Creates a new default initialized bitfield.

- ```rust
  pub(in ::propagators::element) const fn from_bits(bits: u64) -> Self { /* ... */ }
  ```
  Convert from bits.

- ```rust
  pub(in ::propagators::element) const fn into_bits(self: Self) -> u64 { /* ... */ }
  ```
  Convert into bits.

- ```rust
  pub(in ::propagators::element) const fn bound(self: &Self) -> Bound { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) const fn with_bound_checked(self: Self, value: Bound) -> core::result::Result<Self, ()> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) const fn with_bound(self: Self, value: Bound) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) fn set_bound(self: &mut Self, value: Bound) { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) fn set_bound_checked(self: &mut Self, value: Bound) -> core::result::Result<(), ()> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) const fn value(self: &Self) -> i32 { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) const fn with_value_checked(self: Self, value: i32) -> core::result::Result<Self, ()> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) const fn with_value(self: Self, value: i32) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) fn set_value(self: &mut Self, value: i32) { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::element) fn set_value_checked(self: &mut Self, value: i32) -> core::result::Result<(), ()> { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

  - ```rust
    fn from(v: u64) -> Self { /* ... */ }
    ```

  - ```rust
    fn from(v: RightHandSideReason) -> u64 { /* ... */ }
    ```

- **Unpin**
- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut core::fmt::Formatter<''_>) -> core::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> RightHandSideReason { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Copy**
- **Sync**
- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

### Constants and Statics

#### Constant `ID_INDEX`

```rust
pub(in ::propagators::element) const ID_INDEX: local_id::LocalId = _;
```

#### Constant `ID_RHS`

```rust
pub(in ::propagators::element) const ID_RHS: local_id::LocalId = _;
```

#### Constant `ID_X_OFFSET`

```rust
pub(in ::propagators::element) const ID_X_OFFSET: u32 = 2;
```

## Module `nogoods`

```rust
pub(crate) mod nogoods { /* ... */ }
```

### Modules

## Module `learning_options`

```rust
pub(in ::propagators::nogoods) mod learning_options { /* ... */ }
```

### Types

#### Struct `LearningOptions`

Options which determine how the learned clauses are handled .

These options influence when the learned clause database removed clauses.

```rust
pub struct LearningOptions {
    pub max_activity: f32,
    pub activity_decay_factor: f32,
    pub limit_num_high_lbd_nogoods: usize,
    pub lbd_threshold: u32,
    pub nogood_sorting_strategy: LearnedNogoodSortingStrategy,
    pub activity_bump_increment: f32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `max_activity` | `f32` | Determines when to rescale the activites of the learned clauses in the database. |
| `activity_decay_factor` | `f32` | Determines the factor by which the activities are divided when a conflict is found. |
| `limit_num_high_lbd_nogoods` | `usize` | The maximum number of clauses with an LBD higher than [`LearningOptions::lbd_threshold`]<br>allowed by the learned clause database. If there are more clauses with an LBD higher than<br>[`LearningOptions::lbd_threshold`] then removal from the database will be considered. |
| `lbd_threshold` | `u32` | The treshold which specifies whether a learned clause database is considered to be with<br>"High" LBD or "Low" LBD. Learned clauses with high LBD will be considered for removal. |
| `nogood_sorting_strategy` | `LearnedNogoodSortingStrategy` | Specifies how the learned clauses are sorted when considering removal. |
| `activity_bump_increment` | `f32` | Specifies by how much the activity is increased when a nogood is bumped. |

##### Implementations

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Copy**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> LearningOptions { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Send**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Unpin**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Freeze**
- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

#### Enum `LearnedNogoodSortingStrategy`

The sorting strategy which is used when considering removal from the clause database.

```rust
pub enum LearnedNogoodSortingStrategy {
    Activity,
    Lbd,
}
```

##### Variants

###### `Activity`

Sorts based on the activity, the activity is bumped when a literal is encountered during
conflict analysis.

###### `Lbd`

Sorts based on the literal block distance (LBD) which is an indication of how "good" a
learned clause is.

##### Implementations

###### Trait Implementations

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Eq**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **RefUnwindSafe**
- **StructuralPartialEq**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &LearnedNogoodSortingStrategy) -> bool { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> Result<(), std::fmt::Error> { /* ... */ }
    ```

- **ValueEnum**
  - ```rust
    fn value_variants<''a>() -> &''a [Self] { /* ... */ }
    ```

  - ```rust
    fn to_possible_value<''a>(self: &Self) -> ::std::option::Option<clap::builder::PossibleValue> { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **IntoEither**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> LearnedNogoodSortingStrategy { /* ... */ }
    ```

- **Unpin**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> LearnedNogoodSortingStrategy { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **Freeze**
- **Copy**
## Module `nogood`

```rust
pub(in ::propagators::nogoods) mod nogood { /* ... */ }
```

### Types

#### Struct `Nogood`

A struct which represents a nogood (i.e. a list of [`Predicate`]s which cannot all be true at
the same time).

It additionally contains certain fields related to how the clause was created/activity.

```rust
pub(crate) struct Nogood {
    pub(crate) predicates: crate::predicates::PropositionalConjunction,
    pub(crate) is_learned: bool,
    pub(crate) lbd: u32,
    pub(crate) is_protected: bool,
    pub(crate) is_deleted: bool,
    pub(crate) block_bumps: bool,
    pub(crate) activity: f32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `predicates` | `crate::predicates::PropositionalConjunction` | The predicates which are part of the nogood. |
| `is_learned` | `bool` | Indicates whether the nogood is a learned nogood or not. |
| `lbd` | `u32` | The LBD score of the nogood; this is an indication of how "good" the nogood is. |
| `is_protected` | `bool` | If a nogood is protected then it is not considered for removal for a single iteration. |
| `is_deleted` | `bool` | Whether the nogood has been marked as deleted; this means that it can be replaced by<br>another nogood in the future. |
| `block_bumps` | `bool` | Whether to not allow the nogood to have their activity bumped. |
| `activity` | `f32` | The activity score of the nogood. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new_learned_nogood(predicates: PropositionalConjunction, lbd: u32) -> Self { /* ... */ }
  ```

- ```rust
  pub(crate) fn new_permanent_nogood(predicates: PropositionalConjunction) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Default**
  - ```rust
    fn default() -> Nogood { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Freeze**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> Nogood { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

## Module `nogood_id`

```rust
pub(in ::propagators::nogoods) mod nogood_id { /* ... */ }
```

### Types

#### Struct `NogoodId`

```rust
pub(crate) struct NogoodId {
    pub(crate) id: u32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `id` | `u32` |  |

##### Implementations

###### Trait Implementations

- **StructuralPartialEq**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **StorageKey**
  - ```rust
    fn index(self: &Self) -> usize { /* ... */ }
    ```

  - ```rust
    fn create_from_index(index: usize) -> Self { /* ... */ }
    ```

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> NogoodId { /* ... */ }
    ```

- **IntoEither**
- **Default**
  - ```rust
    fn default() -> NogoodId { /* ... */ }
    ```

- **Copy**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &NogoodId) -> bool { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

## Module `nogood_propagator`

```rust
pub(in ::propagators::nogoods) mod nogood_propagator { /* ... */ }
```

### Types

#### Struct `NogoodPropagator`

A propagator which propagates nogoods (i.e. a list of [`Predicate`]s which cannot all be true
at the same time).

It should be noted that this propagator is notified about each event which occurs in the solver
(since the propagator does not know which IDs will be present in its learnt clauses).

The idea for propagation is the two-watcher scheme; this is achieved by internally keeping
track of watch lists.

```rust
pub(crate) struct NogoodPropagator {
    pub(in ::propagators::nogoods::nogood_propagator) nogoods: crate::containers::KeyedVec<super::NogoodId, crate::propagators::nogoods::Nogood>,
    pub(in ::propagators::nogoods::nogood_propagator) permanent_nogoods: Vec<super::NogoodId>,
    pub(in ::propagators::nogoods::nogood_propagator) learned_nogood_ids: LearnedNogoodIds,
    pub(in ::propagators::nogoods::nogood_propagator) delete_ids: Vec<super::NogoodId>,
    pub(in ::propagators::nogoods::nogood_propagator) last_index_on_trail: usize,
    pub(in ::propagators::nogoods::nogood_propagator) watch_lists: crate::containers::KeyedVec<crate::engine::variables::DomainId, super::NogoodWatchList>,
    pub(in ::propagators::nogoods::nogood_propagator) enqueued_updates: crate::engine::EventSink,
    pub(in ::propagators::nogoods::nogood_propagator) lbd_helper: literal_block_distance::Lbd,
    pub(in ::propagators::nogoods::nogood_propagator) parameters: super::LearningOptions,
    pub(in ::propagators::nogoods::nogood_propagator) bumped_nogoods: Vec<super::NogoodId>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `nogoods` | `crate::containers::KeyedVec<super::NogoodId, crate::propagators::nogoods::Nogood>` | The list of currently stored nogoods |
| `permanent_nogoods` | `Vec<super::NogoodId>` | Nogoods which are permanently present |
| `learned_nogood_ids` | `LearnedNogoodIds` | The ids of the nogoods sorted based on whether they have a "low" LBD score or a "high" LBD<br>score. |
| `delete_ids` | `Vec<super::NogoodId>` | Ids which have been deleted and can now be re-used |
| `last_index_on_trail` | `usize` | The trail index is used to determine the domains of the variables since last time. |
| `watch_lists` | `crate::containers::KeyedVec<crate::engine::variables::DomainId, super::NogoodWatchList>` | Watch lists for the nogood propagator. |
| `enqueued_updates` | `crate::engine::EventSink` | Keep track of the events which the propagator has been notified of. |
| `lbd_helper` | `literal_block_distance::Lbd` | A helper for calculating the LBD for the nogoods. |
| `parameters` | `super::LearningOptions` | The parameters which influence the learning of the propagator and aspects such as clause<br>management |
| `bumped_nogoods` | `Vec<super::NogoodId>` | The nogoods which have been bumped. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn with_options(parameters: LearningOptions) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn is_nogood_propagating(self: &Self, context: PropagationContext<''_>, reason_store: &ReasonStore, id: NogoodId) -> bool { /* ... */ }
  ```
  Determines whether the nogood (pointed to by `id`) is propagating using the following

- ```rust
  pub(crate) fn add_asserting_nogood(self: &mut Self, nogood: Vec<Predicate>, context: &mut PropagationContextMut<''_>, statistics: &mut SolverStatistics) { /* ... */ }
  ```
  Adds a nogood which has been learned during search.

- ```rust
  pub(crate) fn add_nogood(self: &mut Self, nogood: Vec<Predicate>, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Adds a nogood to the propagator as a permanent nogood and sets the internal state to be

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn add_permanent_nogood(self: &mut Self, nogood: Vec<Predicate>, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```
  Adds a nogood which cannot be deleted by clause management.

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn add_watcher(watch_lists: &mut KeyedVec<DomainId, NogoodWatchList>, predicate: Predicate, nogood_id: NogoodId) { /* ... */ }
  ```
  Adds a watcher to the predicate in the provided nogood with the provided [`NogoodId`].

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn remove_nogood_from_watch_list(watch_lists: &mut KeyedVec<DomainId, NogoodWatchList>, watching_predicate: Predicate, id: NogoodId) { /* ... */ }
  ```
  Removes the noogd from the watch list

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn clean_up_learned_nogoods_if_needed(self: &mut Self, context: PropagationContext<''_>, reason_store: &ReasonStore) { /* ... */ }
  ```
  Removes nogoods if there are too many nogoods with a "high" LBD

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn promote_high_lbd_nogoods(self: &mut Self) { /* ... */ }
  ```
  Goes through all of the "high" LBD nogoods and promotes nogoods which have been updated to

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn remove_high_lbd_nogoods(self: &mut Self, context: PropagationContext<''_>, reason_store: &ReasonStore) { /* ... */ }
  ```
  Removes high LBD nogoods from the internal structures.

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn sort_high_lbd_nogoods_by_quality_better_first(self: &mut Self) { /* ... */ }
  ```
  Orders the `high_lbd` nogoods in such a way that the 'better' nogoods are in front.

- ```rust
  pub(crate) fn decay_nogood_activities(self: &mut Self) { /* ... */ }
  ```
  Decays the activity bump increment by

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn preprocess_nogood(nogood: &mut Vec<Predicate>, context: &mut PropagationContextMut<''_>) { /* ... */ }
  ```
  Does simple preprocessing, modifying the input nogood by:

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn debug_propagate_nogood_from_scratch(self: &Self, nogood_id: NogoodId, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::nogoods::nogood_propagator) fn debug_is_properly_watched(self: &Self) -> bool { /* ... */ }
  ```
  Checks for each nogood whether the first two predicates in the nogood are being watched

###### Trait Implementations

- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **UnwindSafe**
- **RefUnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Propagator**
  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
    ```

  - ```rust
    fn notify(self: &mut Self, _context: StatefulPropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn lazy_explanation(self: &mut Self, code: u64, context: ExplanationContext<''_>) -> &[Predicate] { /* ... */ }
    ```
    Returns the slice representing a conjunction of predicates that explain the propagation

  - ```rust
    fn initialise_at_root(self: &mut Self, _context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> NogoodPropagator { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> NogoodPropagator { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Sync**
#### Struct `LearnedNogoodIds`

A struct which keeps track of which nogoods are considered "high" LBD and which nogoods are
considered "low" LBD.

```rust
pub(in ::propagators::nogoods::nogood_propagator) struct LearnedNogoodIds {
    pub(in ::propagators::nogoods::nogood_propagator) low_lbd: Vec<super::NogoodId>,
    pub(in ::propagators::nogoods::nogood_propagator) high_lbd: Vec<super::NogoodId>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `low_lbd` | `Vec<super::NogoodId>` |  |
| `high_lbd` | `Vec<super::NogoodId>` |  |

##### Implementations

###### Trait Implementations

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> LearnedNogoodIds { /* ... */ }
    ```

- **Unpin**
- **Send**
- **Default**
  - ```rust
    fn default() -> LearnedNogoodIds { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

## Module `nogood_watching`

```rust
pub(in ::propagators::nogoods) mod nogood_watching { /* ... */ }
```

### Types

#### Struct `NogoodWatchList`

The watch list is specific to a domain id.

```rust
pub(crate) struct NogoodWatchList {
    pub(in ::propagators::nogoods::nogood_watching) lower_bound: Vec<NogoodWatcher>,
    pub(in ::propagators::nogoods::nogood_watching) upper_bound: Vec<NogoodWatcher>,
    pub(in ::propagators::nogoods::nogood_watching) hole: Vec<NogoodWatcher>,
    pub(in ::propagators::nogoods::nogood_watching) equals: Vec<NogoodWatcher>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `lower_bound` | `Vec<NogoodWatcher>` | Nogoods with a watched predicate [x >= k] |
| `upper_bound` | `Vec<NogoodWatcher>` | Nogoods with a watched predicate [x <= k] |
| `hole` | `Vec<NogoodWatcher>` | Nogoods with a watched predicate [x != k] |
| `equals` | `Vec<NogoodWatcher>` | Nogoods with a watched predicate [x == k] |

##### Implementations

###### Methods

- ```rust
  pub(in ::propagators::nogoods::nogood_watching) fn find_and_remove_watcher(watch_list: &mut Vec<NogoodWatcher>, id: NogoodId, value: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_lower_bound_watchers(self: &Self) -> impl Iterator<Item = &NogoodWatcher> { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove_lower_bound_watcher(self: &mut Self, nogood_id: NogoodId, value: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn truncate_lower_bound_watchers(self: &mut Self, new_len: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_lower_bound_watcher_to_other_watcher(self: &mut Self, index: usize, other_index: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_lower_bound_watcher_at_index(self: &Self, index: usize) -> &NogoodWatcher { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_lower_bound_watcher(self: &mut Self, nogood_id: NogoodId, right_hand_side: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn num_lower_bound_watchers(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_upper_bound_watchers(self: &Self) -> impl Iterator<Item = &NogoodWatcher> { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove_upper_bound_watcher(self: &mut Self, nogood_id: NogoodId, value: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn truncate_upper_bound_watchers(self: &mut Self, new_len: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_upper_bound_watcher_to_other_watcher(self: &mut Self, index: usize, other_index: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_upper_bound_watcher_at_index(self: &Self, index: usize) -> &NogoodWatcher { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_upper_bound_watcher(self: &mut Self, nogood_id: NogoodId, right_hand_side: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn num_upper_bound_watchers(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_inequality_watchers(self: &Self) -> impl Iterator<Item = &NogoodWatcher> { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove_inequality_watcher(self: &mut Self, nogood_id: NogoodId, value: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn truncate_inequality_watchers(self: &mut Self, new_len: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_inequality_watcher_to_other_watcher(self: &mut Self, index: usize, other_index: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_inequality_watcher_at_index(self: &Self, index: usize) -> &NogoodWatcher { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_inequality_watcher(self: &mut Self, nogood_id: NogoodId, right_hand_side: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn num_inequality_watchers(self: &Self) -> usize { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_right_hand_side_of_inequality_watcher_at_index(self: &mut Self, index: usize, new_rhs: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn iter_equality_watchers(self: &Self) -> impl Iterator<Item = &NogoodWatcher> { /* ... */ }
  ```

- ```rust
  pub(crate) fn remove_equality_watcher(self: &mut Self, nogood_id: NogoodId, value: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn truncate_equality_watchers(self: &mut Self, new_len: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn set_equality_watcher_to_other_watcher(self: &mut Self, index: usize, other_index: usize) { /* ... */ }
  ```

- ```rust
  pub(crate) fn get_equality_watcher_at_index(self: &Self, index: usize) -> &NogoodWatcher { /* ... */ }
  ```

- ```rust
  pub(crate) fn add_equality_watcher(self: &mut Self, nogood_id: NogoodId, right_hand_side: i32) { /* ... */ }
  ```

- ```rust
  pub(crate) fn num_equality_watchers(self: &Self) -> usize { /* ... */ }
  ```

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> NogoodWatchList { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> NogoodWatchList { /* ... */ }
    ```

- **Sync**
- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **IntoEither**
- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

#### Struct `NogoodWatcher`

The watcher is with respect to a specific domain id and predicate type.

```rust
pub(crate) struct NogoodWatcher {
    pub(crate) right_hand_side: i32,
    pub(crate) nogood_id: super::NogoodId,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `right_hand_side` | `i32` | This field represents the right-hand side of the predicate present in the nogood.<br><br>It is used as an indicator to whether the nogood should be inspected. |
| `nogood_id` | `super::NogoodId` |  |

##### Implementations

###### Trait Implementations

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Copy**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> NogoodWatcher { /* ... */ }
    ```

- **Unpin**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Freeze**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> NogoodWatcher { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

### Re-exports

#### Re-export `learning_options::*`

```rust
pub use learning_options::*;
```

## Module `reified_propagator`

```rust
pub(in ::propagators) mod reified_propagator { /* ... */ }
```

### Types

#### Struct `ReifiedPropagator`

Propagator for the constraint `r -> p`, where `r` is a Boolean literal and `p` is an arbitrary
propagator.

When a propagator is reified, it will only propagate whenever `r` is set to true. However, if
the propagator implements [`Propagator::detect_inconsistency`], the result of that method may
be used to propagate `r` to false. If that method is not implemented, `r` will never be
propagated to false.

```rust
pub(crate) struct ReifiedPropagator<WrappedPropagator> {
    pub(in ::propagators::reified_propagator) propagator: WrappedPropagator,
    pub(in ::propagators::reified_propagator) reification_literal: crate::variables::Literal,
    pub(in ::propagators::reified_propagator) inconsistency: Option<crate::predicates::PropositionalConjunction>,
    pub(in ::propagators::reified_propagator) name: String,
    pub(in ::propagators::reified_propagator) reification_literal_id: local_id::LocalId,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `propagator` | `WrappedPropagator` |  |
| `reification_literal` | `crate::variables::Literal` |  |
| `inconsistency` | `Option<crate::predicates::PropositionalConjunction>` | An inconsistency that is identified by `propagator`. |
| `name` | `String` | The formatted name of the propagator. |
| `reification_literal_id` | `local_id::LocalId` | The `LocalId` of the reification literal. Is guaranteed to be a larger ID than any of the<br>registered ids of the wrapped propagator. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(propagator: WrappedPropagator, reification_literal: Literal) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::reified_propagator) fn map_propagation_status(self: &Self, status: Result<(), Inconsistency>) -> Result<(), Inconsistency> { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::reified_propagator) fn propagate_reification(self: &Self, context: &mut PropagationContextMut<''_>) -> Result<(), Inconsistency>
where
    Prop: Propagator { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::reified_propagator) fn find_inconsistency(self: &mut Self, context: StatefulPropagationContext<''_>) -> bool { /* ... */ }
  ```

- ```rust
  pub(in ::propagators::reified_propagator) fn filter_enqueue_decision(self: &mut Self, context: StatefulPropagationContext<''_>, decision: EnqueueDecision) -> EnqueueDecision { /* ... */ }
  ```

###### Trait Implementations

- **Propagator**
  - ```rust
    fn notify(self: &mut Self, context: StatefulPropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision { /* ... */ }
    ```

  - ```rust
    fn notify_backtrack(self: &mut Self, context: PropagationContext<''_>, local_id: LocalId, event: OpaqueDomainEvent) { /* ... */ }
    ```

  - ```rust
    fn initialise_at_root(self: &mut Self, context: &mut PropagatorInitialisationContext<''_>) -> Result<(), PropositionalConjunction> { /* ... */ }
    ```

  - ```rust
    fn priority(self: &Self) -> u32 { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, context: PropagationContext<''_>) { /* ... */ }
    ```

  - ```rust
    fn propagate(self: &mut Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

  - ```rust
    fn name(self: &Self) -> &str { /* ... */ }
    ```

  - ```rust
    fn debug_propagate_from_scratch(self: &Self, context: PropagationContextMut<''_>) -> Result<(), Inconsistency> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ReifiedPropagator<WrappedPropagator> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

### Re-exports

#### Re-export `CumulativeExplanationType`

```rust
pub use cumulative::CumulativeExplanationType;
```

#### Re-export `CumulativeOptions`

```rust
pub use cumulative::CumulativeOptions;
```

#### Re-export `CumulativePropagationMethod`

```rust
pub use cumulative::CumulativePropagationMethod;
```

## Module `pumpkin_asserts`

```rust
pub(crate) mod pumpkin_asserts { /* ... */ }
```

### Constants and Statics

#### Constant `PUMPKIN_ASSERT_LEVEL_DEFINITION`

**Attributes:**

- `#[<cfg>(all(not(test), not(feature = "debug-checks")))]`

```rust
pub const PUMPKIN_ASSERT_LEVEL_DEFINITION: u8 = PUMPKIN_ASSERT_SIMPLE;
```

#### Constant `PUMPKIN_ASSERT_SIMPLE`

```rust
pub const PUMPKIN_ASSERT_SIMPLE: u8 = 1;
```

#### Constant `PUMPKIN_ASSERT_MODERATE`

```rust
pub const PUMPKIN_ASSERT_MODERATE: u8 = 2;
```

#### Constant `PUMPKIN_ASSERT_ADVANCED`

```rust
pub const PUMPKIN_ASSERT_ADVANCED: u8 = 3;
```

#### Constant `PUMPKIN_ASSERT_EXTREME`

```rust
pub const PUMPKIN_ASSERT_EXTREME: u8 = 4;
```

## Module `variable_names`

```rust
pub(crate) mod variable_names { /* ... */ }
```

### Types

#### Struct `VariableNames`

```rust
pub(crate) struct VariableNames {
    pub(in ::variable_names) integers: std::collections::HashMap<crate::engine::variables::DomainId, String, fnv::FnvBuildHasher>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `integers` | `std::collections::HashMap<crate::engine::variables::DomainId, String, fnv::FnvBuildHasher>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn get_int_name(self: &Self, domain_id: DomainId) -> Option<&str> { /* ... */ }
  ```
  Get the name associated with a domain id.

- ```rust
  pub(crate) fn add_integer(self: &mut Self, integer: DomainId, name: String) { /* ... */ }
  ```
  Add a name to the integer variable. This will override existing the name if it

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> VariableNames { /* ... */ }
    ```

- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

## Module `branching`

Contains structures and traits to define the decision making procedure of the [`Solver`].

In general, it provides 3 traits:
- The [`Brancher`] which defines how a branching procedure (which selects an unfixed variable and splits the domain in some way, see [Section 4.3.1 of \[1\]](http://www.cse.unsw.com.au/~tw/brwhkr08.pdf)
  for more information) should operate; the main method of this trait is the [`Brancher::next_decision`] method. An example implementation of this trait is the [`IndependentVariableValueBrancher`].
- The [`VariableSelector`] which defines the method required of a variable selector (including
  the hooks into the solver); the main method of this trait is the
  [`VariableSelector::select_variable`] method. An example implementation of this trait is the
  [`AntiFirstFail`] strategy.
- The [`ValueSelector`] which defines the method required of a value selector (including the
  hooks into the solver); the main method of this trait is the [`ValueSelector::select_value`]
  method.

A [`Brancher`] is expected to be passed to [`Solver::satisfy`], and [`Solver::optimise`]:
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::variables::Literal;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::SatisfactionResult;
# use crate::pumpkin_solver::results::ProblemSolution;
let mut solver = Solver::default();

let variables = vec![solver.new_literal()];

let mut termination = Indefinite;
let mut brancher = solver.default_brancher();
let result = solver.satisfy(&mut brancher, &mut termination);
if let SatisfactionResult::Satisfiable(solution) = result {
    // Getting the value of the literal in the solution should not panic
    variables.into_iter().for_each(|variable| {
        solver.get_literal_value(variable);
    });
} else {
    panic!("Solving should have returned satsifiable")
}
```


A default implementation of a [`Brancher`]
is provided using the method
[`Solver::default_brancher`].
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::variables::Literal;
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::results::SatisfactionResult;
# use crate::pumpkin_solver::results::ProblemSolution;
let mut solver = Solver::default();

let literals = vec![solver.new_literal()];

let mut termination = Indefinite;
let mut brancher = solver.default_brancher();
let result = solver.satisfy(&mut brancher, &mut termination);
if let SatisfactionResult::Satisfiable(solution) = result {
    // Getting the value of the literal in the solution should not panic
    literals.into_iter().for_each(|literal| {
        solution.get_literal_value(literal);
    })
} else {
    panic!("Solving should have returned satsifiable")
}
```

\[1\] F. Rossi, P. Van Beek, and T. Walsh, Handbook of constraint programming. Elsevier, 2006.

```rust
pub mod branching { /* ... */ }
```

### Modules

## Module `brancher`

```rust
pub(in ::branching) mod brancher { /* ... */ }
```

### Types

#### Enum `BrancherEvent`

The events which can occur for a [`Brancher`]. Used for returning which events are relevant in
[`Brancher::subscribe_to_events`], [`VariableSelector::subscribe_to_events`],
and [`ValueSelector::subscribe_to_events`].

```rust
pub enum BrancherEvent {
    Conflict,
    Backtrack,
    Solution,
    UnassignInteger,
    AppearanceInConflictPredicate,
    Restart,
    Synchronise,
}
```

##### Variants

###### `Conflict`

Event for when a conflict is detected

###### `Backtrack`

Event for when a backtrack is performed

###### `Solution`

Event for when a solution has been found

###### `UnassignInteger`

Event for when an integer variable has become unassigned

###### `AppearanceInConflictPredicate`

Event for when a predicate appears during conflict analysis

###### `Restart`

Event for when a restart occurs

###### `Synchronise`

Event which is called with the new state after a backtrack has occurred

##### Implementations

###### Trait Implementations

- **Hash**
  - ```rust
    fn hash<__H: $crate::hash::Hasher>(self: &Self, state: &mut __H) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Freeze**
- **Send**
- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **StructuralPartialEq**
- **Eq**
- **Enum**
  - ```rust
    fn from_usize(value: usize) -> Self { /* ... */ }
    ```

  - ```rust
    fn into_usize(self: Self) -> usize { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &BrancherEvent) -> bool { /* ... */ }
    ```

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **EnumArray**
- **IntoEither**
- **Sync**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> BrancherEvent { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Copy**
### Traits

#### Trait `Brancher`

A trait for definining a branching strategy (oftentimes utilising a [`VariableSelector`] and a
[`ValueSelector`]).

In general, implementations of this trait define how the search of the solver proceeds (i.e. it
controls how the solver determines which part of the search space to explore). It is required
that the resulting decision creates a smaller domain for at least 1 of the variables (and more
domains can be affected due to subsequent inference). See [`branching`] for
example usages.

If the [`Brancher`] (or any component thereof) is implemented incorrectly then the
behaviour of the solver is undefined.

```rust
pub trait Brancher {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `next_decision`: Returns the next decision concerning a single variable and value; it returns the
- `subscribe_to_events`: Indicates which [`BrancherEvent`] are relevant for this particular [`Brancher`].

##### Provided Methods

- ```rust
  fn log_statistics(self: &Self, _statistic_logger: StatisticLogger) { /* ... */ }
  ```
  Logs statistics of the brancher using the provided [`StatisticLogger`].

- ```rust
  fn on_conflict(self: &mut Self) { /* ... */ }
  ```
  A function which is called after a conflict has been found and processed but (currently)

- ```rust
  fn on_backtrack(self: &mut Self) { /* ... */ }
  ```
  A function which is called whenever a backtrack occurs in the [`Solver`].

- ```rust
  fn on_solution(self: &mut Self, _solution: SolutionReference<''_>) { /* ... */ }
  ```
  This method is called when a solution is found; this will either be called when a new

- ```rust
  fn on_unassign_integer(self: &mut Self, _variable: DomainId, _value: i32) { /* ... */ }
  ```
  A function which is called after a [`DomainId`] is unassigned during backtracking (i.e. when

- ```rust
  fn on_appearance_in_conflict_predicate(self: &mut Self, _predicate: Predicate) { /* ... */ }
  ```
  A function which is called when a [`Predicate`] appears in a conflict during conflict

- ```rust
  fn on_restart(self: &mut Self) { /* ... */ }
  ```
  This method is called whenever a restart is performed.

- ```rust
  fn synchronise(self: &mut Self, _assignments: &Assignments) { /* ... */ }
  ```
  Called after backtracking.

- ```rust
  fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
  ```
  This method returns whether a restart is *currently* pointless for the [`Brancher`].

##### Implementations

This trait is implemented for the following types:

- `AlternatingBrancher<OtherBrancher>` with <OtherBrancher: Brancher>
- `AutonomousSearch<BackupBrancher>` with <BackupBrancher: Brancher>
- `DynamicBrancher`
- `IndependentVariableValueBrancher<Var, VariableSelect, ValueSelect>` with <Var, VariableSelect, ValueSelect>

## Module `branchers`

Provides several implementations of [`Brancher`]s.

```rust
pub mod branchers { /* ... */ }
```

### Modules

## Module `alternating_brancher`

A [`Brancher`] which alternates between the [`DefaultBrancher`] and another [`Brancher`] based
on the strategy specified in [`AlternatingStrategy`].

```rust
pub mod alternating_brancher { /* ... */ }
```

### Types

#### Enum `AlternatingStrategy`

Determines which alternation strategy is used by the [`AlternatingBrancher`].

Currently we allow switching every time a solution is found
([`AlternatingStrategy::EverySolution`]), after every other solution
([`AlternatingStrategy::EveryOtherSolution`]), switching to [`DefaultBrancher`] after the first
solution is found and switching strategy upon restart.

```rust
pub enum AlternatingStrategy {
    EverySolution,
    EveryOtherSolution,
    SwitchToDefaultAfterFirstSolution,
    EveryRestart,
}
```

##### Variants

###### `EverySolution`

Specifies that the [`AlternatingBrancher`] should switch between [`DefaultBrancher`] and
the provided brancher every solution.

###### `EveryOtherSolution`

Specifies that the [`AlternatingBrancher`] should switch between [`DefaultBrancher`] and
the provided brancher every other solution.

###### `SwitchToDefaultAfterFirstSolution`

Specifies that the [`AlternatingBrancher`] should switch to [`DefaultBrancher`] for the
rest of the search after finding a single solution with the provided strategy.

###### `EveryRestart`

Specifies that the [`AlternatingBrancher`] should switch between [`DefaultBrancher`] and
the provided brancher every restart.

##### Implementations

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Copy**
- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> AlternatingStrategy { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &AlternatingStrategy) -> bool { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Sync**
- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **StructuralPartialEq**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Unpin**
- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
#### Struct `AlternatingBrancher`

A [`Brancher`] which switches between its provided brancher and [`DefaultBrancher`] based on the
provided [`AlternatingStrategy`].

Note that the [`DefaultBrancher`] is informed of every
conflict and unassignment even if it is not currently utilised as [`Brancher`].

Note that this brancher starts out by using the provided [`Brancher`] and then switches based on
the [`AlternatingStrategy`].

```rust
pub struct AlternatingBrancher<OtherBrancher> {
    pub(in ::branching::branchers::alternating_brancher) even_number_of_solutions: bool,
    pub(in ::branching::branchers::alternating_brancher) is_using_default_brancher: bool,
    pub(in ::branching::branchers::alternating_brancher) other_brancher: OtherBrancher,
    pub(in ::branching::branchers::alternating_brancher) default_brancher: crate::DefaultBrancher,
    pub(in ::branching::branchers::alternating_brancher) strategy: AlternatingStrategy,
    pub(in ::branching::branchers::alternating_brancher) has_considered_restart: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `even_number_of_solutions` | `bool` |  |
| `is_using_default_brancher` | `bool` | Whether the [`Brancher`] is currently using the [`DefaultBrancher`] or not |
| `other_brancher` | `OtherBrancher` | The other [`Brancher`] which is used when<br>[`AlternatingBrancher::is_using_default_brancher`] is false. |
| `default_brancher` | `crate::DefaultBrancher` | The instance of [`DefaultBrancher`] which is used when<br>[`AlternatingBrancher::is_using_default_brancher`] is true. |
| `strategy` | `AlternatingStrategy` | The strategy used to determine when to switch between the two branchers. |
| `has_considered_restart` | `bool` | Indicates that the [`AlternatingBrancher`] has considered a restart; note that this<br>variable is only used in the context of [`ÀlternatingStrategy::EveryRestart`]. |

##### Implementations

###### Methods

- ```rust
  pub fn new(solver: &Solver, other_brancher: OtherBrancher, strategy: AlternatingStrategy) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::branching::branchers::alternating_brancher) fn toggle_brancher(self: &mut Self) { /* ... */ }
  ```
  Toggles which [`Brancher`] is used.

- ```rust
  pub(in ::branching::branchers::alternating_brancher) fn will_always_use_default(self: &Self) -> bool { /* ... */ }
  ```
  Returns true if only the default strategy is used from now on and false otherwise.

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Brancher**
  - ```rust
    fn next_decision(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Predicate> { /* ... */ }
    ```

  - ```rust
    fn log_statistics(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

  - ```rust
    fn on_appearance_in_conflict_predicate(self: &mut Self, predicate: Predicate) { /* ... */ }
    ```

  - ```rust
    fn on_conflict(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_solution(self: &mut Self, solution: SolutionReference<''_>) { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, value: i32) { /* ... */ }
    ```

  - ```rust
    fn on_restart(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn on_backtrack(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, assignments: &Assignments) { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Unpin**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `autonomous_search`

```rust
pub mod autonomous_search { /* ... */ }
```

### Types

#### Struct `AutonomousSearch`

A [`Brancher`] that combines [VSIDS \[1\]](https://dl.acm.org/doi/pdf/10.1145/378239.379017)
and [Solution-based phase saving \[2\]](https://people.eng.unimelb.edu.au/pstuckey/papers/lns-restarts.pdf).

There are three components:
1. Predicate selection
2. Truth value assignment
3. Backup Selection

# Predicate selection
The VSIDS algorithm is an adaptation for the CP case. It determines which
[`Predicate`] should be branched on based on how often it appears in conflicts.

Intuitively, the more often a [`Predicate`] appears in *recent* conflicts, the more "important"
it is during the search process. VSIDS is originally from the SAT field (see \[1\]) but we
adapted it for constraint programming by considering [`Predicate`]s from recent conflicts
directly rather than Boolean variables.

# Truth value assignment
The truth value for the [`Predicate`] is selected to be consistent with the
best solution known so far. In this way, the search is directed around this existing solution.

In case where there is no known solution, then the predicate is assigned to true. This resembles
a fail-first strategy with the idea that the given predicate was encountered in conflicts, so
assigning it to true may cause another conflict soon.

# Backup selection
VSIDS relies on [`Predicate`]s appearing in conflicts to discover which [`Predicate`]s are
"important". However, it could be the case that all [`Predicate`]s which VSIDS has discovered
are already assigned.

In this case, [`AutonomousSearch`] defaults either to the backup described in
[`DefaultBrancher`] (when created using [`AutonomousSearch::default_over_all_variables`]) or it
defaults to the [`Brancher`] provided to [`AutonomousSearch::new`].

# Bibliography
\[1\] M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang, and S. Malik, ‘Chaff: Engineering an
efficient SAT solver’, in Proceedings of the 38th annual Design Automation Conference, 2001.

\[2\] E. Demirović, G. Chu, and P. J. Stuckey, ‘Solution-based phase saving for CP: A
value-selection heuristic to simulate local search behavior in complete solvers’, in the
proceedings of the Principles and Practice of Constraint Programming (CP 2018).

```rust
pub struct AutonomousSearch<BackupBrancher> {
    pub(in ::branching::branchers::autonomous_search) predicate_id_info: predicate_id_generator::PredicateIdGenerator,
    pub(in ::branching::branchers::autonomous_search) heap: crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, f64>,
    pub(in ::branching::branchers::autonomous_search) dormant_predicates: Vec<crate::engine::predicates::predicate::Predicate>,
    pub(in ::branching::branchers::autonomous_search) increment: f64,
    pub(in ::branching::branchers::autonomous_search) max_threshold: f64,
    pub(in ::branching::branchers::autonomous_search) decay_factor: f64,
    pub(in ::branching::branchers::autonomous_search) best_known_solution: Option<crate::results::Solution>,
    pub(in ::branching::branchers::autonomous_search) backup_brancher: BackupBrancher,
    pub(in ::branching::branchers::autonomous_search) statistics: AutonomousSearchStatistics,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `predicate_id_info` | `predicate_id_generator::PredicateIdGenerator` | Predicates are mapped to ids. This is used internally in the heap. |
| `heap` | `crate::containers::KeyValueHeap<predicate_id_generator::PredicateId, f64>` | Stores the activities for a predicate, represented with its id. |
| `dormant_predicates` | `Vec<crate::engine::predicates::predicate::Predicate>` | After popping predicates off the heap that current have a truth value, the predicates are<br>labelled as dormant because they do not contribute to VSIDS at the moment. When<br>backtracking, dormant predicates are examined and readded to the heap. Dormant predicates<br>with low activities are removed. |
| `increment` | `f64` | How much the activity of a predicate is increased when it appears in a conflict.<br>This value changes during search (see [`Vsids::decay_activities`]). |
| `max_threshold` | `f64` | The maximum allowed [`Vsids`] value, if this value is reached then all of the values are<br>divided by this value. The increment is constant. |
| `decay_factor` | `f64` | Whenever a conflict is found, the [`Vsids::increment`] is multiplied by<br>1 / [`Vsids::decay_factor`] (this is synonymous with increasing the<br>[`Vsids::increment`] since 0 <= [`Vsids::decay_factor`] <= 1).<br>The decay factor is constant. |
| `best_known_solution` | `Option<crate::results::Solution>` | Contains the best-known solution or [`None`] if no solution has been found. |
| `backup_brancher` | `BackupBrancher` | If the heap does not contain any more unfixed predicates then this backup_brancher will be<br>used instead. |
| `statistics` | `AutonomousSearchStatistics` |  |

##### Implementations

###### Methods

- ```rust
  pub fn default_over_all_variables(assignments: &Assignments) -> DefaultBrancher { /* ... */ }
  ```
  Creates a new instance with default values for

- ```rust
  pub fn new(backup_brancher: BackupSelector) -> Self { /* ... */ }
  ```
  Creates a new instance with default values for

- ```rust
  pub(in ::branching::branchers::autonomous_search) fn resize_heap(self: &mut Self, id: PredicateId) { /* ... */ }
  ```
  Resizes the heap to accommodate for the id.

- ```rust
  pub(in ::branching::branchers::autonomous_search) fn bump_activity(self: &mut Self, predicate: Predicate) { /* ... */ }
  ```
  Bumps the activity of a predicate by [`Vsids::increment`].

- ```rust
  pub(in ::branching::branchers::autonomous_search) fn decay_activities(self: &mut Self) { /* ... */ }
  ```
  Decays the activities (i.e. increases the [`Vsids::increment`] by multiplying it

- ```rust
  pub(in ::branching::branchers::autonomous_search) fn next_candidate_predicate(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Predicate> { /* ... */ }
  ```

- ```rust
  pub(in ::branching::branchers::autonomous_search) fn determine_polarity(self: &Self, predicate: Predicate) -> Predicate { /* ... */ }
  ```
  Determines whether the provided [`Predicate`] should be returned as is or whether its

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Brancher**
  - ```rust
    fn next_decision(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Predicate> { /* ... */ }
    ```

  - ```rust
    fn log_statistics(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

  - ```rust
    fn on_backtrack(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, assignments: &Assignments) { /* ... */ }
    ```
    Restores dormant predicates after backtracking.

  - ```rust
    fn on_conflict(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_solution(self: &mut Self, solution: SolutionReference<''_>) { /* ... */ }
    ```

  - ```rust
    fn on_appearance_in_conflict_predicate(self: &mut Self, predicate: Predicate) { /* ... */ }
    ```

  - ```rust
    fn on_restart(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, value: i32) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

#### Struct `AutonomousSearchStatistics`

```rust
pub(crate) struct AutonomousSearchStatistics {
    pub(crate) num_backup_called: usize,
    pub(crate) num_predicates_removed: usize,
    pub(crate) num_calls: usize,
    pub(crate) num_predicates_added: usize,
    pub(crate) average_size_of_heap: cumulative_moving_average::CumulativeMovingAverage<usize>,
    pub(crate) num_assigned_predicates_encountered: usize,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `num_backup_called` | `usize` |  |
| `num_predicates_removed` | `usize` |  |
| `num_calls` | `usize` |  |
| `num_predicates_added` | `usize` |  |
| `average_size_of_heap` | `cumulative_moving_average::CumulativeMovingAverage<usize>` |  |
| `num_assigned_predicates_encountered` | `usize` |  |

##### Implementations

###### Trait Implementations

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> AutonomousSearchStatistics { /* ... */ }
    ```

- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: $crate::statistics::StatisticLogger) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Copy**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Unpin**
- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **RefUnwindSafe**
- **Default**
  - ```rust
    fn default() -> AutonomousSearchStatistics { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

### Constants and Statics

#### Constant `DEFAULT_VSIDS_INCREMENT`

```rust
pub(in ::branching::branchers::autonomous_search) const DEFAULT_VSIDS_INCREMENT: f64 = 1.0;
```

#### Constant `DEFAULT_VSIDS_MAX_THRESHOLD`

```rust
pub(in ::branching::branchers::autonomous_search) const DEFAULT_VSIDS_MAX_THRESHOLD: f64 = 1e100;
```

#### Constant `DEFAULT_VSIDS_DECAY_FACTOR`

```rust
pub(in ::branching::branchers::autonomous_search) const DEFAULT_VSIDS_DECAY_FACTOR: f64 = 0.95;
```

#### Constant `DEFAULT_VSIDS_VALUE`

```rust
pub(in ::branching::branchers::autonomous_search) const DEFAULT_VSIDS_VALUE: f64 = 0.0;
```

## Module `dynamic_brancher`

A [`Brancher`] which sequentially applies a list of [`Brancher`]s until all of them can not find
another decision.

Note that this structure should be used if you want to use dynamic [`Brancher`]s but
require a [`Sized`] object (e.g. when a function takes as input `impl Brancher`).

```rust
pub mod dynamic_brancher { /* ... */ }
```

### Types

#### Struct `DynamicBrancher`

An implementation of a [`Brancher`] which takes a [`Vec`] of `Box<dyn Brancher>` and
sequentially applies [`Brancher::next_decision`] until all of them return [`None`].

For any other method in [`Brancher`] it will simply pass it along to all of the provided
`Box<dyn Brancher>`s. This structure should be used if you want to use dynamic [`Brancher`]s but
require a [`Sized`] object (e.g. when a function takes as input `impl Brancher`).

# Note
It is important that the methods [`DynamicBrancher::on_conflict`] and
[`DynamicBrancher::on_solution`] are called at the appropriate times as these methods ensure
that the index to the current brancher to try is reset. If these methods are not called at the
appropriate time then it will (likely) lead to incomplete solutions being returned!

```rust
pub struct DynamicBrancher {
    pub(in ::branching::branchers::dynamic_brancher) branchers: Vec<Box<dyn Brancher>>,
    pub(in ::branching::branchers::dynamic_brancher) brancher_index: usize,
    pub(in ::branching::branchers::dynamic_brancher) relevant_event_to_index: enum_map::EnumMap<crate::branching::brancher::BrancherEvent, Vec<usize>>,
    pub(in ::branching::branchers::dynamic_brancher) relevant_events: Vec<crate::branching::brancher::BrancherEvent>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `branchers` | `Vec<Box<dyn Brancher>>` |  |
| `brancher_index` | `usize` |  |
| `relevant_event_to_index` | `enum_map::EnumMap<crate::branching::brancher::BrancherEvent, Vec<usize>>` |  |
| `relevant_events` | `Vec<crate::branching::brancher::BrancherEvent>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(branchers: Vec<Box<dyn Brancher>>) -> Self { /* ... */ }
  ```
  Creates a new [`DynamicBrancher`] with the provided `branchers`. It will attempt to use the

- ```rust
  pub fn add_brancher(self: &mut Self, brancher: Box<dyn Brancher>) { /* ... */ }
  ```

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Unpin**
- **Brancher**
  - ```rust
    fn next_decision(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Predicate> { /* ... */ }
    ```

  - ```rust
    fn log_statistics(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

  - ```rust
    fn on_conflict(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_backtrack(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, value: i32) { /* ... */ }
    ```

  - ```rust
    fn on_appearance_in_conflict_predicate(self: &mut Self, predicate: Predicate) { /* ... */ }
    ```

  - ```rust
    fn on_solution(self: &mut Self, solution: SolutionReference<''_>) { /* ... */ }
    ```

  - ```rust
    fn on_restart(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn synchronise(self: &mut Self, assignments: &Assignments) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **RefUnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **Send**
## Module `independent_variable_value_brancher`

A [`Brancher`] which simply switches uses a single [`VariableSelector`] and a single
[`ValueSelector`].

```rust
pub mod independent_variable_value_brancher { /* ... */ }
```

### Types

#### Struct `IndependentVariableValueBrancher`

An implementation of a [`Brancher`] which simply uses a single
[`VariableSelector`] and a single [`ValueSelector`] independently of one another.

```rust
pub struct IndependentVariableValueBrancher<Var, VariableSelect, ValueSelect> {
    pub(crate) variable_selector: VariableSelect,
    pub(crate) value_selector: ValueSelect,
    pub(crate) variable_type: std::marker::PhantomData<Var>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variable_selector` | `VariableSelect` | The [`VariableSelector`] of the [`Brancher`], determines which (unfixed) variable to branch<br>next on. |
| `value_selector` | `ValueSelect` | The [`ValueSelector`] of the [`Brancher`] determines which value in the domain to branch<br>next on given a variable. |
| `variable_type` | `std::marker::PhantomData<Var>` | [`PhantomData`] to ensure that the variable type is bound to the<br>[`IndependentVariableValueBrancher`] |

##### Implementations

###### Methods

- ```rust
  pub fn new(var_selector: VariableSelect, val_selector: ValueSelect) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Brancher**
  - ```rust
    fn next_decision(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Predicate> { /* ... */ }
    ```
    First we select a variable

  - ```rust
    fn on_backtrack(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_conflict(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, value: i32) { /* ... */ }
    ```

  - ```rust
    fn on_appearance_in_conflict_predicate(self: &mut Self, predicate: Predicate) { /* ... */ }
    ```

  - ```rust
    fn on_solution(self: &mut Self, solution: SolutionReference<''_>) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Send**
- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

## Module `selection_context`

```rust
pub(in ::branching) mod selection_context { /* ... */ }
```

### Types

#### Struct `SelectionContext`

The context provided to the [`Brancher`],
it allows the retrieval of domain values of variables and access to methods from a [`Random`]
generator.

```rust
pub struct SelectionContext<''a> {
    pub(in ::branching::selection_context) assignments: &''a assignments::Assignments,
    pub(in ::branching::selection_context) random_generator: &''a mut dyn Random,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `assignments` | `&''a assignments::Assignments` |  |
| `random_generator` | `&''a mut dyn Random` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(assignments: &''a Assignments, rng: &''a mut dyn Random) -> Self { /* ... */ }
  ```

- ```rust
  pub fn are_all_variables_assigned(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub fn random(self: &mut Self) -> &mut dyn Random { /* ... */ }
  ```
  Returns a random generator which can be used to generate random values (see [`Random`] for

- ```rust
  pub fn get_size_of_domain<Var: IntegerVariable>(self: &Self, var: Var) -> i32 { /* ... */ }
  ```
  Returns the difference between the upper-bound and the lower-bound of the provided

- ```rust
  pub fn lower_bound<Var: IntegerVariable>(self: &Self, var: Var) -> i32 { /* ... */ }
  ```
  Returns the lower bound of the provided [`IntegerVariable`]

- ```rust
  pub fn upper_bound<Var: IntegerVariable>(self: &Self, var: Var) -> i32 { /* ... */ }
  ```
  Returns the upper bound of the provided [`IntegerVariable`]

- ```rust
  pub fn contains<Var: IntegerVariable>(self: &Self, var: Var, value: i32) -> bool { /* ... */ }
  ```
  Determines whether the provided value is in the domain of the provided [`IntegerVariable`]

- ```rust
  pub fn is_integer_fixed<Var: IntegerVariable>(self: &Self, var: Var) -> bool { /* ... */ }
  ```
  Determines whether the provided [`IntegerVariable`] has a unit domain (i.e. a domain of size

- ```rust
  pub fn is_predicate_assigned(self: &Self, predicate: Predicate) -> bool { /* ... */ }
  ```

- ```rust
  pub fn get_domains(self: &Self) -> DomainGeneratorIterator { /* ... */ }
  ```
  Returns all currently defined [`DomainId`]s.

###### Trait Implementations

- **Send**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **UnwindSafe**
- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `tie_breaking`

Contains structures for tie-breaking.

These structures provide an interface for deciding
between two variables when there is a tie between them (for example during variable
selection there can be two variables with the same smallest value in the domain).

The responsibility of a [`TieBreaker`] is two-fold:
- First of all, it should have the ability to break arbitrary ties between values, for example,
  if we consider the [`Smallest`] strategy then a tie could occur when two variables have the
  same lower-bound; one tie-breaking strategy could be to simply pick the first element that was
  encountered (implemented in [`InOrderTieBreaker`]) but others could be considered.
- Secondly, it should keep track of which variable to consider based on the value (and based on
  the [`Direction`]); if we once again look at the example of [`Smallest`] then the
  [`TieBreaker`] should only consider tie-breaking between variables with the same value or
  update the "best" variable found so far. For example, considering the [`Smallest`]
  [`VariableSelector`], if we have two variables, `x` with lower-bound 5 and `y` with
  lower-bound 6 then the [`TieBreaker`] should only consider `x` as potential candidate since it
  has a strictly lower value and the direction of this [`VariableSelector`] is
  [`Direction::Minimum`].

The following example shows how a simple [`TieBreaker`] ([`InOrderTieBreaker`]) will
select the first variable with the lowest-value that it has found.

```rust
# use pumpkin_solver::branching::tie_breaking::InOrderTieBreaker;
# use pumpkin_solver::variables::DomainId;
# use pumpkin_solver::branching::tie_breaking::Direction;
# use pumpkin_solver::branching::tie_breaking::TieBreaker;
let mut breaker = InOrderTieBreaker::new(Direction::Minimum);

// We consider 3 variables, where only variables with ID 1 and ID 2 should be considered.
// We expect the variable with ID 1 to be selected since it was the first one with
// the minimum value which was considered.
breaker.consider(DomainId::new(0), 10);
breaker.consider(DomainId::new(1), 5);
breaker.consider(DomainId::new(2), 5);

let selected = breaker.select();
assert!(selected.is_some());
assert_eq!(selected.unwrap(), DomainId::new(1));
```

```rust
pub mod tie_breaking { /* ... */ }
```

### Modules

## Module `in_order_tie_breaker`

```rust
pub(in ::branching::tie_breaking) mod in_order_tie_breaker { /* ... */ }
```

### Types

#### Struct `InOrderTieBreaker`

A tie-breaker which simply selects the first variable that it receives with the "best" value
according to the provided [`Direction`].

 For example, if the provided direction is [`Direction::Minimum`] and there are two variables
`x1` with value 5 and `x2` with value 5, if the tie-breaker first receives `x2` and then `x1`
then it will return `x2` because it was the first variable with the minimum value (of 5 in this
example) which was provided.

```rust
pub struct InOrderTieBreaker<Var, Value> {
    pub(in ::branching::tie_breaking::in_order_tie_breaker) selected_variable: Option<Var>,
    pub(in ::branching::tie_breaking::in_order_tie_breaker) selected_value: Option<Value>,
    pub(in ::branching::tie_breaking::in_order_tie_breaker) direction: super::Direction,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `selected_variable` | `Option<Var>` | The selected variable, could be [None] if no variable has been considered yet |
| `selected_value` | `Option<Value>` | The selected value, could be [None] if no variable has been considered yet |
| `direction` | `super::Direction` | Whether the tie-breaker should find the variable with the maximum or minimum value |

##### Implementations

###### Methods

- ```rust
  pub fn new(direction: Direction) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::branching::tie_breaking::in_order_tie_breaker) fn reset(self: &mut Self) { /* ... */ }
  ```

###### Trait Implementations

- **IntoEither**
- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **RefUnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **TieBreaker**
  - ```rust
    fn consider(self: &mut Self, variable: Var, value: Value) { /* ... */ }
    ```

  - ```rust
    fn select(self: &mut Self) -> Option<Var> { /* ... */ }
    ```

  - ```rust
    fn get_direction(self: &Self) -> Direction { /* ... */ }
    ```

## Module `random_tie_breaker`

```rust
pub(in ::branching::tie_breaking) mod random_tie_breaker { /* ... */ }
```

### Types

#### Struct `RandomTieBreaker`

A tie breaker which selects the variable with the "best" value (according to the [`Direction`]),
if there is a tie then it will select any of the variables part of this tie with equal
probability.

The random selection proceeds as follows:
- If no variable has been considered yet then this is the one which is currently considered to
  be selected
- If a variable has previously been considered then we can split into 3 cases:
    - If the direction is [`Direction::Maximum`] and the value of the newly provided variable is
      stricly bigger than that of the currently selected variable then we update the currently
      selected variable
    - If the direction is [`Direction::Minimum`] and the value of the newly provided variable is
      stricly smaller than that of the currently selected variable then we update the currently
      selected variable
    - If the values are equal then we randomly select the newly considered variable with
      probability `1 / num_previously_seen_variables` where `num_previously_seen_variables` is
      the number of variables which have been previously considered with the same value

```rust
pub struct RandomTieBreaker<Var, Value> {
    pub(in ::branching::tie_breaking::random_tie_breaker) selected_variable: Option<Var>,
    pub(in ::branching::tie_breaking::random_tie_breaker) selected_value: Option<Value>,
    pub(in ::branching::tie_breaking::random_tie_breaker) rng: Box<dyn Random>,
    pub(in ::branching::tie_breaking::random_tie_breaker) num_variables_considered: usize,
    pub(in ::branching::tie_breaking::random_tie_breaker) direction: super::Direction,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `selected_variable` | `Option<Var>` | The selected variable, could be [None] if no variable has been considered yet |
| `selected_value` | `Option<Value>` | The selected value, could be [None] if no variable has been considered yet |
| `rng` | `Box<dyn Random>` | The [SeedableRng] which is used for randomly selecting the variable |
| `num_variables_considered` | `usize` | The number of variables with the current<br>[`selected_value`][RandomTieBreaker::selected_value] |
| `direction` | `super::Direction` | Whether the tie-breaker should find the variable with the maximum or minimum value |

##### Implementations

###### Methods

- ```rust
  pub fn new(direction: Direction, rng: Box<dyn Random>) -> Self { /* ... */ }
  ```

- ```rust
  pub(in ::branching::tie_breaking::random_tie_breaker) fn reset(self: &mut Self) { /* ... */ }
  ```

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **Freeze**
- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **TieBreaker**
  - ```rust
    fn consider(self: &mut Self, variable: Var, value: Value) { /* ... */ }
    ```

  - ```rust
    fn select(self: &mut Self) -> Option<Var> { /* ... */ }
    ```

  - ```rust
    fn get_direction(self: &Self) -> Direction { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

## Module `tie_breaker`

```rust
pub(in ::branching::tie_breaking) mod tie_breaker { /* ... */ }
```

### Types

#### Enum `Direction`

Whether the value comparison should find the maximum [`Direction::Maximum`] variable or the
[`Direction::Minimum`] variable.

```rust
pub enum Direction {
    Maximum,
    Minimum,
}
```

##### Variants

###### `Maximum`

###### `Minimum`

##### Implementations

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Freeze**
- **StructuralPartialEq**
- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &Direction) -> bool { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **UnwindSafe**
- **RefUnwindSafe**
- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> Direction { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

### Traits

#### Trait `TieBreaker`

The interface for a tie-breaker which considers additional elements with values; depending on
the [`Direction`] it should only consider variables with the "best" value for selection.

```rust
pub trait TieBreaker<Var, Value> {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `consider`: Consider the next additional element with corresponding value
- `select`: Get the final variable which was selected. After this method is called it resets the stored
- `get_direction`: Returns whether the tie-breaker is attempting to find the minimum ([`Direction::Minimum`])

##### Implementations

This trait is implemented for the following types:

- `InOrderTieBreaker<Var, Value>` with <Var: Copy, Value: PartialOrd>
- `RandomTieBreaker<Var, Value>` with <Var: Copy, Value: PartialOrd>

### Re-exports

#### Re-export `in_order_tie_breaker::*`

```rust
pub use in_order_tie_breaker::*;
```

#### Re-export `random_tie_breaker::*`

```rust
pub use random_tie_breaker::*;
```

#### Re-export `tie_breaker::*`

```rust
pub use tie_breaker::*;
```

## Module `value_selection`

Provides the [`ValueSelector`] trait which is required
for value selectors to implement; the main method in this trait relies on
[`ValueSelector::select_value`].

Furthermore, it defines several implementations of the [`ValueSelector`] trait. Any
[`ValueSelector`] should only select values which are in the domain of the provided variable.

```rust
pub mod value_selection { /* ... */ }
```

### Modules

## Module `dynamic_value_selector`

```rust
pub(in ::branching::value_selection) mod dynamic_value_selector { /* ... */ }
```

### Types

#### Struct `DynamicValueSelector`

Similar to [`DynamicBrancher`], this is a pass-along structure which should be used when a
[`Sized`] object is required.

```rust
pub struct DynamicValueSelector<Var> {
    pub(in ::branching::value_selection::dynamic_value_selector) selector: Box<dyn ValueSelector<Var>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `selector` | `Box<dyn ValueSelector<Var>>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(selector: Box<dyn ValueSelector<Var>>) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **Send**
- **Unpin**
- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn on_solution(self: &mut Self, solution: SolutionReference<''_>) { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, value: i32) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

## Module `in_domain_interval`

```rust
pub(in ::branching::value_selection) mod in_domain_interval { /* ... */ }
```

### Types

#### Struct `InDomainInterval`

Reduces the domain (consisting of intervals) to its first interval.

If the domain consists of several intervals (e.g. a variable with the domain {0, 1, 4, 5, 6, 9,
10} consists of the interval {[0-1], [4-6], [9-10]}), then this [`ValueSelector`] will reduce
the domain to the first interval (e.g. to {0, 1} in the previous example).

Otherwise (i.e. if the domain is one continuous interval) then it will bisect the domain in the
same manner as [`InDomainSplit`].

```rust
pub struct InDomainInterval;
```

##### Implementations

###### Trait Implementations

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Copy**
- **Sync**
- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainInterval { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

## Module `in_domain_max`

```rust
pub(in ::branching::value_selection) mod in_domain_max { /* ... */ }
```

### Types

#### Struct `InDomainMax`

[`ValueSelector`] which chooses to assign the provided variable to its upper-bound.

```rust
pub struct InDomainMax;
```

##### Implementations

###### Trait Implementations

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainMax { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Copy**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `in_domain_median`

```rust
pub(in ::branching::value_selection) mod in_domain_median { /* ... */ }
```

### Types

#### Struct `InDomainMedian`

A [`ValueSelector`] which selects the median value in the domain (or if this value is already
assigned then the closest variable to it in terms of index).

```rust
pub struct InDomainMedian;
```

##### Implementations

###### Trait Implementations

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Send**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainMedian { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
## Module `in_domain_middle`

```rust
pub(in ::branching::value_selection) mod in_domain_middle { /* ... */ }
```

### Types

#### Struct `InDomainMiddle`

A [`ValueSelector`] which selects the middle value in the domain (or if this value is already
assigned then the closest variable to it).

Note that this strategy is different from [`InDomainMedian`] if there are holes in the
domain.

```rust
pub struct InDomainMiddle;
```

##### Implementations

###### Trait Implementations

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Send**
- **Freeze**
- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **IntoEither**
- **Unpin**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainMiddle { /* ... */ }
    ```

## Module `in_domain_min`

```rust
pub(in ::branching::value_selection) mod in_domain_min { /* ... */ }
```

### Types

#### Struct `InDomainMin`

[`ValueSelector`] which chooses to assign the provided variable to its lowest-bound.

```rust
pub struct InDomainMin;
```

##### Implementations

###### Trait Implementations

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **IntoEither**
- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **Copy**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Sync**
- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainMin { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

## Module `in_domain_random`

```rust
pub(in ::branching::value_selection) mod in_domain_random { /* ... */ }
```

### Types

#### Struct `InDomainRandom`

A [`ValueSelector`] which assigns to a random value in the domain.

```rust
pub struct InDomainRandom;
```

##### Implementations

###### Trait Implementations

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Literal) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **UnwindSafe**
- **IntoEither**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainRandom { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
## Module `in_domain_split`

```rust
pub(in ::branching::value_selection) mod in_domain_split { /* ... */ }
```

### Types

#### Struct `InDomainSplit`

A [`ValueSelector`] which splits the domain in half (based on the lower-bound and upper-bound,
disregarding holes) and removes the upper-half from the domain.

Note that this strategy will not necessarily result in an equal split if there are holes in the
domain.

```rust
pub struct InDomainSplit;
```

##### Implementations

###### Methods

- ```rust
  pub fn get_predicate_excluding_upper_half<Var: IntegerVariable + Copy>(context: &SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
  ```

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Copy**
- **RefUnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainSplit { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

## Module `in_domain_split_random`

```rust
pub(in ::branching::value_selection) mod in_domain_split_random { /* ... */ }
```

### Types

#### Struct `InDomainSplitRandom`

A [`ValueSelector`] which bisects the domain in the middle (between the lower-bound and
lower-bound, disregarding holes), randomly selecting whether to exclude the lower-half or the
upper-half.

```rust
pub struct InDomainSplitRandom;
```

##### Implementations

###### Trait Implementations

- **Send**
- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Copy**
- **Unpin**
- **UnwindSafe**
- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Freeze**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> InDomainSplitRandom { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

## Module `out_domain_max`

```rust
pub(in ::branching::value_selection) mod out_domain_max { /* ... */ }
```

### Types

#### Struct `OutDomainMax`

A [`ValueSelector`] which excludes the largest value from the domain.

```rust
pub struct OutDomainMax;
```

##### Implementations

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Copy**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OutDomainMax { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

## Module `out_domain_median`

```rust
pub(in ::branching::value_selection) mod out_domain_median { /* ... */ }
```

### Types

#### Struct `OutDomainMedian`

A [`ValueSelector`] which excludes the median value from the domain.

```rust
pub struct OutDomainMedian;
```

##### Implementations

###### Trait Implementations

- **UnwindSafe**
- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OutDomainMedian { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Copy**
- **Freeze**
- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

## Module `out_domain_min`

```rust
pub(in ::branching::value_selection) mod out_domain_min { /* ... */ }
```

### Types

#### Struct `OutDomainMin`

A [`ValueSelector`] which excludes the smallest value from the domain.

```rust
pub struct OutDomainMin;
```

##### Implementations

###### Trait Implementations

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OutDomainMin { /* ... */ }
    ```

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **Copy**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `out_domain_random`

```rust
pub(in ::branching::value_selection) mod out_domain_random { /* ... */ }
```

### Types

#### Struct `OutDomainRandom`

A [`ValueSelector`] which excludes a random value from the domain.

```rust
pub struct OutDomainRandom;
```

##### Implementations

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Send**
- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Freeze**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **Unpin**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OutDomainRandom { /* ... */ }
    ```

## Module `random_splitter`

```rust
pub(in ::branching::value_selection) mod random_splitter { /* ... */ }
```

### Types

#### Struct `RandomSplitter`

A [`ValueSelector`] which splits the domain in a random manner (between the lower-bound and
lower-bound, disregarding holes), randomly selecting whether to exclude the lower-half or the
upper-half.

```rust
pub struct RandomSplitter;
```

##### Implementations

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Freeze**
- **UnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Unpin**
- **IntoEither**
- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> RandomSplitter { /* ... */ }
    ```

- **Copy**
- **Sync**
- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: DomainId) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

## Module `reverse_in_domain_split`

```rust
pub(in ::branching::value_selection) mod reverse_in_domain_split { /* ... */ }
```

### Types

#### Struct `ReverseInDomainSplit`

A [`ValueSelector`] which splits the domain in half (based on the lower-bound and upper-bound,
disregarding holes) and removes the lower-half from the domain.

Note that this strategy will not necessarily result in an equal split if there are holes in the
domain.

```rust
pub struct ReverseInDomainSplit;
```

##### Implementations

###### Trait Implementations

- **Unpin**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Freeze**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **IntoEither**
- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> ReverseInDomainSplit { /* ... */ }
    ```

- **UnwindSafe**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ValueSelector**
  - ```rust
    fn select_value(self: &mut Self, context: &mut SelectionContext<''_>, decision_variable: Var) -> Predicate { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

## Module `value_selector`

```rust
pub(in ::branching::value_selection) mod value_selector { /* ... */ }
```

### Traits

#### Trait `ValueSelector`

A trait containing the interface for [`ValueSelector`]s,
specifying the appropriate hooks into the solver and the methods required for selecting a value
for a given variable.

```rust
pub trait ValueSelector<Var> {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `select_value`: Determines which value in the domain of `decision_variable` to branch next on.
- `subscribe_to_events`: Indicates which [`BrancherEvent`] are relevant for this particular [`ValueSelector`].

##### Provided Methods

- ```rust
  fn on_unassign_integer(self: &mut Self, _variable: DomainId, _value: i32) { /* ... */ }
  ```
  A function which is called after a [`DomainId`] is unassigned during backtracking (i.e. when

- ```rust
  fn on_solution(self: &mut Self, _solution: SolutionReference<''_>) { /* ... */ }
  ```
  This method is called when a solution is found; either when iterating over all solutions in

- ```rust
  fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
  ```
  This method returns whether a restart is *currently* pointless for the [`ValueSelector`].

##### Implementations

This trait is implemented for the following types:

- `DynamicValueSelector<Var>` with <Var>
- `InDomainInterval`
- `InDomainMax` with <Var: IntegerVariable + Copy>
- `InDomainMedian` with <Var: IntegerVariable + Copy>
- `InDomainMiddle` with <Var: IntegerVariable + Copy>
- `InDomainMin` with <Var: IntegerVariable + Copy>
- `InDomainRandom`
- `InDomainRandom`
- `InDomainSplit` with <Var: IntegerVariable + Copy>
- `InDomainSplitRandom`
- `OutDomainMax`
- `OutDomainMedian`
- `OutDomainMin`
- `OutDomainRandom`
- `RandomSplitter`
- `ReverseInDomainSplit` with <Var: IntegerVariable + Copy>

### Re-exports

#### Re-export `ValueSelector`

```rust
pub use value_selector::ValueSelector;
```

#### Re-export `dynamic_value_selector::*`

```rust
pub use dynamic_value_selector::*;
```

#### Re-export `in_domain_interval::*`

```rust
pub use in_domain_interval::*;
```

#### Re-export `in_domain_max::*`

```rust
pub use in_domain_max::*;
```

#### Re-export `in_domain_median::*`

```rust
pub use in_domain_median::*;
```

#### Re-export `in_domain_middle::*`

```rust
pub use in_domain_middle::*;
```

#### Re-export `in_domain_min::*`

```rust
pub use in_domain_min::*;
```

#### Re-export `in_domain_random::*`

```rust
pub use in_domain_random::*;
```

#### Re-export `in_domain_split::*`

```rust
pub use in_domain_split::*;
```

#### Re-export `in_domain_split_random::*`

```rust
pub use in_domain_split_random::*;
```

#### Re-export `out_domain_max::*`

```rust
pub use out_domain_max::*;
```

#### Re-export `out_domain_median::*`

```rust
pub use out_domain_median::*;
```

#### Re-export `out_domain_min::*`

```rust
pub use out_domain_min::*;
```

#### Re-export `out_domain_random::*`

```rust
pub use out_domain_random::*;
```

#### Re-export `random_splitter::*`

```rust
pub use random_splitter::*;
```

#### Re-export `reverse_in_domain_split::*`

```rust
pub use reverse_in_domain_split::*;
```

## Module `variable_selection`

Provides the [`VariableSelector`] trait which is required
for variable selectors to implement; the main method in this trait relies on
[`VariableSelector::select_variable`].

Furthermore, it defines several implementations of the [`VariableSelector`] trait. Any
[`VariableSelector`] should only select variables which have a domain of size 2 or larger.

```rust
pub mod variable_selection { /* ... */ }
```

### Modules

## Module `anti_first_fail`

```rust
pub(in ::branching::variable_selection) mod anti_first_fail { /* ... */ }
```

### Types

#### Struct `AntiFirstFail`

A [`VariableSelector`] which selects the variable with the largest domain (based on the
lower-bound and upper-bound, disregarding holes).

Uses a [`TieBreaker`] to break ties, the default is the [`InOrderTieBreaker`] but it is
possible to construct the variable selector with a custom [`TieBreaker`] by
using the method [`AntiFirstFail::with_tie_breaker`].

```rust
pub struct AntiFirstFail<Var, TieBreaking> {
    pub(in ::branching::variable_selection::anti_first_fail) variables: Vec<Var>,
    pub(in ::branching::variable_selection::anti_first_fail) tie_breaker: TieBreaking,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var]) -> Self { /* ... */ }
  ```

- ```rust
  pub fn with_tie_breaker(variables: &[Var], tie_breaker: TieBreaking) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Sync**
- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Freeze**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

## Module `dynamic_variable_selector`

```rust
pub(in ::branching::variable_selection) mod dynamic_variable_selector { /* ... */ }
```

### Types

#### Struct `DynamicVariableSelector`

Similar to [`DynamicBrancher`], this is a pass-along structure which should be used when a
[`Sized`] object is required.

```rust
pub struct DynamicVariableSelector<Var> {
    pub(in ::branching::variable_selection::dynamic_variable_selector) selector: Box<dyn VariableSelector<Var>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `selector` | `Box<dyn VariableSelector<Var>>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(selector: Box<dyn VariableSelector<Var>>) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **RefUnwindSafe**
- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Send**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Var> { /* ... */ }
    ```

  - ```rust
    fn on_appearance_in_conflict_predicate(self: &mut Self, predicate: Predicate) { /* ... */ }
    ```

  - ```rust
    fn on_conflict(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, value: i32) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

## Module `first_fail`

```rust
pub(in ::branching::variable_selection) mod first_fail { /* ... */ }
```

### Types

#### Struct `FirstFail`

A [`VariableSelector`] which selects the variable with the smallest domain (based on the
lower-bound and upper-bound, disregarding holes).

Uses a [`TieBreaker`] to break ties, the default is the [`InOrderTieBreaker`] but it is
possible to construct the variable selector with a custom [`TieBreaker`] by using
the method [`FirstFail::with_tie_breaker`].

```rust
pub struct FirstFail<Var, TieBreaking> {
    pub(in ::branching::variable_selection::first_fail) variables: Vec<Var>,
    pub(in ::branching::variable_selection::first_fail) tie_breaker: TieBreaking,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var]) -> Self { /* ... */ }
  ```

- ```rust
  pub fn with_tie_breaker(variables: &[Var], tie_breaker: TieBreaking) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

## Module `input_order`

```rust
pub(in ::branching::variable_selection) mod input_order { /* ... */ }
```

### Types

#### Struct `InputOrder`

A [`VariableSelector`] which selects the first variable which is not fixed given the order in
the provided list.

```rust
pub struct InputOrder<Var> {
    pub(in ::branching::variable_selection::input_order) variables: Vec<Var>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var]) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **RefUnwindSafe**
- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<Literal> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Unpin**
## Module `largest`

```rust
pub(in ::branching::variable_selection) mod largest { /* ... */ }
```

### Types

#### Struct `Largest`

A [`VariableSelector`] which selects the variable with the largest value in its domain.

Uses a [`TieBreaker`] to break ties, the default is the [`InOrderTieBreaker`] but it is
possible to construct the variable selector with a custom [`TieBreaker`] by using the
method [`Largest::with_tie_breaker`].

```rust
pub struct Largest<Var, TieBreaking> {
    pub(in ::branching::variable_selection::largest) variables: Vec<Var>,
    pub(in ::branching::variable_selection::largest) tie_breaker: TieBreaking,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var]) -> Self { /* ... */ }
  ```

- ```rust
  pub fn with_tie_breaker(variables: &[Var], tie_breaker: TieBreaking) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **RefUnwindSafe**
- **Sync**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Send**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `max_regret`

```rust
pub(in ::branching::variable_selection) mod max_regret { /* ... */ }
```

### Types

#### Struct `MaxRegret`

A [`VariableSelector`] which selects the variable with the largest difference between the two
smallest values in its domain.

Currently, due to the implementation of the domains, in the worst-case this selector will go
through all variables and all values between the upper-bound and lower-bound.

Uses a [`TieBreaker`] to break ties, the default is the [`InOrderTieBreaker`] but it is
possible to construct the variable selector with a custom [`TieBreaker`] by using
the method [`MaxRegret::with_tie_breaker`].

```rust
pub struct MaxRegret<Var, TieBreaking> {
    pub(in ::branching::variable_selection::max_regret) variables: Vec<Var>,
    pub(in ::branching::variable_selection::max_regret) tie_breaker: TieBreaking,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var]) -> Self { /* ... */ }
  ```

- ```rust
  pub fn with_tie_breaker(variables: &[Var], tie_breaker: TieBreaking) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Freeze**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
## Module `most_constrained`

```rust
pub(in ::branching::variable_selection) mod most_constrained { /* ... */ }
```

### Types

#### Struct `MostConstrained`

A [`VariableSelector`] which selects the variable with the smallest domain (similar to
[`FirstFail`]).

It breaks ties according to the number of attached
constraints (giving priority to variable with more attached constraints).

```rust
pub struct MostConstrained<Var, TieBreaking> {
    pub(in ::branching::variable_selection::most_constrained) variables: Vec<Var>,
    pub(in ::branching::variable_selection::most_constrained) tie_breaker: TieBreaking,
    pub(in ::branching::variable_selection::most_constrained) num_occurrences: Vec<u32>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |
| `num_occurrences` | `Vec<u32>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var], num_occurrences: &[u32]) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **RefUnwindSafe**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

#### Struct `MostConstrainedValue`

```rust
pub(in ::branching::variable_selection::most_constrained) struct MostConstrainedValue {
    pub(in ::branching::variable_selection::most_constrained) domain_size: i32,
    pub(in ::branching::variable_selection::most_constrained) number_of_attached_constraints: u32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `domain_size` | `i32` |  |
| `number_of_attached_constraints` | `u32` |  |

##### Implementations

###### Trait Implementations

- **RefUnwindSafe**
- **Send**
- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **PartialOrd**
  - ```rust
    fn partial_cmp(self: &Self, other: &Self) -> Option<Ordering> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &MostConstrainedValue) -> bool { /* ... */ }
    ```

- **StructuralPartialEq**
- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

## Module `occurrence`

```rust
pub(in ::branching::variable_selection) mod occurrence { /* ... */ }
```

### Types

#### Struct `Occurrence`

A [`VariableSelector`] which selects the variable with the largest number of attached
constraints (where the provided `num_occurrences` stores the number of
attached constraints per variable).

```rust
pub struct Occurrence<Var, TieBreaking> {
    pub(in ::branching::variable_selection::occurrence) variables: Vec<Var>,
    pub(in ::branching::variable_selection::occurrence) tie_breaker: TieBreaking,
    pub(in ::branching::variable_selection::occurrence) num_occurrences: Vec<u32>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |
| `num_occurrences` | `Vec<u32>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var], num_occurrences: &[u32]) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Sync**
- **RefUnwindSafe**
- **Freeze**
- **Unpin**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

## Module `proportional_domain_size`

```rust
pub(in ::branching::variable_selection) mod proportional_domain_size { /* ... */ }
```

### Types

#### Struct `ProportionalDomainSize`

```rust
pub struct ProportionalDomainSize {
    pub(in ::branching::variable_selection::proportional_domain_size) domain_sizes: Vec<f64>,
    pub(in ::branching::variable_selection::proportional_domain_size) weights_idx_to_variables: Vec<usize>,
    pub(in ::branching::variable_selection::proportional_domain_size) variables: Vec<crate::variables::DomainId>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `domain_sizes` | `Vec<f64>` | A list domain sizes, used as weights to select the next variable. |
| `weights_idx_to_variables` | `Vec<usize>` | For every entry in `domain_sizes`, the index into `variables` for the corresponding<br>variable. |
| `variables` | `Vec<crate::variables::DomainId>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[DomainId]) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **Send**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn on_backtrack(self: &mut Self) { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `random`

```rust
pub(in ::branching::variable_selection) mod random { /* ... */ }
```

### Types

#### Struct `RandomSelector`

A [`VariableSelector`] which selects a random unfixed variable.

```rust
pub struct RandomSelector {
    pub(in ::branching::variable_selection::random) variables: sparse_set::SparseSet<crate::variables::DomainId>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `sparse_set::SparseSet<crate::variables::DomainId>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new</* synthetic */ impl IntoIterator<Item = DomainId>: IntoIterator<Item = DomainId>>(variables: impl IntoIterator<Item = DomainId>) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn on_unassign_integer(self: &mut Self, variable: DomainId, _value: i32) { /* ... */ }
    ```

  - ```rust
    fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **Send**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **Freeze**
- **RefUnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

## Module `smallest`

```rust
pub(in ::branching::variable_selection) mod smallest { /* ... */ }
```

### Types

#### Struct `Smallest`

A [`VariableSelector`] which selects the variable with the smallest value in its domain.

Uses a [`TieBreaker`] to break ties, the default is the [`InOrderTieBreaker`] but it is
possible to construct the variable selector with a custom [`TieBreaker`] by using
the method [`Smallest::with_tie_breaker`].

```rust
pub struct Smallest<Var, TieBreaking> {
    pub(in ::branching::variable_selection::smallest) variables: Vec<Var>,
    pub(in ::branching::variable_selection::smallest) tie_breaker: TieBreaking,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `Vec<Var>` |  |
| `tie_breaker` | `TieBreaking` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(variables: &[Var]) -> Self { /* ... */ }
  ```

- ```rust
  pub fn with_tie_breaker(variables: &[Var], tie_breaker: TieBreaking) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **VariableSelector**
  - ```rust
    fn select_variable(self: &mut Self, context: &mut SelectionContext<''_>) -> Option<DomainId> { /* ... */ }
    ```

  - ```rust
    fn subscribe_to_events(self: &Self) -> Vec<BrancherEvent> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
## Module `variable_selector`

```rust
pub(in ::branching::variable_selection) mod variable_selector { /* ... */ }
```

### Traits

#### Trait `VariableSelector`

A trait containing the interface for [`VariableSelector`]s,
specifying the appropriate hooks into the solver and the methods required for selecting
variables.

```rust
pub trait VariableSelector<Var> {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `select_variable`: Determines which variable to select next if there are any left to branch on.
- `subscribe_to_events`: Indicates which [`BrancherEvent`] are relevant for this particular [`VariableSelector`].

##### Provided Methods

- ```rust
  fn on_conflict(self: &mut Self) { /* ... */ }
  ```
  A function which is called after a conflict has been found and processed but (currently)

- ```rust
  fn on_backtrack(self: &mut Self) { /* ... */ }
  ```
  A function which is called whenever a backtrack occurs in the solver.

- ```rust
  fn on_unassign_integer(self: &mut Self, _variable: DomainId, _value: i32) { /* ... */ }
  ```
  A function which is called after a [`DomainId`] is unassigned during backtracking (i.e. when

- ```rust
  fn on_appearance_in_conflict_predicate(self: &mut Self, _predicate: Predicate) { /* ... */ }
  ```
  A function which is called when a [`Predicate`] appears in a conflict during conflict

- ```rust
  fn is_restart_pointless(self: &mut Self) -> bool { /* ... */ }
  ```
  This method returns whether a restart is *currently* pointless for the [`VariableSelector`].

##### Implementations

This trait is implemented for the following types:

- `AntiFirstFail<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking: TieBreaker<crate::engine::variables::DomainId, i32>>
- `DynamicVariableSelector<Var>` with <Var>
- `FirstFail<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking>
- `InputOrder<crate::engine::variables::DomainId>`
- `InputOrder<crate::variables::Literal>`
- `Largest<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking>
- `MaxRegret<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking>
- `MostConstrained<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking>
- `Occurrence<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking>
- `ProportionalDomainSize`
- `RandomSelector`
- `Smallest<crate::engine::variables::DomainId, TieBreaking>` with <TieBreaking>

### Re-exports

#### Re-export `RandomSelector`

```rust
pub use random::RandomSelector;
```

#### Re-export `VariableSelector`

```rust
pub use variable_selector::VariableSelector;
```

#### Re-export `anti_first_fail::*`

```rust
pub use anti_first_fail::*;
```

#### Re-export `dynamic_variable_selector::*`

```rust
pub use dynamic_variable_selector::*;
```

#### Re-export `first_fail::*`

```rust
pub use first_fail::*;
```

#### Re-export `input_order::*`

```rust
pub use input_order::*;
```

#### Re-export `largest::*`

```rust
pub use largest::*;
```

#### Re-export `max_regret::*`

```rust
pub use max_regret::*;
```

#### Re-export `most_constrained::*`

```rust
pub use most_constrained::*;
```

#### Re-export `occurrence::*`

```rust
pub use occurrence::*;
```

#### Re-export `proportional_domain_size::*`

```rust
pub use proportional_domain_size::*;
```

#### Re-export `smallest::*`

```rust
pub use smallest::*;
```

### Re-exports

#### Re-export `SelectionContext`

```rust
pub use selection_context::SelectionContext;
```

#### Re-export `brancher::*`

```rust
pub use brancher::*;
```

## Module `constraints`

Defines the constraints that Pumpkin provides out of the box which can be added to the
[`Solver`].

A constraint is a relation over variables. In the solver, constraints are enforced through
propagators, and therefore constraints can be viewed as a collection of propagators.

# Example
```
# use pumpkin_solver::constraints;
# use pumpkin_solver::Solver;
let mut solver = Solver::default();

let a = solver.new_bounded_integer(0, 3);
let b = solver.new_bounded_integer(0, 3);

solver.add_constraint(constraints::equals([a, b], 0)).post();
```

# Note
At the moment, the API for posting propagators is not yet publicly accessible as it is
unstable. Consumers of the Pumpkin library can therefore only define constraints by
decomposing them into the constraints that are predefined in the library. Once the
propagator API is stabilized, it will become part of the public API.

```rust
pub mod constraints { /* ... */ }
```

### Modules

## Module `all_different`

```rust
pub(in ::constraints) mod all_different { /* ... */ }
```

### Functions

#### Function `all_different`

Creates the [`Constraint`] that enforces that all the given `variables` are distinct.

```rust
pub fn all_different<Var: IntegerVariable + ''static, /* synthetic */ impl Into<Box<[Var]>>: Into<Box<[Var]>>>(variables: impl Into<Box<[Var]>>) -> impl Constraint { /* ... */ }
```

## Module `arithmetic`

```rust
pub(in ::constraints) mod arithmetic { /* ... */ }
```

### Modules

## Module `equality`

```rust
pub(in ::constraints::arithmetic) mod equality { /* ... */ }
```

### Types

#### Struct `EqualConstraint`

```rust
pub(in ::constraints::arithmetic::equality) struct EqualConstraint<Var> {
    pub(in ::constraints::arithmetic::equality) terms: Box<[Var]>,
    pub(in ::constraints::arithmetic::equality) rhs: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `terms` | `Box<[Var]>` |  |
| `rhs` | `i32` |  |

##### Implementations

###### Trait Implementations

- **NegatableConstraint**
  - ```rust
    fn negation(self: &Self) -> <Self as >::NegatedConstraint { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Send**
- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

#### Struct `NotEqualConstraint`

```rust
pub(in ::constraints::arithmetic::equality) struct NotEqualConstraint<Var> {
    pub(in ::constraints::arithmetic::equality) terms: Box<[Var]>,
    pub(in ::constraints::arithmetic::equality) rhs: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `terms` | `Box<[Var]>` |  |
| `rhs` | `i32` |  |

##### Implementations

###### Trait Implementations

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **NegatableConstraint**
  - ```rust
    fn negation(self: &Self) -> <Self as >::NegatedConstraint { /* ... */ }
    ```

- **RefUnwindSafe**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

### Functions

#### Function `equals`

Creates the [`NegatableConstraint`] `\sum terms_i = rhs`.

Its negation is [`not_equals`].

```rust
pub fn equals<Var: IntegerVariable + Clone + ''static, /* synthetic */ impl Into<Box<[Var]>>: Into<Box<[Var]>>>(terms: impl Into<Box<[Var]>>, rhs: i32) -> impl NegatableConstraint { /* ... */ }
```

#### Function `binary_equals`

Creates the [`NegatableConstraint`] `lhs = rhs`.

Its negation is [`binary_not_equals`].

```rust
pub fn binary_equals<Var: IntegerVariable + ''static>(lhs: Var, rhs: Var) -> impl NegatableConstraint { /* ... */ }
```

#### Function `not_equals`

Create the [`NegatableConstraint`] `\sum terms_i != rhs`.

Its negation is [`equals`].

```rust
pub fn not_equals<Var: IntegerVariable + Clone + ''static, /* synthetic */ impl Into<Box<[Var]>>: Into<Box<[Var]>>>(terms: impl Into<Box<[Var]>>, rhs: i32) -> impl NegatableConstraint { /* ... */ }
```

#### Function `binary_not_equals`

Creates the [`NegatableConstraint`] `lhs != rhs`.

Its negation is [`binary_equals`].

```rust
pub fn binary_not_equals<Var: IntegerVariable + ''static>(lhs: Var, rhs: Var) -> impl NegatableConstraint { /* ... */ }
```

## Module `inequality`

```rust
pub(in ::constraints::arithmetic) mod inequality { /* ... */ }
```

### Types

#### Struct `Inequality`

```rust
pub(in ::constraints::arithmetic::inequality) struct Inequality<Var> {
    pub(in ::constraints::arithmetic::inequality) terms: Box<[Var]>,
    pub(in ::constraints::arithmetic::inequality) rhs: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `terms` | `Box<[Var]>` |  |
| `rhs` | `i32` |  |

##### Implementations

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **NegatableConstraint**
  - ```rust
    fn negation(self: &Self) -> <Self as >::NegatedConstraint { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: crate::variables::Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **RefUnwindSafe**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

### Functions

#### Function `less_than_or_equals`

Create the [`NegatableConstraint`] `\sum terms_i <= rhs`.

Its negation is `\sum terms_i > rhs`

```rust
pub fn less_than_or_equals<Var: IntegerVariable + ''static, /* synthetic */ impl Into<Box<[Var]>>: Into<Box<[Var]>>>(terms: impl Into<Box<[Var]>>, rhs: i32) -> impl NegatableConstraint { /* ... */ }
```

#### Function `binary_less_than_or_equals`

Creates the [`NegatableConstraint`] `lhs <= rhs`.

Its negation is `lhs > rhs`.

```rust
pub fn binary_less_than_or_equals<Var: IntegerVariable + ''static>(lhs: Var, rhs: Var) -> impl NegatableConstraint { /* ... */ }
```

#### Function `binary_less_than`

Creates the [`NegatableConstraint`] `lhs < rhs`.

Its negation is `lhs >= rhs`.

```rust
pub fn binary_less_than<Var: IntegerVariable + ''static>(lhs: Var, rhs: Var) -> impl NegatableConstraint { /* ... */ }
```

### Functions

#### Function `plus`

Creates the [`Constraint`] `a + b = c`.

```rust
pub fn plus<Var: IntegerVariable + ''static>(a: Var, b: Var, c: Var) -> impl Constraint { /* ... */ }
```

#### Function `times`

Creates the [`Constraint`] `a * b = c`.

```rust
pub fn times</* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static>(a: impl IntegerVariable + ''static, b: impl IntegerVariable + ''static, c: impl IntegerVariable + ''static) -> impl Constraint { /* ... */ }
```

#### Function `division`

Creates the [`Constraint`] `numerator / denominator = rhs`.

Note that this [`Constraint`] models truncating division (i.e. rounding towards 0).

The `denominator` should not contain the value 0 in its domain; if this is the case then the
solver will panic.

```rust
pub fn division</* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static>(numerator: impl IntegerVariable + ''static, denominator: impl IntegerVariable + ''static, rhs: impl IntegerVariable + ''static) -> impl Constraint { /* ... */ }
```

#### Function `absolute`

Creates the [`Constraint`] `|signed| = absolute`.

```rust
pub fn absolute</* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static>(signed: impl IntegerVariable + ''static, absolute: impl IntegerVariable + ''static) -> impl Constraint { /* ... */ }
```

#### Function `maximum`

Creates the [`Constraint`] `max(array) = m`.

```rust
pub fn maximum<Var: IntegerVariable + ''static, /* synthetic */ impl IntoIterator<Item = Var>: IntoIterator<Item = Var>, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static>(array: impl IntoIterator<Item = Var>, rhs: impl IntegerVariable + ''static) -> impl Constraint { /* ... */ }
```

#### Function `minimum`

Creates the [`Constraint`] `min(array) = m`.

```rust
pub fn minimum<Var: IntegerVariable + ''static, /* synthetic */ impl IntoIterator<Item = Var>: IntoIterator<Item = Var>, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static>(array: impl IntoIterator<Item = Var>, rhs: impl IntegerVariable + ''static) -> impl Constraint { /* ... */ }
```

### Re-exports

#### Re-export `equality::*`

```rust
pub use equality::*;
```

#### Re-export `inequality::*`

```rust
pub use inequality::*;
```

## Module `boolean`

```rust
pub(in ::constraints) mod boolean { /* ... */ }
```

### Types

#### Struct `BooleanLessThanOrEqual`

```rust
pub(in ::constraints::boolean) struct BooleanLessThanOrEqual {
    pub(in ::constraints::boolean) weights: Box<[i32]>,
    pub(in ::constraints::boolean) bools: Box<[crate::variables::Literal]>,
    pub(in ::constraints::boolean) rhs: i32,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `weights` | `Box<[i32]>` |  |
| `bools` | `Box<[crate::variables::Literal]>` |  |
| `rhs` | `i32` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::constraints::boolean) fn create_domains(self: &Self) -> Vec<AffineView<DomainId>> { /* ... */ }
  ```

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Send**
- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

#### Struct `BooleanEqual`

```rust
pub(in ::constraints::boolean) struct BooleanEqual {
    pub(in ::constraints::boolean) weights: Box<[i32]>,
    pub(in ::constraints::boolean) bools: Box<[crate::variables::Literal]>,
    pub(in ::constraints::boolean) rhs: crate::variables::DomainId,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `weights` | `Box<[i32]>` |  |
| `bools` | `Box<[crate::variables::Literal]>` |  |
| `rhs` | `crate::variables::DomainId` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::constraints::boolean) fn create_domains(self: &Self) -> Vec<AffineView<DomainId>> { /* ... */ }
  ```

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **RefUnwindSafe**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Freeze**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
### Functions

#### Function `boolean_less_than_or_equals`

Creates the [`Constraint`] `\sum weights_i * bools_i <= rhs`.

```rust
pub fn boolean_less_than_or_equals</* synthetic */ impl Into<Box<[i32]>>: Into<Box<[i32]>>, /* synthetic */ impl Into<Box<[Literal]>>: Into<Box<[crate::variables::Literal]>>>(weights: impl Into<Box<[i32]>>, bools: impl Into<Box<[crate::variables::Literal]>>, rhs: i32) -> impl Constraint { /* ... */ }
```

#### Function `boolean_equals`

Creates the [`Constraint`] `\sum weights_i * bools_i == rhs`.

```rust
pub fn boolean_equals</* synthetic */ impl Into<Box<[i32]>>: Into<Box<[i32]>>, /* synthetic */ impl Into<Box<[Literal]>>: Into<Box<[crate::variables::Literal]>>>(weights: impl Into<Box<[i32]>>, bools: impl Into<Box<[crate::variables::Literal]>>, rhs: crate::variables::DomainId) -> impl Constraint { /* ... */ }
```

## Module `clause`

```rust
pub(in ::constraints) mod clause { /* ... */ }
```

### Types

#### Struct `Clause`

```rust
pub(in ::constraints::clause) struct Clause(pub(in ::constraints::clause) Vec<crate::variables::Literal>);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `Vec<crate::variables::Literal>` |  |

##### Implementations

###### Trait Implementations

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **NegatableConstraint**
  - ```rust
    fn negation(self: &Self) -> <Self as >::NegatedConstraint { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

#### Struct `Conjunction`

```rust
pub(in ::constraints::clause) struct Conjunction(pub(in ::constraints::clause) Vec<crate::variables::Literal>);
```

##### Fields

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `Vec<crate::variables::Literal>` |  |

##### Implementations

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **NegatableConstraint**
  - ```rust
    fn negation(self: &Self) -> <Self as >::NegatedConstraint { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Freeze**
- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **UnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **Send**
- **RefUnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

### Functions

#### Function `clause`

Creates the [`NegatableConstraint`] `\/ literal`

Its negation is `/\ !literal`

```rust
pub fn clause</* synthetic */ impl Into<Vec<Literal>>: Into<Vec<crate::variables::Literal>>>(literals: impl Into<Vec<crate::variables::Literal>>) -> impl NegatableConstraint { /* ... */ }
```

#### Function `conjunction`

Creates the [`NegatableConstraint`] `/\ literal`

Its negation is `\/ !literal`

```rust
pub fn conjunction</* synthetic */ impl Into<Vec<Literal>>: Into<Vec<crate::variables::Literal>>>(literals: impl Into<Vec<crate::variables::Literal>>) -> impl NegatableConstraint { /* ... */ }
```

## Module `constraint_poster`

```rust
pub(in ::constraints) mod constraint_poster { /* ... */ }
```

### Types

#### Struct `ConstraintPoster`

A structure which is responsible for adding the created [`Constraint`]s to the
[`Solver`]. For an example on how to use this, see [`crate::constraints`].

```rust
pub struct ConstraintPoster<''solver, ConstraintImpl> {
    pub(in ::constraints::constraint_poster) solver: &''solver mut crate::Solver,
    pub(in ::constraints::constraint_poster) constraint: Option<ConstraintImpl>,
    pub(in ::constraints::constraint_poster) tag: Option<std::num::NonZero<u32>>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `solver` | `&''solver mut crate::Solver` |  |
| `constraint` | `Option<ConstraintImpl>` |  |
| `tag` | `Option<std::num::NonZero<u32>>` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(solver: &''a mut Solver, constraint: ConstraintImpl) -> Self { /* ... */ }
  ```

- ```rust
  pub fn with_tag(self: Self, tag: NonZero<u32>) -> Self { /* ... */ }
  ```
  Tag the constraint with an integer. This tag is used in the proof to identify which

- ```rust
  pub fn post(self: Self) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Add the [`Constraint`] to the [`Solver`].

- ```rust
  pub fn implied_by(self: Self, reification_literal: Literal) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Add the half-reified version of the [`Constraint`] to the [`Solver`]; i.e. post the

- ```rust
  pub fn reify(self: Self, reification_literal: Literal) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Add the reified version of the [`Constraint`] to the [`Solver`]; i.e. post the constraint

###### Trait Implementations

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Drop**
  - ```rust
    fn drop(self: &mut Self) { /* ... */ }
    ```

- **RefUnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **IntoEither**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
## Module `cumulative`

```rust
pub(in ::constraints) mod cumulative { /* ... */ }
```

### Types

#### Struct `CumulativeConstraint`

```rust
pub(in ::constraints::cumulative) struct CumulativeConstraint<Var> {
    pub(in ::constraints::cumulative) tasks: Vec<crate::propagators::ArgTask<Var>>,
    pub(in ::constraints::cumulative) resource_capacity: i32,
    pub(in ::constraints::cumulative) options: crate::propagators::CumulativeOptions,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `tasks` | `Vec<crate::propagators::ArgTask<Var>>` |  |
| `resource_capacity` | `i32` |  |
| `options` | `crate::propagators::CumulativeOptions` |  |

##### Implementations

###### Methods

- ```rust
  pub(in ::constraints::cumulative) fn new(tasks: &[ArgTask<Var>], resource_capacity: i32, options: CumulativeOptions) -> Self { /* ... */ }
  ```

###### Trait Implementations

- **Send**
- **Constraint**
  - ```rust
    fn post(self: Self, solver: &mut Solver, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

  - ```rust
    fn implied_by(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError> { /* ... */ }
    ```

- **Unpin**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

### Functions

#### Function `cumulative`

Creates the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) [`Constraint`].

This constraint ensures that at no point in time, the cumulative resource usage of the tasks
exceeds `bound`.

The implementation uses a form of time-table reasoning (for an example of this type of
reasoning, see \[1], note that it does **not** implement the specific algorithm in the paper
but that the reasoning used is the same).

The length of `start_times`, `durations` and `resource_requirements` should be the same; if
this is not the case then this method will panic.

It is possible to specify certain options for the cumulative (such as whether to allow holes in
the domain or the type of explanation) using [`cumulative_with_options`].

# Example
```rust
// We construct three tasks for a resource with capacity 2:
// - Task 0: Start times: [0, 5], Processing time: 4, Resource usage: 1
// - Task 1: Start times: [0, 5], Processing time: 2, Resource usage: 1
// - Task 2: Start times: [0, 5], Processing time: 4, Resource usage: 2
// We can infer that Task 0 and Task 1 execute at the same time
// while Task 2 will start after them
# use pumpkin_solver::termination::Indefinite;
# use pumpkin_solver::Solver;
# use pumpkin_solver::results::SatisfactionResult;
# use pumpkin_solver::constraints;
# use pumpkin_solver::constraints::Constraint;
# use crate::pumpkin_solver::results::ProblemSolution;
let solver = Solver::default();

let mut solver = Solver::default();

let start_0 = solver.new_bounded_integer(0, 4);
let start_1 = solver.new_bounded_integer(0, 4);
let start_2 = solver.new_bounded_integer(0, 5);

let start_times = [start_0, start_1, start_2];
let durations = [5, 2, 5];
let resource_requirements = [1, 1, 2];
let resource_capacity = 2;

solver
    .add_constraint(constraints::cumulative(
        start_times.clone(),
        durations.clone(),
        resource_requirements.clone(),
        resource_capacity,
    ))
    .post();

let mut termination = Indefinite;
let mut brancher = solver.default_brancher();

let result = solver.satisfy(&mut brancher, &mut termination);

// We check whether the result was feasible
if let SatisfactionResult::Satisfiable(solution) = result {
    let horizon = durations.iter().sum::<i32>();
    let start_times = [start_0, start_1, start_2];

    // Now we check whether the resource constraint is satisfied at each time-point t
    assert!((0..=horizon).all(|t| {
        // We gather all of the resource usages at the current time t
        let resource_usage_at_t = start_times
            .iter()
            .enumerate()
            .filter_map(|(task_index, start_time)| {
                if solution.get_integer_value(*start_time) <= t
                    && solution.get_integer_value(*start_time) + durations[task_index] > t
                {
                    Some(resource_requirements[task_index])
                } else {
                    None
                }
            })
            .sum::<i32>();
        // Then we check whether the resource usage at the current time point is lower than
        // the resource capacity
        resource_usage_at_t <= resource_capacity
    }));

    // Finally we check whether Task 2 starts after Task 0 and Task 1 and that Task 0 and
    // Task 1 overlap
    assert!(
        solution.get_integer_value(start_2)
            >= solution.get_integer_value(start_0) + durations[0]
            && solution.get_integer_value(start_2)
                >= solution.get_integer_value(start_1) + durations[1]
    );
    assert!(
        solution.get_integer_value(start_0)
            < solution.get_integer_value(start_1) + durations[1]
            && solution.get_integer_value(start_1)
                < solution.get_integer_value(start_0) + durations[0]
    );
}
```

# Bibliography
\[1\] S. Gay, R. Hartert, and P. Schaus, ‘Simple and scalable time-table filtering for the
cumulative constraint’, in Principles and Practice of Constraint Programming: 21st
International Conference, CP 2015, Cork, Ireland, August 31--September 4, 2015, Proceedings
21, 2015, pp. 149–157.

```rust
pub fn cumulative<StartTimes, Durations, ResourceRequirements>(start_times: StartTimes, durations: Durations, resource_requirements: ResourceRequirements, resource_capacity: i32) -> impl Constraint
where
    StartTimes: IntoIterator,
    <StartTimes as >::Item: IntegerVariable + Debug + ''static,
    <StartTimes as >::IntoIter: ExactSizeIterator,
    Durations: IntoIterator<Item = i32>,
    <Durations as >::IntoIter: ExactSizeIterator,
    ResourceRequirements: IntoIterator<Item = i32>,
    <ResourceRequirements as >::IntoIter: ExactSizeIterator { /* ... */ }
```

#### Function `cumulative_with_options`

Creates the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) constraint
with the provided [`CumulativeOptions`].

See the documentation of [`cumulative`] for more information about the constraint.

```rust
pub fn cumulative_with_options<StartTimes, Durations, ResourceRequirements>(start_times: StartTimes, durations: Durations, resource_requirements: ResourceRequirements, resource_capacity: i32, options: crate::propagators::CumulativeOptions) -> impl Constraint
where
    StartTimes: IntoIterator,
    <StartTimes as >::Item: IntegerVariable + Debug + ''static,
    <StartTimes as >::IntoIter: ExactSizeIterator,
    Durations: IntoIterator<Item = i32>,
    <Durations as >::IntoIter: ExactSizeIterator,
    ResourceRequirements: IntoIterator<Item = i32>,
    <ResourceRequirements as >::IntoIter: ExactSizeIterator { /* ... */ }
```

## Module `element`

```rust
pub(in ::constraints) mod element { /* ... */ }
```

### Functions

#### Function `element`

Creates the [element](https://sofdem.github.io/gccat/gccat/Celement.html) [`Constraint`] which states that `array[index] = rhs`.

```rust
pub fn element<ElementVar: IntegerVariable + ''static, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static, /* synthetic */ impl IntoIterator<Item = ElementVar>: IntoIterator<Item = ElementVar>, /* synthetic */ impl IntegerVariable + 'static: IntegerVariable + ''static>(index: impl IntegerVariable + ''static, array: impl IntoIterator<Item = ElementVar>, rhs: impl IntegerVariable + ''static) -> impl Constraint { /* ... */ }
```

### Traits

#### Trait `Constraint`

A [`Constraint`] is a relation over variables. It disqualifies certain partial assignments of
making it into a solution of the problem.

For example, the constraint `a = b` over two variables `a` and `b` only allows assignments to
`a` and `b` of the same value, and rejects any assignment where `a` and `b` differ.

```rust
pub trait Constraint {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `post`: Add the [`Constraint`] to the [`Solver`].
- `implied_by`: Add the half-reified version of the [`Constraint`] to the [`Solver`]; i.e. post the

##### Implementations

This trait is implemented for the following types:

- `EqualConstraint<Var>` with <Var>
- `NotEqualConstraint<Var>` with <Var>
- `Inequality<Var>` with <Var: IntegerVariable + ''static>
- `BooleanLessThanOrEqual`
- `BooleanEqual`
- `Clause`
- `Conjunction`
- `CumulativeConstraint<Var>` with <Var: IntegerVariable + ''static + Debug>
- `ConcretePropagator` with <ConcretePropagator>
- `Vec<C>` with <C: Constraint>

#### Trait `NegatableConstraint`

A [`Constraint`] which has a well-defined negation.

Having a negation means the [`Constraint`] can be fully reified; i.e., a constraint `C` can be
turned into `r <-> C` where `r` is a reification literal.

For example, the negation of the [`Constraint`] `a = b` is (well-)defined as `a != b`.

```rust
pub trait NegatableConstraint: Constraint {
    /* Associated items */
}
```

##### Required Items

###### Associated Types

- `NegatedConstraint`

###### Required Methods

- `negation`

##### Provided Methods

- ```rust
  fn reify(self: Self, solver: &mut Solver, reification_literal: Literal, tag: Option<NonZero<u32>>) -> Result<(), ConstraintOperationError>
where
    Self: Sized { /* ... */ }
  ```
  Add the reified version of the [`Constraint`] to the [`Solver`]; i.e. post the constraint

##### Implementations

This trait is implemented for the following types:

- `EqualConstraint<Var>` with <Var>
- `NotEqualConstraint<Var>` with <Var>
- `Inequality<Var>` with <Var: IntegerVariable + ''static>
- `Clause`
- `Conjunction`

### Re-exports

#### Re-export `all_different::*`

```rust
pub use all_different::*;
```

#### Re-export `arithmetic::*`

```rust
pub use arithmetic::*;
```

#### Re-export `boolean::*`

```rust
pub use boolean::*;
```

#### Re-export `clause::*`

```rust
pub use clause::*;
```

#### Re-export `constraint_poster::*`

```rust
pub use constraint_poster::*;
```

#### Re-export `cumulative::*`

```rust
pub use cumulative::*;
```

#### Re-export `element::*`

```rust
pub use element::*;
```

## Module `optimisation`

Contains structures related to optimissation.

```rust
pub mod optimisation { /* ... */ }
```

### Modules

## Module `linear_sat_unsat`

```rust
pub mod linear_sat_unsat { /* ... */ }
```

### Types

#### Struct `LinearSatUnsat`

Implements the linear SAT-UNSAT (LSU) optimisation procedure.

```rust
pub struct LinearSatUnsat<Var, Callback> {
    pub(in ::optimisation::linear_sat_unsat) direction: crate::optimisation::OptimisationDirection,
    pub(in ::optimisation::linear_sat_unsat) objective: Var,
    pub(in ::optimisation::linear_sat_unsat) solution_callback: Callback,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `direction` | `crate::optimisation::OptimisationDirection` |  |
| `objective` | `Var` |  |
| `solution_callback` | `Callback` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(direction: OptimisationDirection, objective: Var, solution_callback: Callback) -> Self { /* ... */ }
  ```
  Create a new instance of [`LinearSatUnsat`].

- ```rust
  pub(in ::optimisation::linear_sat_unsat) fn strengthen</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &mut Self, objective_variable: &impl IntegerVariable, best_objective_value: i64, solver: &mut Solver) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Given the current objective value `best_objective_value`, it adds a constraint specifying

- ```rust
  pub(in ::optimisation::linear_sat_unsat) fn debug_bound_change</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, objective_variable: &impl IntegerVariable, best_objective_value: i64, solver: &Solver) { /* ... */ }
  ```

###### Trait Implementations

- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> LinearSatUnsat<Var, Callback> { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Copy**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **OptimisationProcedure**
  - ```rust
    fn optimise</* synthetic */ impl TerminationCondition: TerminationCondition>(self: &mut Self, brancher: &mut B, termination: &mut impl TerminationCondition, solver: &mut Solver) -> OptimisationResult { /* ... */ }
    ```

  - ```rust
    fn on_solution_callback(self: &Self, solver: &Solver, solution: SolutionReference<''_>, brancher: &B) { /* ... */ }
    ```

- **Freeze**
- **Unpin**
- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

## Module `linear_unsat_sat`

```rust
pub mod linear_unsat_sat { /* ... */ }
```

### Types

#### Struct `LinearUnsatSat`

Implements the linear UNSAT-SAT (LUS) optimisation procedure.

```rust
pub struct LinearUnsatSat<Var, Callback> {
    pub(in ::optimisation::linear_unsat_sat) direction: crate::optimisation::OptimisationDirection,
    pub(in ::optimisation::linear_unsat_sat) objective: Var,
    pub(in ::optimisation::linear_unsat_sat) solution_callback: Callback,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `direction` | `crate::optimisation::OptimisationDirection` |  |
| `objective` | `Var` |  |
| `solution_callback` | `Callback` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(direction: OptimisationDirection, objective: Var, solution_callback: Callback) -> Self { /* ... */ }
  ```
  Create a new instance of [`LinearUnsatSat`].

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Unpin**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Copy**
- **Send**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **IntoEither**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> LinearUnsatSat<Var, Callback> { /* ... */ }
    ```

- **OptimisationProcedure**
  - ```rust
    fn optimise</* synthetic */ impl TerminationCondition: TerminationCondition>(self: &mut Self, brancher: &mut B, termination: &mut impl TerminationCondition, solver: &mut Solver) -> OptimisationResult { /* ... */ }
    ```

  - ```rust
    fn on_solution_callback(self: &Self, solver: &Solver, solution: SolutionReference<''_>, brancher: &B) { /* ... */ }
    ```

- **RefUnwindSafe**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **UnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `solution_callback`

```rust
pub mod solution_callback { /* ... */ }
```

### Traits

#### Trait `SolutionCallback`

```rust
pub trait SolutionCallback<B: Brancher> {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `on_solution_callback`

##### Implementations

This trait is implemented for the following types:

- `T` with <T: Fn(&crate::Solver, crate::results::SolutionReference<''_>, &B), B: Brancher>
- `Option<T>` with <T: SolutionCallback<B>, B: Brancher>

### Types

#### Enum `OptimisationStrategy`

The type of search which is performed by the solver.

```rust
pub enum OptimisationStrategy {
    LinearSatUnsat,
    LinearUnsatSat,
}
```

##### Variants

###### `LinearSatUnsat`

Linear SAT-UNSAT - Starts with a satisfiable solution and tightens the bound on the
objective variable until an UNSAT result is reached. Can be seen as upper-bounding search.

###### `LinearUnsatSat`

Linear UNSAT-SAT - Starts with an unsatisfiable solution and tightens the bound on the
objective variable until a SAT result is reached. Can be seen as lower-bounding search.

##### Implementations

###### Trait Implementations

- **Sync**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **ValueEnum**
  - ```rust
    fn value_variants<''a>() -> &''a [Self] { /* ... */ }
    ```

  - ```rust
    fn to_possible_value<''a>(self: &Self) -> ::std::option::Option<clap::builder::PossibleValue> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Statistic**
  - ```rust
    fn log(self: &Self, statistic_logger: StatisticLogger) { /* ... */ }
    ```

- **Clone**
  - ```rust
    fn clone(self: &Self) -> OptimisationStrategy { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Copy**
- **RefUnwindSafe**
- **Default**
  - ```rust
    fn default() -> OptimisationStrategy { /* ... */ }
    ```

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **ToString**
  - ```rust
    fn to_string(self: &Self) -> String { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **IntoEither**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Display**
  - ```rust
    fn fmt(self: &Self, f: &mut std::fmt::Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

#### Enum `OptimisationDirection`

The direction of the optimisation, either maximising or minimising.

```rust
pub enum OptimisationDirection {
    Maximise,
    Minimise,
}
```

##### Variants

###### `Maximise`

###### `Minimise`

##### Implementations

###### Trait Implementations

- **RefUnwindSafe**
- **Send**
- **IntoEither**
- **Freeze**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Copy**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **PartialEq**
  - ```rust
    fn eq(self: &Self, other: &OptimisationDirection) -> bool { /* ... */ }
    ```

- **StructuralPartialEq**
- **Sync**
- **Unpin**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> OptimisationDirection { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

### Traits

#### Trait `OptimisationProcedure`

```rust
pub trait OptimisationProcedure<B: Brancher, Callback: SolutionCallback<B>> {
    /* Associated items */
}
```

> This trait is not object-safe and cannot be used in dynamic trait objects.

##### Required Items

###### Required Methods

- `optimise`
- `on_solution_callback`

##### Provided Methods

- ```rust
  fn update_best_solution_and_process</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, objective_multiplier: i32, objective_variable: &impl IntegerVariable, best_objective_value: &mut i64, best_solution: &mut Solution, brancher: &mut B, solver: &Solver) { /* ... */ }
  ```
  Processes a solution when it is found, it consists of the following procedure:

- ```rust
  fn internal_process_solution(self: &Self, solution: &Solution, brancher: &mut B, solver: &Solver) { /* ... */ }
  ```

##### Implementations

This trait is implemented for the following types:

- `LinearSatUnsat<Var, Callback>` with <Var, Callback, B>
- `LinearUnsatSat<Var, Callback>` with <Var, B, Callback>

## Module `proof`

Pumpkin supports proof logging for SAT and CP problems. During search, the solver produces a
[`ProofLog`], which is a list of deductions made by the solver.

Proof logging for CP is supported in the DRCP format. This format explicitly supports usage
where the solver logs a proof scaffold which later processed into a full proof after search
has completed.

```rust
pub mod proof { /* ... */ }
```

### Modules

## Module `dimacs`

```rust
pub(in ::proof) mod dimacs { /* ... */ }
```

### Types

#### Struct `DimacsProof`

```rust
pub(crate) struct DimacsProof<W: Write> {
    pub(in ::proof::dimacs) writer: std::io::BufWriter<W>,
    pub(in ::proof::dimacs) next_clause_id: std::num::NonZeroU64,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `writer` | `std::io::BufWriter<W>` |  |
| `next_clause_id` | `std::num::NonZeroU64` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(writer: W) -> DimacsProof<W> { /* ... */ }
  ```

- ```rust
  pub(crate) fn learned_clause</* synthetic */ impl IntoIterator<Item = Predicate>: IntoIterator<Item = Predicate>>(self: &mut Self, predicates: impl IntoIterator<Item = Predicate>, variable_names: &VariableNames) -> std::io::Result<NonZeroU64> { /* ... */ }
  ```

###### Trait Implementations

- **Freeze**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Unpin**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **UnwindSafe**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

## Module `finalizer`

Responsible for finalizing the proof in the solver.

The other resolvers are not fit for this job.

```rust
pub(in ::proof) mod finalizer { /* ... */ }
```

### Types

#### Struct `FinalizingContext`

```rust
pub(crate) struct FinalizingContext<''a> {
    pub(crate) conflict: crate::predicates::PropositionalConjunction,
    pub(crate) propagators: &''a mut crate::engine::propagation::store::PropagatorStore,
    pub(crate) proof_log: &''a mut super::ProofLog,
    pub(crate) unit_nogood_step_ids: &''a std::collections::HashMap<crate::predicates::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>,
    pub(crate) assignments: &''a assignments::Assignments,
    pub(crate) reason_store: &''a mut crate::engine::reason::ReasonStore,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `conflict` | `crate::predicates::PropositionalConjunction` |  |
| `propagators` | `&''a mut crate::engine::propagation::store::PropagatorStore` |  |
| `proof_log` | `&''a mut super::ProofLog` |  |
| `unit_nogood_step_ids` | `&''a std::collections::HashMap<crate::predicates::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>` |  |
| `assignments` | `&''a assignments::Assignments` |  |
| `reason_store` | `&''a mut crate::engine::reason::ReasonStore` |  |

##### Implementations

###### Trait Implementations

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Freeze**
- **IntoEither**
- **RefUnwindSafe**
- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

#### Struct `RootExplanationContext`

```rust
pub(crate) struct RootExplanationContext<''a> {
    pub(crate) propagators: &''a mut crate::engine::propagation::store::PropagatorStore,
    pub(crate) proof_log: &''a mut super::ProofLog,
    pub(crate) unit_nogood_step_ids: &''a std::collections::HashMap<crate::predicates::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>,
    pub(crate) assignments: &''a assignments::Assignments,
    pub(crate) reason_store: &''a mut crate::engine::reason::ReasonStore,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `propagators` | `&''a mut crate::engine::propagation::store::PropagatorStore` |  |
| `proof_log` | `&''a mut super::ProofLog` |  |
| `unit_nogood_step_ids` | `&''a std::collections::HashMap<crate::predicates::Predicate, drcp_format::steps::StepId, fnv::FnvBuildHasher>` |  |
| `assignments` | `&''a assignments::Assignments` |  |
| `reason_store` | `&''a mut crate::engine::reason::ReasonStore` |  |

##### Implementations

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **RefUnwindSafe**
- **UnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **IntoEither**
- **Freeze**
- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Send**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

### Functions

#### Function `finalize_proof`

Finalizes the proof by introducing inferences used to derive root-level unsatisfiability. This
happens by recursively going through the implication graph to explain any predicate that does
not have a nogood step id yet.

This should only include implicit propagations done through the [`Assignments`] struct. If a
predicate is propagated by a propagator, it would have been logged as a root-level propagation
by the solver prior to reaching this function.

```rust
pub(crate) fn finalize_proof(context: FinalizingContext<''_>) { /* ... */ }
```

#### Function `explain_root_assignment`

Explain why a given predicate is true. We assume that `predicate` is true at the root.

```rust
pub(crate) fn explain_root_assignment(context: &mut RootExplanationContext<''_>, predicate: crate::predicates::Predicate) { /* ... */ }
```

## Module `proof_literals`

```rust
pub(in ::proof) mod proof_literals { /* ... */ }
```

### Types

#### Struct `ProofLiterals`

```rust
pub(crate) struct ProofLiterals {
    pub(in ::proof::proof_literals) variables: std::collections::HashMap<crate::predicates::Predicate, std::num::NonZeroU32, fnv::FnvBuildHasher>,
    pub(in ::proof::proof_literals) reification_domains: std::collections::HashMap<crate::variables::DomainId, crate::predicates::Predicate, fnv::FnvBuildHasher>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `variables` | `std::collections::HashMap<crate::predicates::Predicate, std::num::NonZeroU32, fnv::FnvBuildHasher>` | All the predicates seen in the proof log.<br><br>The predicates in the map are only LessThanEqual or Equal. The other variants are negations<br>of the predicates in the map. |
| `reification_domains` | `std::collections::HashMap<crate::variables::DomainId, crate::predicates::Predicate, fnv::FnvBuildHasher>` | Maps the domain id of a 0-1 integer `x` to the predicate `p` that it reifies:<br>`[x == 1] <-> p`.<br><br>Used in substituting the reification domain with the predicate when logging reasons. |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn write</* synthetic */ impl Write: Write>(self: Self, sink: impl Write, variable_names: &VariableNames) -> std::io::Result<()> { /* ... */ }
  ```

- ```rust
  pub(crate) fn reify_predicate(self: &mut Self, literal: Literal, predicate: Predicate) { /* ... */ }
  ```
  Given a literal, whenever it shows up in a proof step, substitute it with the provided

- ```rust
  pub(in ::proof::proof_literals) fn get_underlying_predicate(self: &Self, predicate: Predicate) -> Option<Predicate> { /* ... */ }
  ```
  The given predicate is a predicate over a literal. This function gets the associated

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Sync**
- **Send**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> ProofLiterals { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **UnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **LiteralCodeProvider**
  - ```rust
    fn to_code(self: &mut Self, literal: <Self as >::Literal) -> NonZeroI32 { /* ... */ }
    ```

- **Unpin**
- **IntoEither**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

### Functions

#### Function `predicate_to_atomic`

```rust
pub(in ::proof::proof_literals) fn predicate_to_atomic(predicate: crate::predicates::Predicate, variable_names: &crate::variable_names::VariableNames) -> drcp_format::AtomicConstraint<&str> { /* ... */ }
```

### Types

#### Struct `ProofLog`

A proof log which logs the proof steps necessary to prove unsatisfiability or optimality. We
allow the following types of proofs:
- A CP proof log - This can be created using [`ProofLog::cp`].
- A DIMACS proof log - This can be created using [`ProofLog::dimacs`].

When a proof log should not be generated, use the implementation of [`Default`].

```rust
pub struct ProofLog {
    pub(in ::proof) internal_proof: Option<ProofImpl>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `internal_proof` | `Option<ProofImpl>` |  |

##### Implementations

###### Methods

- ```rust
  pub fn cp(file_path: &Path, format: Format, log_inferences: bool, log_hints: bool) -> std::io::Result<ProofLog> { /* ... */ }
  ```
  Create a CP proof logger.

- ```rust
  pub fn dimacs(file_path: &Path) -> std::io::Result<ProofLog> { /* ... */ }
  ```
  Create a dimacs proof logger.

- ```rust
  pub(crate) fn log_inference</* synthetic */ impl IntoIterator<Item = Predicate>: IntoIterator<Item = Predicate>>(self: &mut Self, constraint_tag: Option<NonZero<u32>>, premises: impl IntoIterator<Item = Predicate>, propagated: Option<Predicate>) -> std::io::Result<NonZeroU64> { /* ... */ }
  ```
  Log an inference to the proof.

- ```rust
  pub(crate) fn add_propagation(self: &mut Self, step_id: NonZeroU64) { /* ... */ }
  ```
  Record that a step has been used in the derivation of the next nogood.

- ```rust
  pub(crate) fn log_learned_clause</* synthetic */ impl IntoIterator<Item = Predicate>: IntoIterator<Item = Predicate>>(self: &mut Self, literals: impl IntoIterator<Item = Predicate>, variable_names: &VariableNames) -> std::io::Result<NonZeroU64> { /* ... */ }
  ```
  Log a learned clause to the proof.

- ```rust
  pub(crate) fn unsat(self: Self, variable_names: &VariableNames) -> std::io::Result<()> { /* ... */ }
  ```

- ```rust
  pub(crate) fn optimal(self: Self, objective_bound: Predicate, variable_names: &VariableNames) -> std::io::Result<()> { /* ... */ }
  ```

- ```rust
  pub(crate) fn is_logging_inferences(self: &Self) -> bool { /* ... */ }
  ```

- ```rust
  pub(crate) fn reify_predicate(self: &mut Self, literal: Literal, predicate: Predicate) { /* ... */ }
  ```

###### Trait Implementations

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **IntoEither**
- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> ProofLog { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Sync**
- **Unpin**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

#### Enum `ProofImpl`

```rust
pub(in ::proof) enum ProofImpl {
    CpProof {
        writer: drcp_format::writer::ProofWriter<std::fs::File, self::proof_literals::ProofLiterals>,
        log_inferences: bool,
        definitions_path: std::path::PathBuf,
        propagation_order_hint: Option<Vec<std::num::NonZeroU64>>,
    },
    DimacsProof(self::dimacs::DimacsProof<std::fs::File>),
}
```

##### Variants

###### `CpProof`

Fields:

| Name | Type | Documentation |
|------|------|---------------|
| `writer` | `drcp_format::writer::ProofWriter<std::fs::File, self::proof_literals::ProofLiterals>` |  |
| `log_inferences` | `bool` |  |
| `definitions_path` | `std::path::PathBuf` |  |
| `propagation_order_hint` | `Option<Vec<std::num::NonZeroU64>>` |  |

###### `DimacsProof`

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `self::dimacs::DimacsProof<std::fs::File>` |  |

##### Implementations

###### Trait Implementations

- **Freeze**
- **Unpin**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Sync**
- **Send**
- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

### Constants and Statics

#### Constant `DUMMY_STEP_ID`

A dummy proof step ID. Used when there is proof logging is not enabled.

```rust
pub(in ::proof) const DUMMY_STEP_ID: std::num::NonZeroU64 = _;
```

### Re-exports

#### Re-export `Format`

```rust
pub use drcp_format::Format;
```

## Module `statistics`

Contains structures related to the statistic logging of the [`Solver`]

```rust
pub mod statistics { /* ... */ }
```

### Modules

## Module `statistic_logger`

```rust
pub(crate) mod statistic_logger { /* ... */ }
```

### Types

#### Struct `StatisticLogger`

Responsible for logging the statistics with the provided prefix; currently used when logging
the statistics of propagators.

```rust
pub struct StatisticLogger {
    pub(in ::statistics::statistic_logger) name_prefix: String,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `name_prefix` | `String` | The prefix which will be attached to the statistic name |

##### Implementations

###### Methods

- ```rust
  pub fn new<Input: IntoIterator<Item = impl Display>, /* synthetic */ impl Display: Display>(name_prefix: Input) -> Self { /* ... */ }
  ```

- ```rust
  pub fn attach_to_prefix</* synthetic */ impl Display: Display>(self: &Self, addition_to_prefix: impl Display) -> Self { /* ... */ }
  ```
  Attaches the provided `addition_to_prefix` to the stored internal prefix and returns a new

- ```rust
  pub fn log_statistic</* synthetic */ impl Display: Display>(self: &Self, value: impl Display) { /* ... */ }
  ```

###### Trait Implementations

- **Sync**
- **ToOwned**
  - ```rust
    fn to_owned(self: &Self) -> T { /* ... */ }
    ```

  - ```rust
    fn clone_into(self: &Self, target: &mut T) { /* ... */ }
    ```

- **RefUnwindSafe**
- **CloneToUninit**
  - ```rust
    unsafe fn clone_to_uninit(self: &Self, dest: *mut u8) { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **Send**
- **Default**
  - ```rust
    fn default() -> StatisticLogger { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **UnwindSafe**
- **Freeze**
- **Unpin**
- **Clone**
  - ```rust
    fn clone(self: &Self) -> StatisticLogger { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

## Module `statistic_logging`

Responsible for behaviour related to logging statistics with a specific pre-fix and closing
lines.

```rust
pub(crate) mod statistic_logging { /* ... */ }
```

### Types

#### Struct `StatisticOptions`

The options for statistic logging containing the statistic prefix, the (optional) line which is
printed after the statistics, and the (optional) casing of the statistics.

```rust
pub struct StatisticOptions<''a> {
    pub(in ::statistics::statistic_logging) statistic_prefix: &''a str,
    pub(in ::statistics::statistic_logging) after_statistics: Option<&''a str>,
    pub(in ::statistics::statistic_logging) statistics_casing: Option<convert_case::Case>,
    pub(in ::statistics::statistic_logging) statistics_writer: Box<dyn Write + Send + Sync>,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `statistic_prefix` | `&''a str` |  |
| `after_statistics` | `Option<&''a str>` |  |
| `statistics_casing` | `Option<convert_case::Case>` |  |
| `statistics_writer` | `Box<dyn Write + Send + Sync>` |  |

##### Implementations

###### Trait Implementations

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **RefUnwindSafe**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **IntoEither**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut Formatter<''_>) -> std::fmt::Result { /* ... */ }
    ```

- **Freeze**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Unpin**
- **Send**
- **UnwindSafe**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

### Functions

#### Function `configure_statistic_logging`

Configures the logging of the statistics.

It specifies the (optional) prefix and a closing line (postfix) which
can be written to the writer after all of the statistics have been logged.
It also specifies the writer to be used for writing statistics. In case no writer is specified,
stdout will be used. Statistics will only be written if `log_statistics` is true.

```rust
pub fn configure_statistic_logging(prefix: &''static str, after: Option<&''static str>, casing: Option<convert_case::Case>, writer: Option<Box<dyn Write + Send + Sync>>) { /* ... */ }
```

#### Function `log_statistic`

Logs the provided statistic with name `name` and value `value`. At the moment it will log in
the format `STATISTIC_PREFIX NAME=VALUE`.

```rust
pub fn log_statistic</* synthetic */ impl Display: Display, /* synthetic */ impl Display: Display>(name: impl Display, value: impl Display) { /* ... */ }
```

#### Function `log_statistic_postfix`

Logs the postfix of the statistics (if it has been set).

Certain formats (e.g. the [MiniZinc](https://www.minizinc.org/doc-2.7.6/en/fzn-spec.html#statistics-output)
output format) require that a block of statistics is followed by a closing line; this
function outputs this closing line **if** it is configued.

```rust
pub fn log_statistic_postfix() { /* ... */ }
```

#### Function `should_log_statistics`

Returns whether or not statistics should be logged by determining whether the
[`StatisticOptions`] have been configured.

```rust
pub fn should_log_statistics() -> bool { /* ... */ }
```

### Constants and Statics

#### Static `STATISTIC_OPTIONS`

```rust
pub(in ::statistics::statistic_logging) static STATISTIC_OPTIONS: std::sync::OnceLock<std::sync::RwLock<StatisticOptions<''_>>> = _;
```

### Traits

#### Trait `Statistic`

A simple trait for defining a loggable statistic.

See [`create_statistics_struct`] for creating a statistic struct automatically!

```rust
pub trait Statistic {
    /* Associated items */
}
```

##### Required Items

###### Required Methods

- `log`: Logs the [`Statistic`] using the provided [`StatisticLogger`].

##### Implementations

This trait is implemented for the following types:

- `SolverStatistics`
- `EngineStatistics`
- `LearnedClauseStatistics`
- `AutonomousSearchStatistics`
- `Value` with <Value: Display>

### Re-exports

#### Re-export `StatisticLogger`

```rust
pub use statistic_logger::StatisticLogger;
```

#### Re-export `configure_statistic_logging`

```rust
pub use statistic_logging::configure_statistic_logging;
```

#### Re-export `log_statistic`

```rust
pub use statistic_logging::log_statistic;
```

#### Re-export `log_statistic_postfix`

```rust
pub use statistic_logging::log_statistic_postfix;
```

#### Re-export `should_log_statistics`

```rust
pub use statistic_logging::should_log_statistics;
```

#### Re-export `StatisticOptions`

```rust
pub use statistic_logging::StatisticOptions;
```

## Module `api`

```rust
pub(crate) mod api { /* ... */ }
```

### Modules

## Module `outputs`

```rust
pub(in ::api) mod outputs { /* ... */ }
```

### Modules

## Module `solution_iterator`

Contains the structures corresponding to solution iterations.

```rust
pub mod solution_iterator { /* ... */ }
```

### Types

#### Struct `SolutionIterator`

A struct which allows the retrieval of multiple solutions to a satisfaction problem.

```rust
pub struct SolutionIterator<''solver, ''brancher, ''termination, B, T> {
    pub(in ::api::outputs::solution_iterator) solver: &''solver mut crate::Solver,
    pub(in ::api::outputs::solution_iterator) brancher: &''brancher mut B,
    pub(in ::api::outputs::solution_iterator) termination: &''termination mut T,
    pub(in ::api::outputs::solution_iterator) next_blocking_clause: Option<Vec<crate::predicates::Predicate>>,
    pub(in ::api::outputs::solution_iterator) has_solution: bool,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `solver` | `&''solver mut crate::Solver` |  |
| `brancher` | `&''brancher mut B` |  |
| `termination` | `&''termination mut T` |  |
| `next_blocking_clause` | `Option<Vec<crate::predicates::Predicate>>` |  |
| `has_solution` | `bool` |  |

##### Implementations

###### Methods

- ```rust
  pub(crate) fn new(solver: &''solver mut Solver, brancher: &''brancher mut B, termination: &''termination mut T) -> Self { /* ... */ }
  ```

- ```rust
  pub fn next_solution(self: &mut Self) -> IteratedSolution<''_, B> { /* ... */ }
  ```
  Find a new solution by blocking the previous solution from being found. Also calls the

###### Trait Implementations

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Freeze**
- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **RefUnwindSafe**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Send**
- **Unpin**
- **IntoEither**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **UnwindSafe**
#### Enum `IteratedSolution`

**Attributes:**

- `#[allow(clippy::large_enum_variant, reason =
"these will not be stored in bulk, so this is not an issue")]`

Enum which specifies the status of the call to [`SolutionIterator::next_solution`].

```rust
pub enum IteratedSolution<''a, B> {
    Solution(crate::results::Solution, &''a crate::Solver, &''a B),
    Finished,
    Unknown,
    Unsatisfiable,
}
```

##### Variants

###### `Solution`

A new solution was identified.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::results::Solution` |  |
| 1 | `&''a crate::Solver` |  |
| 2 | `&''a B` |  |

###### `Finished`

No more solutions exist.

###### `Unknown`

The solver was terminated during search.

###### `Unsatisfiable`

There exists no solution

##### Implementations

###### Trait Implementations

- **UnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Send**
- **Freeze**
- **RefUnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Sync**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

### Functions

#### Function `get_blocking_clause`

Creates a clause which prevents the current solution from occurring again by going over the
defined output variables and creating a clause which prevents those values from
being assigned.

This method is used when attempting to find multiple solutions.

```rust
pub(in ::api::outputs::solution_iterator) fn get_blocking_clause(solution: &crate::results::Solution) -> Vec<crate::predicates::Predicate> { /* ... */ }
```

## Module `unsatisfiable`

Contains the representation of a unsatisfiable solution.

```rust
pub mod unsatisfiable { /* ... */ }
```

### Types

#### Struct `UnsatisfiableUnderAssumptions`

A struct which allows the retrieval of an unsatisfiable core consisting of the provided
assumptions passed to the initial [`Solver::satisfy_under_assumptions`].

Note that when this struct is dropped (using [`Drop`]) then the [`Solver`] is reset.

```rust
pub struct UnsatisfiableUnderAssumptions<''solver, ''brancher, B: Brancher> {
    pub(crate) solver: &''solver mut constraint_satisfaction_solver::ConstraintSatisfactionSolver,
    pub(crate) brancher: &''brancher mut B,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `solver` | `&''solver mut constraint_satisfaction_solver::ConstraintSatisfactionSolver` |  |
| `brancher` | `&''brancher mut B` |  |

##### Implementations

###### Methods

- ```rust
  pub fn new(solver: &''solver mut ConstraintSatisfactionSolver, brancher: &''brancher mut B) -> Self { /* ... */ }
  ```

- ```rust
  pub fn extract_core(self: &mut Self) -> Box<[Predicate]> { /* ... */ }
  ```
  Extract an unsatisfiable core in terms of the assumptions.

###### Trait Implementations

- **Drop**
  - ```rust
    fn drop(self: &mut Self) { /* ... */ }
    ```

- **Sync**
- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **IntoEither**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **RefUnwindSafe**
- **Send**
- **Freeze**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Unpin**
- **UnwindSafe**
### Types

#### Enum `SatisfactionResult`

**Attributes:**

- `#[allow(clippy::large_enum_variant, reason =
"these will not be stored in bulk, so this is not an issue")]`

The result of a call to [`Solver::satisfy`].

```rust
pub enum SatisfactionResult {
    Satisfiable(crate::basic_types::Solution),
    Unsatisfiable,
    Unknown,
}
```

##### Variants

###### `Satisfiable`

Indicates that a solution was found and provides the corresponding [`Solution`].

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::Solution` |  |

###### `Unsatisfiable`

Indicates that there is no solution to the satisfaction problem.

###### `Unknown`

Indicates that it is not known whether a solution exists. This is likely due to a
[`TerminationCondition`] triggering.

##### Implementations

###### Trait Implementations

- **Sync**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Send**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **UnwindSafe**
- **IntoEither**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **RefUnwindSafe**
- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

#### Enum `SatisfactionResultUnderAssumptions`

**Attributes:**

- `#[allow(clippy::large_enum_variant, reason =
"these will not be stored in bulk, so this is not an issue")]`

The result of a call to [`Solver::satisfy_under_assumptions`].

```rust
pub enum SatisfactionResultUnderAssumptions<''solver, ''brancher, B: Brancher> {
    Satisfiable(crate::basic_types::Solution),
    UnsatisfiableUnderAssumptions(self::unsatisfiable::UnsatisfiableUnderAssumptions<''solver, ''brancher, B>),
    Unsatisfiable,
    Unknown,
}
```

##### Variants

###### `Satisfiable`

Indicates that a solution was found and provides the corresponding [`Solution`].

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::Solution` |  |

###### `UnsatisfiableUnderAssumptions`

Indicates that there is no solution to the satisfaction problem due to the provided
assumptions. It returns an [`UnsatisfiableUnderAssumptions`] which can be used to retrieve
an unsatisfiable core.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `self::unsatisfiable::UnsatisfiableUnderAssumptions<''solver, ''brancher, B>` |  |

###### `Unsatisfiable`

Indicates that there is no solution to the satisfaction problem.

###### `Unknown`

Indicates that it is not known whether a solution exists. This is likely due to a
[`TerminationCondition`] triggering.

##### Implementations

###### Trait Implementations

- **Unpin**
- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **UnwindSafe**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Sync**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Freeze**
- **Send**
- **RefUnwindSafe**
- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **IntoEither**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

#### Enum `OptimisationResult`

The result of a call to [`Solver::optimise`].

```rust
pub enum OptimisationResult {
    Optimal(crate::basic_types::Solution),
    Satisfiable(crate::basic_types::Solution),
    Unsatisfiable,
    Unknown,
}
```

##### Variants

###### `Optimal`

Indicates that an optimal solution has been found and proven to be optimal. It provides an
instance of [`Solution`] which contains the optimal solution.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::Solution` |  |

###### `Satisfiable`

Indicates that a solution was found and provides an instance of [`Solution`] which contains
best known solution by the solver.

Fields:

| Index | Type | Documentation |
|-------|------|---------------|
| 0 | `crate::basic_types::Solution` |  |

###### `Unsatisfiable`

Indicates that there is no solution to the problem.

###### `Unknown`

Indicates that it is not known whether a solution exists. This is likely due to a
[`TerminationCondition`] triggering.

##### Implementations

###### Trait Implementations

- **IntoEither**
- **Freeze**
- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Sync**
- **UnwindSafe**
- **Unpin**
- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **DowncastSync**
  - ```rust
    fn into_any_arc(self: Arc<T>) -> Arc<dyn Any + Send + Sync> { /* ... */ }
    ```

- **Send**
- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **RefUnwindSafe**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

### Re-exports

#### Re-export `ProblemSolution`

```rust
pub use crate::basic_types::ProblemSolution;
```

#### Re-export `SolutionReference`

```rust
pub use crate::basic_types::SolutionReference;
```

## Module `solver`

```rust
pub(crate) mod solver { /* ... */ }
```

### Types

#### Struct `Solver`

The main interaction point which allows the creation of variables, the addition of constraints,
and solving problems.


# Creating Variables
As stated in [`crate::variables`], we can create two types of variables: propositional variables
and integer variables.

```rust
# use pumpkin_solver::Solver;
# use crate::pumpkin_solver::variables::TransformableVariable;
let mut solver = Solver::default();

// Integer Variables

// We can create an integer variable with a domain in the range [0, 10]
let integer_between_bounds = solver.new_bounded_integer(0, 10);

// We can also create such a variable with a name
let named_integer_between_bounds = solver.new_named_bounded_integer(0, 10, "x");

// We can also create an integer variable with a non-continuous domain in the follow way
let mut sparse_integer = solver.new_sparse_integer(vec![0, 3, 5]);

// We can also create such a variable with a name
let named_sparse_integer = solver.new_named_sparse_integer(vec![0, 3, 5], "y");

// Additionally, we can also create an affine view over a variable with both a scale and an offset (or either)
let view_over_integer = integer_between_bounds.scaled(-1).offset(15);


// Propositional Variable

// We can create a literal
let literal = solver.new_literal();

// We can also create such a variable with a name
let named_literal = solver.new_named_literal("z");

// We can also get the predicate from the literal
let true_predicate = literal.get_true_predicate();

// We can also create an iterator of new literals and get a number of them at once
let list_of_5_literals = solver.new_literals().take(5).collect::<Vec<_>>();
assert_eq!(list_of_5_literals.len(), 5);
```

# Using the Solver
For examples on how to use the solver, see the [root-level crate documentation](crate) or [one of these examples](https://github.com/ConSol-Lab/Pumpkin/tree/master/pumpkin-lib/examples).

```rust
pub struct Solver {
    pub(crate) satisfaction_solver: constraint_satisfaction_solver::ConstraintSatisfactionSolver,
    pub(in ::api::solver) true_literal: crate::engine::variables::Literal,
}
```

##### Fields

| Name | Type | Documentation |
|------|------|---------------|
| `satisfaction_solver` | `constraint_satisfaction_solver::ConstraintSatisfactionSolver` | The internal [`ConstraintSatisfactionSolver`] which is used to solve the problems. |
| `true_literal` | `crate::engine::variables::Literal` |  |

##### Implementations

###### Methods

- ```rust
  pub fn with_options(solver_options: SolverOptions) -> Self { /* ... */ }
  ```
  Creates a solver with the provided [`SolverOptions`].

- ```rust
  pub fn log_statistics_with_objective(self: &Self, objective_value: i64) { /* ... */ }
  ```
  Logs the statistics currently present in the solver with the provided objective value.

- ```rust
  pub fn log_statistics(self: &Self) { /* ... */ }
  ```
  Logs the statistics currently present in the solver.

- ```rust
  pub fn get_solution_reference(self: &Self) -> SolutionReference<''_> { /* ... */ }
  ```

- ```rust
  pub fn get_literal_value(self: &Self, literal: Literal) -> Option<bool> { /* ... */ }
  ```
  Get the value of the given [`Literal`] at the root level (after propagation), which could be

- ```rust
  pub fn lower_bound</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, variable: &impl IntegerVariable) -> i32 { /* ... */ }
  ```
  Get the lower-bound of the given [`IntegerVariable`] at the root level (after propagation).

- ```rust
  pub fn upper_bound</* synthetic */ impl IntegerVariable: IntegerVariable>(self: &Self, variable: &impl IntegerVariable) -> i32 { /* ... */ }
  ```
  Get the upper-bound of the given [`IntegerVariable`] at the root level (after propagation).

- ```rust
  pub fn new_literals(self: &mut Self) -> impl Iterator<Item = Literal> + ''_ { /* ... */ }
  ```
  Returns an infinite iterator of positive literals of new variables. The new variables will

- ```rust
  pub fn new_literal(self: &mut Self) -> Literal { /* ... */ }
  ```
  Create a fresh propositional variable and return the literal with positive polarity.

- ```rust
  pub fn new_literal_for_predicate(self: &mut Self, predicate: Predicate) -> Literal { /* ... */ }
  ```

- ```rust
  pub fn new_named_literal</* synthetic */ impl Into<String>: Into<String>>(self: &mut Self, name: impl Into<String>) -> Literal { /* ... */ }
  ```
  Create a fresh propositional variable with a given name and return the literal with positive

- ```rust
  pub fn get_true_literal(self: &Self) -> Literal { /* ... */ }
  ```
  Get a literal which is always true.

- ```rust
  pub fn get_false_literal(self: &Self) -> Literal { /* ... */ }
  ```
  Get a literal which is always false.

- ```rust
  pub fn new_bounded_integer(self: &mut Self, lower_bound: i32, upper_bound: i32) -> DomainId { /* ... */ }
  ```
  Create a new integer variable with the given bounds.

- ```rust
  pub fn new_named_bounded_integer</* synthetic */ impl Into<String>: Into<String>>(self: &mut Self, lower_bound: i32, upper_bound: i32, name: impl Into<String>) -> DomainId { /* ... */ }
  ```
  Create a new named integer variable with the given bounds.

- ```rust
  pub fn new_sparse_integer</* synthetic */ impl Into<Vec<i32>>: Into<Vec<i32>>>(self: &mut Self, values: impl Into<Vec<i32>>) -> DomainId { /* ... */ }
  ```
  Create a new integer variable which has a domain of predefined values. We remove duplicates

- ```rust
  pub fn new_named_sparse_integer</* synthetic */ impl Into<Vec<i32>>: Into<Vec<i32>>, /* synthetic */ impl Into<String>: Into<String>>(self: &mut Self, values: impl Into<Vec<i32>>, name: impl Into<String>) -> DomainId { /* ... */ }
  ```
  Create a new named integer variable which has a domain of predefined values.

- ```rust
  pub fn satisfy<B: Brancher, T: TerminationCondition>(self: &mut Self, brancher: &mut B, termination: &mut T) -> SatisfactionResult { /* ... */ }
  ```
  Solves the current model in the [`Solver`] until it finds a solution (or is indicated to

- ```rust
  pub fn get_solution_iterator<''this, ''brancher, ''termination, B: Brancher, T: TerminationCondition>(self: &''this mut Self, brancher: &''brancher mut B, termination: &''termination mut T) -> SolutionIterator<''this, ''brancher, ''termination, B, T> { /* ... */ }
  ```

- ```rust
  pub fn satisfy_under_assumptions<''this, ''brancher, B: Brancher, T: TerminationCondition>(self: &''this mut Self, brancher: &''brancher mut B, termination: &mut T, assumptions: &[Predicate]) -> SatisfactionResultUnderAssumptions<''this, ''brancher, B> { /* ... */ }
  ```
  Solves the current model in the [`Solver`] until it finds a solution (or is indicated to

- ```rust
  pub fn optimise<B, Callback, /* synthetic */ impl TerminationCondition: TerminationCondition, /* synthetic */ impl OptimisationProcedure<B, Callback>: OptimisationProcedure<B, Callback>>(self: &mut Self, brancher: &mut B, termination: &mut impl TerminationCondition, optimisation_procedure: impl OptimisationProcedure<B, Callback>) -> OptimisationResult
where
    B: Brancher,
    Callback: SolutionCallback<B> { /* ... */ }
  ```
  Solves the model currently in the [`Solver`] to optimality where the provided

- ```rust
  pub fn add_constraint<Constraint>(self: &mut Self, constraint: Constraint) -> ConstraintPoster<''_, Constraint> { /* ... */ }
  ```
  Add a constraint to the solver. This returns a [`ConstraintPoster`] which enables control

- ```rust
  pub fn add_clause</* synthetic */ impl IntoIterator<Item = Predicate>: IntoIterator<Item = Predicate>>(self: &mut Self, clause: impl IntoIterator<Item = Predicate>) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Creates a clause from `literals` and adds it to the current formula.

- ```rust
  pub(crate) fn add_tagged_propagator</* synthetic */ impl Propagator + 'static: Propagator + ''static>(self: &mut Self, propagator: impl Propagator + ''static, tag: NonZero<u32>) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Adds a propagator with a tag, which is used to identify inferences made by this propagator

- ```rust
  pub(crate) fn add_propagator</* synthetic */ impl Propagator + 'static: Propagator + ''static>(self: &mut Self, propagator: impl Propagator + ''static) -> Result<(), ConstraintOperationError> { /* ... */ }
  ```
  Post a new propagator to the solver. If unsatisfiability can be immediately determined

- ```rust
  pub fn default_brancher(self: &Self) -> DefaultBrancher { /* ... */ }
  ```
  Creates an instance of the [`DefaultBrancher`].

###### Trait Implementations

- **RefUnwindSafe**
- **Debug**
  - ```rust
    fn fmt(self: &Self, f: &mut $crate::fmt::Formatter<''_>) -> $crate::fmt::Result { /* ... */ }
    ```

- **VZip**
  - ```rust
    fn vzip(self: Self) -> V { /* ... */ }
    ```

- **IntoEither**
- **UnwindSafe**
- **TryFrom**
  - ```rust
    fn try_from(value: U) -> Result<T, <T as TryFrom<U>>::Error> { /* ... */ }
    ```

- **TryInto**
  - ```rust
    fn try_into(self: Self) -> Result<U, <U as TryFrom<T>>::Error> { /* ... */ }
    ```

- **Sync**
- **From**
  - ```rust
    fn from(t: T) -> T { /* ... */ }
    ```
    Returns the argument unchanged.

- **Unpin**
- **Any**
  - ```rust
    fn type_id(self: &Self) -> TypeId { /* ... */ }
    ```

- **Downcast**
  - ```rust
    fn into_any(self: Box<T>) -> Box<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn into_any_rc(self: Rc<T>) -> Rc<dyn Any> { /* ... */ }
    ```

  - ```rust
    fn as_any(self: &Self) -> &dyn Any + ''static { /* ... */ }
    ```

  - ```rust
    fn as_any_mut(self: &mut Self) -> &mut dyn Any + ''static { /* ... */ }
    ```

- **BorrowMut**
  - ```rust
    fn borrow_mut(self: &mut Self) -> &mut T { /* ... */ }
    ```

- **Default**
  - ```rust
    fn default() -> Self { /* ... */ }
    ```

- **Into**
  - ```rust
    fn into(self: Self) -> U { /* ... */ }
    ```
    Calls `U::from(self)`.

- **Borrow**
  - ```rust
    fn borrow(self: &Self) -> &T { /* ... */ }
    ```

- **Freeze**
- **Send**
#### Type Alias `DefaultBrancher`

A brancher which makes use of VSIDS \[1\] and solution-based phase saving (both adapted for CP).

If VSIDS does not contain any (unfixed) predicates then it will default to the
[`IndependentVariableValueBrancher`] using [`RandomSelector`] for variable selection
(over the variables in the order in which they were defined) and [`RandomSplitter`] for
value selection.

# Bibliography
\[1\] M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang, and S. Malik, ‘Chaff: Engineering an
efficient SAT solver’, in Proceedings of the 38th annual Design Automation Conference, 2001.

\[2\] E. Demirović, G. Chu, and P. J. Stuckey, ‘Solution-based phase saving for CP: A
value-selection heuristic to simulate local search behavior in complete solvers’, in the
proceedings of the Principles and Practice of Constraint Programming (CP 2018).

```rust
pub type DefaultBrancher = crate::branching::branchers::autonomous_search::AutonomousSearch<crate::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher<crate::engine::variables::DomainId, crate::branching::variable_selection::RandomSelector, crate::branching::value_selection::RandomSplitter>>;
```

## Module `results`

Contains the outputs of solving using the [`Solver`].

We differentiate between 3 different types of results:
- For a **satisfaction** problem ([`SatisfactionResult`])
- For a **satisfaction** problem using **assumptions**
  ([`SatisfactionResultUnderAssumptions`])
- For an **optimisation** problem ([`OptimisationResult`])

On these results, different methods can be called which ensure that the solver is in the
right state for these operations. For example,
[`SatisfactionResultUnderAssumptions::UnsatisfiableUnderAssumptions`] allows you to extract
a core consisting of the assumptions using [`UnsatisfiableUnderAssumptions::extract_core`].

```rust
pub mod results { /* ... */ }
```

### Re-exports

#### Re-export `solution_iterator`

```rust
pub use crate::api::outputs::solution_iterator;
```

#### Re-export `unsatisfiable`

```rust
pub use crate::api::outputs::unsatisfiable;
```

#### Re-export `OptimisationResult`

```rust
pub use crate::api::outputs::OptimisationResult;
```

#### Re-export `ProblemSolution`

```rust
pub use crate::api::outputs::ProblemSolution;
```

#### Re-export `SatisfactionResult`

```rust
pub use crate::api::outputs::SatisfactionResult;
```

#### Re-export `SatisfactionResultUnderAssumptions`

```rust
pub use crate::api::outputs::SatisfactionResultUnderAssumptions;
```

#### Re-export `SolutionReference`

```rust
pub use crate::api::outputs::SolutionReference;
```

#### Re-export `Solution`

```rust
pub use crate::basic_types::Solution;
```

## Module `variables`

Contains the variables which are used by the [`Solver`].

A variable, in the context of the solver, is a view onto a domain. It may forward domain
information unaltered, or apply transformations which can be performed without the need of
constraints.

We define 2 types of variables:
- Integer Variables ([`IntegerVariable`]) - These are represented by [`DomainId`]s when
  interacting with the [`Solver`]. These variables can be created using
  [`Solver::new_bounded_integer`] when creating a variable with the domain between a
  lower-bound and an upper-bound or using [`Solver::new_sparse_integer`] when creating a
  variable with holes in the domain. These variables can be transformed (according to the
  trait [`TransformableVariable`]) to create an [`AffineView`].
- Literals ([`Literal`]) - These specify booleans that can be used when interacting with the
  [`Solver`]. A [`Literal`] can be created using [`Solver::new_literal`].

```rust
pub mod variables { /* ... */ }
```

### Re-exports

#### Re-export `AffineView`

```rust
pub use crate::engine::variables::AffineView;
```

#### Re-export `DomainId`

```rust
pub use crate::engine::variables::DomainId;
```

#### Re-export `IntegerVariable`

```rust
pub use crate::engine::variables::IntegerVariable;
```

#### Re-export `Literal`

```rust
pub use crate::engine::variables::Literal;
```

#### Re-export `TransformableVariable`

```rust
pub use crate::engine::variables::TransformableVariable;
```

## Module `options`

Contains the options which can be passed to the [`Solver`].

These influence the following aspects:
- The restart strategy of the solver
- The learned clause database management approach
- The proof logging

```rust
pub mod options { /* ... */ }
```

### Re-exports

#### Re-export `SequenceGeneratorType`

```rust
pub use crate::basic_types::sequence_generators::SequenceGeneratorType;
```

#### Re-export `ConflictResolver`

```rust
pub use crate::engine::ConflictResolver;
```

#### Re-export `RestartOptions`

```rust
pub use crate::engine::RestartOptions;
```

#### Re-export `SatisfactionSolverOptions`

```rust
pub use crate::engine::SatisfactionSolverOptions as SolverOptions;
```

#### Re-export `LearnedNogoodSortingStrategy`

```rust
pub use crate::propagators::nogoods::LearnedNogoodSortingStrategy;
```

#### Re-export `LearningOptions`

```rust
pub use crate::propagators::nogoods::LearningOptions;
```

#### Re-export `CumulativeExplanationType`

```rust
pub use crate::propagators::CumulativeExplanationType;
```

#### Re-export `CumulativeOptions`

```rust
pub use crate::propagators::CumulativeOptions;
```

#### Re-export `CumulativePropagationMethod`

```rust
pub use crate::propagators::CumulativePropagationMethod;
```

## Module `termination`

Contains the conditions which are used to determine when the [`Solver`] should terminate
even when the state of the satisfaction/optimization problem is unknown.

The main [`TerminationCondition`] is a condition which is polled by the [`Solver`] during
the search process. It indicates when the [`Solver`] should stop, even if no definitive
conclusions have been made.

The most common example would be [`TimeBudget`], which terminates the [`Solver`] whenever
the time budget is exceeded.

```rust
pub mod termination { /* ... */ }
```

### Re-exports

#### Re-export `TerminationCondition`

```rust
pub use crate::engine::termination::TerminationCondition;
```

#### Re-export `crate::engine::termination::combinator::*`

```rust
pub use crate::engine::termination::combinator::*;
```

#### Re-export `crate::engine::termination::indefinite::*`

```rust
pub use crate::engine::termination::indefinite::*;
```

#### Re-export `crate::engine::termination::os_signal::*`

```rust
pub use crate::engine::termination::os_signal::*;
```

#### Re-export `crate::engine::termination::time_budget::*`

```rust
pub use crate::engine::termination::time_budget::*;
```

## Module `predicates`

Contains structures which represent certain [predicates](https://en.wikipedia.org/wiki/Predicate_(mathematical_logic)).

The solver only utilizes the following types of predicates:
- A [`Predicate::LowerBound`] of the form `[x >= v]`
- A [`Predicate::UpperBound`] of the form `[x <= v]`
- A [`Predicate::Equal`] of the form `[x = v]`
- A [`Predicate::NotEqual`] of the form `[x != v]`

In general, these [`Predicate`]s are used to represent propagations, explanations or
decisions.

```rust
pub mod predicates { /* ... */ }
```

### Re-exports

#### Re-export `PropositionalConjunction`

```rust
pub use crate::basic_types::PropositionalConjunction;
```

#### Re-export `Predicate`

```rust
pub use crate::engine::predicates::predicate::Predicate;
```

#### Re-export `PredicateConstructor`

```rust
pub use crate::engine::predicates::predicate_constructor::PredicateConstructor;
```

### Re-exports

#### Re-export `Function`

```rust
pub use crate::basic_types::Function;
```

## Macros

### Macro `conjunction`

**Attributes:**

- `#[macro_export]`

A macro which allows for the creation of a [`PropositionalConjunction`].

# Example
```rust
# use pumpkin_solver::predicates::PropositionalConjunction;
# use pumpkin_solver::Solver;
# use pumpkin_solver::conjunction;
# use pumpkin_solver::predicate;
let mut solver = Solver::default();
let x = solver.new_bounded_integer(0, 10);
let y = solver.new_bounded_integer(5, 15);

let conjunction = conjunction!([x >= 5] & [y <= 10]);
assert_eq!(
    conjunction,
    PropositionalConjunction::new(vec![predicate!(x >= 5), predicate!(y <= 10)].into())
);
```

```rust
pub macro_rules! conjunction {
    /* macro_rules! conjunction {
    (@to_conjunction $($body:tt)*) => { ... };
    (@munch {$($body:tt)*} -> & [$($pred:tt)+] $($rest:tt)*) => { ... };
    (@munch {$($body:tt)*} -> ) => { ... };
    (@munch {$($body:tt)*} -> $($rest:tt)+) => { ... };
    ($($input:tt)+) => { ... };
    () => { ... };
} */
}
```

### Macro `predicate`

**Attributes:**

- `#[macro_export]`

A macro which allows for the creation of a [`Predicate`].

# Example
```rust
# use pumpkin_solver::Solver;
# use pumpkin_solver::predicate;
# use pumpkin_solver::predicates::Predicate;
let mut solver = Solver::default();
let x = solver.new_bounded_integer(0, 10);

let lower_bound_predicate = predicate!(x >= 5);
assert_eq!(
    lower_bound_predicate,
    Predicate::LowerBound {
        domain_id: x,
        lower_bound: 5
    }
    .into()
);

let upper_bound_predicate = predicate!(x <= 5);
assert_eq!(
    upper_bound_predicate,
    Predicate::UpperBound {
        domain_id: x,
        upper_bound: 5
    }
    .into()
);

let equality_predicate = predicate!(x == 5);
assert_eq!(
    equality_predicate,
    Predicate::Equal {
        domain_id: x,
        equality_constant: 5
    }
    .into()
);

let disequality_predicate = predicate!(x != 5);
assert_eq!(
    disequality_predicate,
    Predicate::NotEqual {
        domain_id: x,
        not_equal_constant: 5
    }
    .into()
);
```

```rust
pub macro_rules! predicate {
    /* macro_rules! predicate {
    ($($var:ident).+$([$index:expr])? >= $bound:expr) => { ... };
    ($($var:ident).+$([$index:expr])? <= $bound:expr) => { ... };
    ($($var:ident).+$([$index:expr])? == $value:expr) => { ... };
    ($($var:ident).+$([$index:expr])? != $value:expr) => { ... };
} */
}
```

### Macro `create_statistics_struct`

**Attributes:**

- `#[macro_export]`

A macro for generating a struct for storing statistics.

# Example
```rust
# use pumpkin_solver::create_statistics_struct;
create_statistics_struct!(Statistics {
    number_of_calls: usize
});

let statistics = Statistics::default();

assert_eq!(statistics.number_of_calls, 0);
```

```rust
pub macro_rules! create_statistics_struct {
    /* macro_rules! create_statistics_struct {
    ($(#[$struct_documentation:meta])* $name:ident { $($(#[$variable_documentation:meta])* $field:ident : $type:ident $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)?),+ $(,)? }) => { ... };
} */
}
```

## Re-exports

### Re-export `DefaultBrancher`

```rust
pub use crate::api::solver::DefaultBrancher;
```

### Re-export `Solver`

```rust
pub use crate::api::solver::Solver;
```

### Re-export `ConstraintOperationError`

```rust
pub use crate::basic_types::ConstraintOperationError;
```

### Re-export `Random`

```rust
pub use crate::basic_types::Random;
```

### Re-export `api::*`

```rust
pub use api::*;
```

