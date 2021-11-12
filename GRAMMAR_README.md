# New CFG-Based Traversal

## CFG File

The CFG to be used for traversal is passed via the `--grammar` option; it
should be in SMT2 format, with productions specified via `(assert)` and
non-terminals declared via `(declare-fun)`. Note that multiple CFG files
can be passed; if multiple CFG files define the same root (documented below),
the first CFG file is preferred.

### The Root(s) of the CFG
The start symbol of the CFG is of sort `Bool`, and is either the name of an
inductive invariant in the input file (e.g. `inv`) or the special name
`ANY_INV` to indicate that the CFG should be used for any of the invariants
in the input file. A single CFG file can define more than one start symbol,
used when the input file includes multiple inductive invariants. If a CFG file 
defines a start symbol which matches the name of an inductive invariant in the
input file (e.g. `inv`) *and* the `ANY_INV` start symbol, the more specific
`inv` (in this example) will be used; this allows for `ANY_INV` to be used
as a default, with specific CFG roots overriding it if present.

### Productions
Productions are of the form `(assert (= NON-TERMINAL PRODUCTION))`, where
`PRODUCTION` is either a single production (e.g. `(+ 1 INT_VARS)`), or
a series of productions, denoted by the special `either` family of
functions, which have the form `(either PRODUCTIONS...)` where `PRODUCTIONS`
is a list of productions for the non-terminal.

It is a semantic error to have a given non-terminal on the left side of more
than one `(assert)` statement; all productions for a non-terminal must be
defined in a single `(assert)` statement.

### Special Variables
The following special variables (or families of special variables) are defined
to ease the development of generic CFGs:

- `SORT_VARS`

    Expands to all variables given in the input file of sort `SORT`. Note that
    `SORT` is all uppercase, even if the name of the sort isn't; e.g. for
    sort `Bool`, the variable is given as `BOOL_VARS`. Note also that this
    non-terminal won't exist if a given sort isn't used in the input file.

- `INT_CONSTS`

    Expands to all integer constants present in the input file, or the default
    list of `{ -1, 0, 1 }` if no constants are present.


### Prioritization
Freqhorn supports basic de-prioritization of certain productions of a given
non-terminal. Prioritization values are specified in the grammar using the
special (pre-defined) function `prio`. The function takes two
parameters: the first is the production to change the priority of,
the second is the priority given as a decimal number.

It is a semantic error to specify a number greater than 1 as a priority.

The way that prioritization works is dependent on the `--gen_method` chosen:

- `--gen_method traverse`

    If a priority is not given for a certain production it defaults to 1, which
    means that the production will always be used when the traversal picks it.

    The meaning of the priority number is (roughly) that the production will be
    used with that percentage when expanding the given non-terminal. For
    instance, a line like:

    ```
    (assert (= bterm (either
      (= INT_VARS INT_CONSTS)
      (prio (> INT_VARS INT_CONSTS) 0.1))
    ))
    ```

    Whenever, in the traversal, a production is chosen for iterm, the
    production chosen will be `(= INT_VARS INT_CONSTS)` about 90% of the time,
    and will be `(> INT_VARS INT_CONSTS)` about 10% of the time.

    The prioritization is in addition to the traversal documented below, if
    a traversal method is used: a production is first picked using the rules
    for the specific traversal method chosen, then skipped over if necessary
    according to the prioritization. This isn't particularly evident for
    `--trav_type striped`, but extraordinarily visible for
    `--trav_type ordered`: all permutations of `(= INT_VARS INT_CONSTS)` will
    be chosen first, then all permutations of `(> INT_VARS INT_CONSTS)`
    (assuming `ltr` and `forward`), practically ignoring the priority
    specified.

    Note that, the deeper the non-terminal, the less-accurate the percentage
    will be, due to how the traversal algorithm works; deep non-terminals will 
    tend to expand to the same production several times in a row.

- `--gen_method rnd`

    The priorities given for the productions of a non-terminal are interpreted 
    as a distribution; if not normal, it will be normalized after the CFG is
    parsed. Unspecified priorities will be 1. Productions are picked randomly
    using this distribution; given a sufficient number of iterations,
    the distribution of generated productions should match this normalized
    distribution. For example, given the below prioritization:

    ```
    (assert (= bterm (either
      (= INT_VARS INT_CONSTS)
      (> INT_VARS INT_CONSTS)
      (prio (< INT_VARS INT_CONSTS) 0.3)
      (prio (~= INT_VARS INT_CONSTS) 0.2)
    )))
    ```
    `bterm` will expand to `(< INT_VARS INT_CONSTS)` about 12% of the time,
    to `(~= INT_VARS INT_CONSTS)` about 8% of the time,
    to `(= INT_VARS INT_CONSTS)` about 40% of the time, and
    to `(> INT_VARS INT_CONSTS)` about 40% of the time.

### Constraints

In order to facilitate the creation of succinct CFG files, freqhorn supports
declaring constraints. The intention with constraints is both to allow
manipulating the auto-generated variables, such as `INT_CONSTS`, and to support
limiting the universe of constraints in a more intuitive way. In principle,
each constraint is just a boolean expression which gets evaluated for each
candidate that the traversal generates; if it evaluates to `true`, the 
candidate is used, and if `false` the candidate is skipped. Both non-terminals
and terminals are valid symbols to be used in constraints: terminals are
treated as-is, while non-terminals are first expanded using each expansion(s)
present in the candidate. For instance, consider the sample CFG below:

```
; Sample CFG for constraints

; Auto-generated by freqhorn
;(assert (= INT_VARS (either _FH_inv_0 _FH_inv_1 _FH_inv_2)))
;(assert (= INT_CONSTS (either -1 0 1)))

(assert (= bterm (either (= ivar INT_CONSTS) (> ivar INT_CONSTS))))
(assert (= ANY_INV (or bterm bterm)))
```

For a constraint like `(= INT_CONSTS 1)`, and candidate like
`(or (= _FH_inv_0 1) (= _FH_inv_1 -1))`, the constraint is first interpreted
as `(= 1 1)`, then `(= -1 1)`. If a constraint contains more than one different
non-terminal, then each combination of expansions is considered; if the same
non-terminal is specified multiple times in a single constraint, the instances
will share a common expansion(s) (e.g. for constraint
`(or (= INT_CONSTS 1) (= INT_CONSTS -1))`, expansions are
`(or (= 1 1) (= 1 -1))` and `(or (= -1 1) (= -1 -1))` for example candidate).

In SMT, constraints are declared via assertions, using the function
`(declare-fun constraint (Bool) Bool)`; e.g., the above constraint is given as
`(assert (constraint (= INT_CONSTS 1)))`.

Constraints, by default, must evaluate to `true` for all combinations of
expansions of non-terminals in the candidate; e.g., for the above candidate
and constraint, the candidate would be discarded because it includes an
`INT_CONSTS` that isn't equal to 1. If, instead, it is desired that the
constraint only need evaluate `true` for one (or more) expansions, one may use
the function `(declare-fun constraint_any (Bool) Bool)`.

Freqhorn provides a few custom functions to deal explicitly with the parse tree
of a candidate:

- `(distinct var1)` is equal to `true` when all expansions of non-terminal
  `var1` are unique.

- `(equal var1)` is the opposite of above `all_distinct`; it is equal
  to `true` when all expansions of non-terminal `var1` are the same.

- `(equal var1 var2 ...)` is equivalent to `(= var1 var2 ...)` and just
  provided for convenience.

- `(distinct_under "nt" var1 [var2 ...])` is equal to `true` when all
  expansions of non-terminal `var1` are unique under the *same* node `"nt"`,
  i.e. if there are multiple instances of `"nt"` in the candidate,
  this will ensure that `var1` is distinct under each instance. Note that,
  for recursive non-terminals, the highest non-terminal is picked, e.g. if
  `"nt"` expands to `(or nt nt)`, `var1` will be distinct across the `or`.
  If more than one non-terminal (e.g. `var2`) is specified, then statement
  is `true` if `var1` and `var2` are always distinct under the same `"nt"`,
  which *does not* ensure that `var1` is distinct with itself.

- `(equal_under "nt" var1 [var2 ...])` is the opposite of above
  `distinct_under`; it is equal to `true` when all expansions are the same,
  instead of distinct.

- `(expands var1 "var2")` is `true` when non-terminal `var1` expands to
  expression `var2` (enclosed in quotes) in the parse tree of the candidate.
  If `var1` isn't present in the candidate, then the expression is `true`.

- `(present "var1")` is `true` when non-terminal or terminal `var1` is
  present in the parse tree of the candidate.

- `(under "var1" var2)` is `true` when the given expansion of `var2`
  is a child of `"var1"` (must be in quotes).

- `(recdepth "var1")` returns the deepest recursive depth that `"var1"` goes
  in the parse tree of the candidate.

Constraints are evaluated in most cases by an internal function within
freqhorn; if a constraint cannot be evaluated by this function, it will be
passed on to the Z3 solver, which should allow for the use of more advanced
constraints such as those which include quantifiers. Note that constraints
which get sent to Z3 first have their non-terminals expanded as usual;
`(constraint ...)` and `(constraint_any ...)` still function as normally.
Note that the Z3 solver isn't as good at handling terminal symbolic variables
such as the \_FH\_\* family of invariant arguments; freqhorn will detect
comparisons between these variables and translate them to a form Z3 will work
with, but some (valid) applications of them may still fail. Note that using the
Z3 solver to evaluate constraints is considerably slower than using the
internal function; the user is recommended to avoid constraints that make use
of Z3 unless absolutely necessary (freqhorn will warn you if it is using Z3 to
evaluate a constraint).

Following are some sample constraints with explanations in English, using
the same sample CFG from above (copied below for the reader's convenience).
For brevity, the preceding `(constraint` is omitted and present unless
otherwise noted.

```
; Sample CFG for constraints

; Auto-generated by freqhorn
;(assert (= INT_VARS (either _FH_inv_0 _FH_inv_1 _FH_inv_2)))
;(assert (= INT_CONSTS (either -1 0 1)))
(assert (= ivar1 INT_VARS))
(assert (= ivar2 INT_VARS))

(assert (= bterm (either (= ivar1 INT_CONSTS) (> ivar2 INT_CONSTS))))
(assert (= ANY_INV (or bterm bterm)))
```

  - `(distinct ivar1 ivar2)` - ensures that we don't make multiple comparisons
    on the same variable.
  - `(= ivar1 ivar2)` - requires that `ivar1` and `ivar` always expand to
    the same thing (opposite of above ex.).
  - `(= (mod INT_CONSTS 2) 0)` - only allows even integer constants.
  - `(or (= INT_VARS _FH_inv_0) (= INT_VARS _FH_inv_1))` - limits integer
    variables allowed to be used to `_FH_inv_0` and `_FH_inv_1`.
  - `(expands bterm "(= ivar1 INT_CONSTS)")` - only allow the first production
    of `bterm` to be used.
  - `(constraint_any (= INT_VARS _FH_inv_0))` - ensure that `_FH_inv_0` is
    present in the candidate.
  - `(=> (present "_FH_inv_0") (= (mod INT_CONSTS 2) 0))` - only allow for
    even integer constants when `_FH_inv_0` is present in the candidate.
  - `(exists ((i Int)) (and (= i INT_CONSTS) (>= i 0)))` - equivalent to
    `(>= INT_CONSTS 0)`, but showing off the use of quantifiers. Note that
    this is the only example listed which requires Z3.

## Generation

Once the CFG file has been written, given on the command line, and successfully
parsed, candidate generation will begin. The exact algorithm used to generate
candidates depends on the command line options given, documented below.

### `--gen_method`

  - `rnd` **(default)**

    A completely random, context-free generation method. Every time a candidate
    is generated, a random path in the CFG is chosen. A pre-defined number of
    candidates are stored once generated to reduce the chance of repeated
    candidates. Because the traversal is completely random, the traversal will
    never finish.

  - `traverse`

    An exhaustive traversal through the CFG; traversal continues where it left
    off when a new candidate is generated. Because of this, the traversal is
    guaranteed to end for a given `--maxrecdepth` (documented later). The
    algorithm used to perform the traversal can be configured by several
    options all prefixed by `--trav_` and documented later.

### `--maxrecdepth`

Valid for either `--gen_method`, this option takes a single integer argument.
The integer is interpreted as the maximum depth to expand recursive
productions. For instance, given the following non-terminal and productions:

```
(assert (= iterm (either
  (+ iterm iterm) (* iterm INT_CONSTS) INT_VARS INT_CONSTS
)))
```

and a `--maxrecdepth` of 2, the non-terminal is equivalent to this series of
non-terminals and productions:

```
(assert (= iterm0 (either
  (+ iterm1 iterm1) (* iterm1 INT_CONSTS) INT_VARS INT_CONSTS
)))
(assert (= iterm1 (either
  (+ iterm2 iterm2) (* iterm2 INT_CONSTS) INT_VARS INT_CONSTS
)))
(assert (= iterm2 (either
  INT_VARS INT_CONSTS
)))
```

### The `--trav_*` Family of Options

Note that all of the options require `--gen_method traverse`. The easiest way
to document the options is to show how they work, using a simple example for
each. The grammar for the examples is given below; the examples are the
different expansions of `iterm`, given in the order they are generated in:

```
; Grammar for examples
(declare-fun iterm () Int)
(declare-fun iconst () Int)

(assert (= iconst (either 0 1 2)))
(assert (= iterm (+ iconst iconst)))
```

Note that these methods are, for the most part, exclusively used when a
function is used which has arity > 1, e.g. `(+ INT_VARS INT_CONSTS)`. In such
a situation, there are several different permutations of values for the two
non-terminals; the `--trav_*` family of options determines the order those
permutations are chosen in.

#### `--trav_type`

- `striped` **(default)**

    'Increments' the first argument, then 'increments' the second, and so on.
    Requires that a `--trav_priority` is picked; cannot be shown on its own.

- `ordered`

    Exhausts the first argument of the function, then increments the second,
    then exhausts the first, and so on. Operates somewhat like a clock, or
    positional-dependent (e.g. decimal) numbers.

    ```
    (+ 0 0)
    (+ 1 0)
    (+ 2 0)
    (+ 0 1)
    (+ 1 1)
    (+ 2 1)
    (+ 0 2)
    (+ 1 2)
    (+ 2 2)
    ```

#### `--trav_priority` (Only for `--trav_type striped`)

- `sfs` **(default)**

    ```
    (+ 0 0)
    (+ 1 0)
    (+ 0 1)
    (+ 2 0)
    (+ 0 2)
    (+ 1 1)
    (+ 2 1)
    (+ 1 2)
    (+ 2 2)
    ```

- `bfs`

    ```
    (+ 0 0)
    (+ 1 0)
    (+ 0 1)
    (+ 1 1)
    (+ 1 2)
    (+ 2 0)
    (+ 0 2)
    (+ 2 1)
    (+ 2 2)
    ```

- `dfs`

    ```
    (+ 0 0)
    (+ 1 0)
    (+ 2 0)
    (+ 0 1)
    (+ 0 2)
    (+ 1 1)
    (+ 2 1)
    (+ 1 2)
    (+ 2 2)
    ```

#### `--trav_direction`

Shown with `--trav_type ordered` and `--trav_order forward`.

- `ltr` **(default)**

    ```
    (+ 0 0)
    (+ 1 0)
    (+ 2 0)
    (+ 0 1)
    (+ 1 1)
    (+ 2 1)
    (+ 0 2)
    (+ 1 2)
    (+ 2 2)
    ```

- `rtl`

    ```
    (+ 0 0)
    (+ 0 1)
    (+ 0 2)
    (+ 1 0)
    (+ 1 1)
    (+ 1 2)
    (+ 2 0)
    (+ 2 1)
    (+ 2 2)
    ```

#### `--trav_order`

Shown with `--trav_type ordered` and `--trav_direction ltr`.

- `forward` **(default)**

    ```
    (+ 0 0)
    (+ 1 0)
    (+ 2 0)
    (+ 0 1)
    (+ 1 1)
    (+ 2 1)
    (+ 0 2)
    (+ 1 2)
    (+ 2 2)
    ```

- `reverse`

    ```
    (+ 2 2)
    (+ 1 2)
    (+ 0 2)
    (+ 2 1)
    (+ 1 1)
    (+ 0 1)
    (+ 2 0)
    (+ 1 0)
    (+ 0 0)
    ```

### A Note on Simplification

Freqhorn will try to first simplify any candidates that are generated from the
CFG before sending them to the SMT solver to be checked, performing some
basic arithmetic simplification. Thus, if observing generated candidates with
the `--debug` option, one might observe a discrepancy between the candidates
generated and the language specified by the CFG. Note also that if the
simplified candidate is a tautology or contradiction, it will be skipped.

The tautology/contradiction reduction combined with the checking of new
simplified candidates against (some of) those previously generated can mean
that, especially with higher `--maxrecdepth` values, generation can seem
to pause for long periods of time; Freqhorn is still traversing the grammar,
it is simply that the candidates generated aren't worth sending to the SMT
solver.
