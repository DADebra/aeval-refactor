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
a series of productions, denoted by the special `*_either_*` family of
functions, which have the form `(SORT_either_# PRODUCTIONS...)` where
`SORT` is the sort of each production and the non-terminal, `#` is the number
of productions listed, and `PRODUCTIONS` is a list of productions for the
non-terminal. Note that the `SORT` for parametric types like `Array` is simply
the SMT for the sort with '(' replaced by '\$' and spaces replaced by
underscores (e.g. the sort `(Array Int Int)` is given as `$Array_Int_Int$`).


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
special (pre-defined) function `(SORT_Prio)`, where `SORT` is the same as
in the `(*_either_*)` family of functions above. The function takes two
parameters: the first is the production to change the priority of
(of sort SORT), the second is the priority given as a decimal number.

If a priority is not given for a certain production, the default is 1,
which means that the production will always be used when the traversal
picks it.

It is a semantic error to specify a number greater than 1 as a priority.

The meaning of the priority number is (roughly) that the production will be
used with that percentage when expanding the given non-terminal. For instance,
a line like:

```
(assert (= iterm (Int_either_2
  (= INT_VARS INT_CONSTS)
  (Bool_prio (> INT_VARS INT_CONSTS) 0.1))
))
```

Whenever, in the traversal, a production is chosen for iterm, the production
chosen will be `(= INT_VARS INT_CONSTS)` about 90% of the time,
and will be `(> INT_VARS INT_CONSTS)` about 10% of the time.

The prioritization is in addition to the traversal documented below, if
a traversal method is used: a production is first picked using the rules
for the specific traversal method chosen, then skipped over if necessary
according to the prioritization. This isn't particularly evident for
`--trav_type striped`, but extraordinarily visible for `--trav_type ordered`:
all permutations of `(= INT_VARS INT_CONSTS)` will be chosen first, then
all permutations of `(> INT_VARS INT_CONSTS)` (assuming `ltr` and `forward`),
practically ignoring the priority specified.

Note that, the deeper the non-terminal, the less-accurate the percentage will
be, due to how the traversal algorithm works; deep non-terminals will tend
to expand to the same production several times in a row.

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
(assert (= iterm (Int_either_4
  (+ iterm iterm) (* iterm INT_CONSTS) INT_VARS INT_CONSTS
)))
```

and a `--maxrecdepth` of 2, the non-terminal is equivalent to this series of
non-terminals and productions:

```
(assert (= iterm0 (Int_either_4
  (+ iterm1 iterm1) (* iterm1 INT_CONSTS) INT_VARS INT_CONSTS
)))
(assert (= iterm1 (Int_either_4
  (+ iterm2 iterm2) (* iterm2 INT_CONSTS) INT_VARS INT_CONSTS
)))
(assert (= iterm2 (Int_either_2
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

(assert (= iconst (Int_either_3 0 1 2)))
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
