# Reason.js

## Just experimenting for the time being

This project aims to create a dependently-typed language interpreter in JavaScript to enable native 'certifiable' (i.e. provable) programs.

User references:

* [**Reason.js** introduction and tutorial](https://ajhamwood.github.io/reason) by me

Development references:
* [LambdaPi](https://www.andres-loeh.de/LambdaPi/)
* [Pi-Forall](https://github.com/sweirich/pi-forall)
* [Dependent Pattern Matching and Proof-relevant Unification](https://jesper.sikanda.be/files/thesis-final-digital.pdf)
* [Elaborating Dependent (Co)pattern Matching](https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf)
* [Eliminating the problems of hidden-lambda insertion: Restricting implicit arguments for increased predictability of type checking in a functional programming language with dependent types](http://www.cse.chalmers.se/~abela/MScThesisJohanssonLloyd.pdf)
* [Cubical Agda: A Dependently Typed Programming Language with Univalence and Higher Inductive Types](https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf)

# Features

## JavaScript API
**Reason.js** objects are created using the `Data`, `Def` and `Sig` methods on an initialised `Reason` object. The un-typechecked object is available synchronously with limited properties, and immediately attempts asynchronous typechecking.

To request asynchronous typechecking of **Reason** code either use eg `R.ready`, or for a new object called `myTerm`, use `myTerm.ready`. If your code passes typechecking, new properties and methods will become available.
```js
let R = Reason();

// First method
let identity = new R.Def(
  "id", "(t , x => x) : (T : Type) -> T -> T"
);
await R.ready;

// Second method
let identity = await new R.Def(
  "id", "(t , x => x) : (T : Type) -> T -> T"
).ready;
```

### One-line definitions using `R.Def(name, term)`
Create a simple definition using annotation syntax `term : Type`. In almost all cases, you will need to surround both keywords and user-defined terms with spaces. Phrases like `term: Type` or `term:Type` will not typecheck. Besides annotations, *Lambda* terms are written like `x , y , z => expr`, and *pi* terms (type terms corresponding to functions) are written like `A -> B -> C`.

After typechecking, the your definition will be available in the core syntax through `myTerm.term`, the result of running `myTerm` will be at `myTerm.result`, and the computed type of the result will be at `myTerm.type`.
```js
let idType = new R.Def("idT", "((T : Type) -> T -> T) : Type");
idT.name; // == "idT"

await R.ready;
idType.print; // == "(x : Type) -> (x) -> x"
idType.appliedTerms; // == []
idType.term; // user Term (prints as "(x : Type) -> (x) -> x")
idType.result; // computed Term (prints as "(x : Type) -> (x) -> x")
idType.type; // computed Type (prints as "Type")
```
Reason objects with function type can be applied directly in JavaScript: the arity of the type is the arity of the object when it is used as a JS function, and can be used in both curried and functional style. The resulting object retains a trace of the arguments applied to it, which can be accessed using `myNewTerm.appliedTerms`.
```js
let idid = await identity(idType, identity).ready;

idid.name; // == "id"
idid.print; // == "id ((x : Type) -> (y : x) -> x) (x , y => y)"
idid.result.print(); // == "x , y => y"
idid.appliedTerms; // == [ idT(), id() ]
```

### Separating type signature and term definition using `R.Sig(name, typeTerm)`
When writing more involved code, it can be handy to separate out the signature and definition into their own sections. A signature by itself will have a limited property list, but the result of giving `Sig` first, then `Def`, will be indistinguishable from giving them together in `Def`.
```js
let constant = await new R.Sig("const", "(T : Type) -> T -> T -> T").ready;
constant.print; // == "(x : Type) -> (x) -> (x) -> x"
constant.type.print(); // == "(x : Type) -> (x) -> (x) -> x"

(constant = await id2.Def("t , x , y => x").ready).print; // == "x , y , z => y"
```

### Defining datatypes using `R.Data(name, typeCon, [...dataCon])`
As with other functional languages, Data structures in Reason are defined by giving a type constructor, along with zero or more data constructors. As datatypes can also take arguments if they are a type family, they too are accessed as functions.

If a datatype has constructors, they can be accessed on the JS object by their lowercase name, and may act as functions as well.
```js
let Void = new R.Data("Void", "Type", []),
    Unit = await new R.Data("Unit", "Type", [ "TT : Unit" ]).ready,
    absurd = new R.Sig("absurd", "(A : Type) -> Void");

Void().print; // == "Void"
Unit().tt().print; // == "TT"
Unit().tt().type.print(); // "Unit"
```
Data constructors are written like `DataCon : Args -> TypeCon`. If they take two or more arguments, the `Args` above may be written like `(a : A)(b : B) -> C` with zero or more bindings on the left.
```js
 // Demonstrating that 2 + 2 = 4

let Nat = await new R.Data(
      "Nat", "Type",
      [ "Z : Nat",
        "S : Nat -> Nat" ]).ready, // Must typecheck before they can be used
    addTwo = await new R.Sig(
      "addTwo", "Nat -> Nat" ).Def(
      "n => S (S n)").ready;

let four = await addTwo( Nat().s( Nat().s( Nat().z() ) ) ).ready;
four.print; // == "addTwo (S (S Z))"
four.result.print(); // == S (S (S (S Z)))
```

### Converting JS objects to Reason terms and vice versa: `R.Data(name, typeCon, [...{[dataCon]: {...toJS}}], {fromJS})`
This definition format allows for user-defined converters between the Reason computation context and the ambient JavaScript context. Each data constructor hash must contain a single key-value pair.
```js
let Bool = await new R.Data(
      "Bool", "Type",
      [ { "False : Bool": { toString: () => "F", valueOf: () => false } },
        { "True : Bool": { toString: () => "T", valueOf: () => true } } ],
      { fromJS: v => v ? Bool().true() : Bool().false() }).ready;

let t = Bool().fromJS(true);
t.print // == 'True'
t.toString() // == "T"
```

### Parametrised types
For data types which take one or more fully general parameters to be constructed, the type constructor must be written with a `:` separator, parameters going on the left. Parameters are written like `(a : A)(b : B)(c : C)`.

It is also possible to write converters for parametrised types by using `this` within the `fromJS` function body: a parameter labelled `P` in the type constructor will be available in lowercase as `this.p`, and all data constructors will be available in the same way. In the reverse direction, arguments to data constructors will be available as an `Array` on `this`.
```js
let List = new await R.Data(
      "List", "(A : Type) : Type",
      [ { "Nil : List A": { toString: () => '[]', valueOf: () => [] } },
        { "Cons : A -> List A -> List A":
          { toString () { return '[ ' + (this[1].name === "Cons" ?
              this[0].toString() + ', ' + this[1].toString().slice(2) :
              this[0].toString() + ' ]') },
            valueOf () { return [ this[0].valueOf() ].concat(this[1].valueOf()) } } } ],
      { fromJS (v) { let p = () => v.length ?
          this.cons(this.a.fromJS(v.shift()), p()) :
          this.nil(); return p() } } ).ready;

let someList = List(Bool()).fromJS([true, false])
somelist.print // == "Cons True (Cons False Nil)"
somelist.toString() // == "[ T, F ]"
```

### Case expressions: `R.Sig(...).Def({scrutinee: [...clause]})`
This construct opens the door to richer functions that are defined based on case analysis of the inputs. The scrutinee selects which function argument to analyse and is written like `a b c | a`, and clauses provide return values and are written like `Con x y := z`.
```js
let not = await new R.Sig(
      "not", "Bool -> Bool" ).Def({
      "b | b":
      [ "True  := False",
        "False := True" ] }).ready;

(await not(Bool().true()).ready).result.print() // == 'False'
```

### Pattern match expressions: `R.Sig(...).Def([...clause])`
ML-style function definition. Clauses are written like `@ a b c := d`, where patterns can be a variable, wildcard `_`, or have constructors and variables nested to any level.

Recursive functions must recurse in such a way that the applied arguments taken together are always structurally getting smaller (eg below, the `m` in `half m` has a smaller structure than the `S (S m)` in `half (S (S m))`).
```js
let half = await new R.Sig(
      "half", "Nat -> Nat" ).Def([
      "@  Z        := Z",
      "@ (S  Z)    := Z",
      "@ (S (S m)) := S (half m)" ]).ready

(await half(Nat().fromJS(5)).ready).result.print() // == "S (S Z)"
```

## Reason language features
Language features described above are:
* Type annotations: `(a : A)`
* Lambda expressions: `a , b => c`
* Pi expressions: `A -> B -> C`
* Type constructors (more on this below): `(a : A)(b : B) : Type`
* Data constructors: `A : (b : B)(c : C) -> D -> E`
* Case expressions: `a b c | c` + `D e f := g`
* Pattern match expressions: `@ a b := c`

The JavaScript API has no further features at present, so what follows are the remaining language features.

### Mixfix operators
Rather than only having terms written with the reference on the left and the arguments on the right, a more natural syntax would be for the typographic parts of an operator term to be written between or around the arguments. Borrowing Agda's mixfix syntax, the underscores in a name in Reason indicate the positions arguments will go.

A mixfix operator may start with an underscore like `_a`, end with one like `a_`, do both like `_a_`, or neither like `a_b`, and have any number greater than or equal to one in total. When writing a partially applied mixfix operator, the outside underscores are optional.
```js
let plus = await new R.Sig(
      "_+_", "Nat -> Nat -> Nat" ).Def([
      "@  Z    n := n",
      "@ (S m) n := S (m + n)" ]).ready;
(await new R.Def("onePlusOne", "(+ (S Z)) (S Z) : Nat").ready).result.print() // == S (S Z)
```

### Indexed types
While type parameters are fully general, the indices of an indexed type are at least partially specialised, and share some information with terms of that type. Type information for indexes are included on the right side of the type constructor separator, and have the same structure as data constructors, except that there must be a `Type` term at the right: `(a : A)(b : B) -> C -> Type`.
```js
let Vec = await new R.Data(
      "Vec", "(A : Type) : Nat -> Type",
      [ { "[] : Vec A Z": { toString: () => '[]', valueOf: () => [] } },
        { "_::_ : {n : Nat} -> A -> Vec A n -> Vec A (S n)":
          { toString () { return '[ ' + (this[1].name === "_::_" ?
              this[0].toString() + ', ' + this[1].toString().slice(2) :
              this[0].toString() + ' ]') },
            valueOf () { return [ this[0].valueOf() ].concat(this[1].valueOf()) } } } ],
      { fromJS (v) { let p = () => v.length ?
          this['_::_'](this.a.fromJS(v.shift()), p()) :
          this['[]'](); return p() } } ).ready;
```

## Planned features

### Near future
```js
// Implicit arguments
let doubleVec = new R.Sig(
  "doubleVec", "{A : Type}{m : Nat} -> Vec A m -> Vec A (m + m)" ).Def([
    "@ .{m} [] := []",
    "@ .{m} ({m = S k} a :: as) := {S (S (k + k))} a :: ({S (k + k)} a :: (doubleVec {k + k} as))" ]);

// Fixity annotations
let Leq = await new R.Data(
      "_<=_ r20", "Nat -> Nat -> Type",
      [ "LZ : {n : Nat} -> Z <= n",
        "LS : {m n : Nat} (p : m <= n) -> S m <= S n" ]).ready;

// Equality type
let cong = new R.Sig(
      "cong", "{a b : Type}{c d : a} -> (f : a -> b) -> c = d -> f c = f d").Def(
      { "g p | p": [ "Refl := Refl" ] }),
    antisym = new R.Sig(
      "antisym", "(m n : Nat) -> m <= n -> n <= m -> m = n" ).Def([
        "@ .Z .Z (LZ .{Z}) (LZ .{Z}) := Refl",
        "@ .(S k) .(S l) (LS {k}{l} x) (LS .{l}.{k} y) := cong (a => S a) (antisym k l x y)" ])
```
## Coming soon
```js
// Record types
let Functor = new R.Record(
      "Functor", "(f : Type -> Type) : Type",
      [ { "map : {a, b : Type} -> (a -> b) -> f a -> f b":
        { ??? } } ],
      { fromJS: ??? }),
    Applicative = new R.Record(
      "Applicative", "(f : Type -> Type) : Type",
      [ "pure : {a : Type} -> a -> f a"
        "(_<*>_ l2) : {a, b : Type} -> f (a -> b) -> f a -> f b" ])

// Copatterns
let applicativeFunctor = new R.Sig(
  "applicativeFunctor", "{A : Type} -> Functor (Applicative A)").Def([
    "map @ f x := pure f <*> x" ])

// Let/where bindings
let mirror = new R.Sig(
      "mirror", "{a : Type} -> List a -> List a" ).Def([
        "@ xs := xs ++ xs'",
        "xs' := reverse xs" ])

// Case bindings
let lookupDefault = new R.Sig(
      "lookupDefault", "{a : Type} -> Nat -> List a -> a -> a" ).Def(
        { "@ i xs def := list_lookup i xs": [
          "Nothing := def",
          "Just x  := x"   ] })

// Namespaces
let VecEq = new R.Namespace(ns => ({
      EqVecs: ns.Data(
        "(_~=~_ r4)", "{m n : Nat} -> Vec a m -> Vec a n -> Type", [
          "NilCong : Nil ~=~ Nil",
          "ConsCong x y : {xs, ys} -> (x = y) -> (xs ~=~ ys) -> Cons x xs ~=~ Cons y ys" ]),
      eqVecsEqLength: ns.Sig(
        "eqVecsEqLength", "{m n : Nat}{xs : Vec a m}{ys : Vec a n} -> (xs ~=~ ys) -> m = n" ).Def(
          "@ NilCong := Refl",
          "@ (ConsCong _ e) := cong (a => S a) (eqVecsEqLength e)" ) }));

// Cubical types: I, transp => transpX, PathP, PartialP, hcomp => ghcomp, Glue
let funExt = new R.Sig(
      "funExt", "{A B : Type}{f g : A -> B}(p : (x : A) -> f x = g x) -> f = g" ).Def([
      "@ p i x := p x i" ]),
    transport = new R.Sig(
      "transport", "{A B : Type} -> A = B -> A -> B" ).Def([
      "@ p a := transp (i => p i) left a" ])
```
