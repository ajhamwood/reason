## Just experimenting for the time being

This project aims to create a dependently-typed language interpreter in Javascript to enable native 'certifiable' (i.e. provable) programs.

For the most part, the nuts and bolts have been and are being lifted wholesale from Andres Loeh's LambdaPi and Stephanie Weirich's Pi-Forall.

I'm dreaming of implementing cubical types so proofs can be transported from the peano naturals to (positive) big ints. Maybe native Javascript functions and types can be incorporated as builtins in a systematic way?

I like the promise of efficiency from using interaction nets as well so I'm also planning to yoink that from moonad/Formality at some point.

### Target usage
```
// functions, lambdas
let id1 = new R
  .Sig('id', '(T : Type) -> T -> T')
  .Def('t, x => x');

// functions with builtins
let id2 = new R.Def("id'", '(x => x) : {T : Type} -> T -> T',
  { toString () { return this.value[0].toString() },
    valueOf () { return this.value[0].valueOf() } }
);

// types
let Unit = new R.Data(
  'Unit', 'Type', ['tt : Unit'],
  { fromJS: () => Unit().tt() }
);
let Nat_ = new R.Data(
  "Nat' : Type",
  [ 'Z : Nat',
    'S : Nat -> Nat' ]
)

// types with builtins
let Nat = new R.Data('Nat', 'Type',
  [ { 'Z : Nat': { toString: () => 'Z', valueOf: () => 0 } },
    { 'S : Nat -> Nat': {
      toString () { return 'S' + this.value[0].toString() },
      valueOf () { return this.value[0].valueOf() + 1 }
    } ],
  { fromJS: v => ((f = a => (--v ? f : x => x)(Nat().s(a))) => f(Nat().z()))() }
);

// usage:

console.log(Nat().z())
// Type error: unchecked
R.ready.then(async () => {
  let idN = id(Nat());
  await R.ready;

  console.log(idN(Nat().z()).valueOf())
  // 0
  console.log(idN(Unit().tt()).valueOf())
  // Type error
})

// pattern matching
let id3 = new R
  .Sig("id'' : (T : Type) -> T -> T')
  .Def('@ t x := x');

let plus = new R
  .Sig('plus', 'Nat -> Nat -> Nat')
  .Def(
    '@ Z n := n',
    '@ (S m) n := S (plus m n)'
  )

let Vec = new R.Data('Vec', '(A : Type) : Nat -> Type',
  [ { 'Nil : Vec A Z': { toString: () => '<>', valueOf: () => [] } },
    { 'Cons : {n : Nat}(A)(Vec A n) -> Vec A (S n)': {
      toString () { return this.value[0].toString() + ' :: ' + this.value[1].toString() },
      valueOf () { return this.value[1].concat([this.value[0]]) }
    } ]
);

// functions with builtins
let zipWith = new R
  .Sig('zipWith', '{a b : Type}{n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n')
  .Def(
    '@ Nil _ := Nil',
    '@ (Cons f fs) (Cons x xs) := Cons (f x) (zipWith fs xs)',
    { valueOf () { return this.value[0].map((f, i) => f(this.value[1][i])) } }
  );

//usage:
R.ready.then(async () => {
  let Succs = Vec(new R.Def('', 'Nat -> Nat : Type')) //?
  let succ = new R.Def('succ', '(x => S x) : Nat -> Nat');

  R.builtin({ 'Nat -> Nat': v => f => f(R.from(v, 'Nat')) }) //?
  await R.ready;

  let result = zipWith(
    Succs().cons(succ, Succs.cons(succ, Succs.nil())),
//    R.from([succ, succ], 'Vec (Nat -> Nat)'), //?
    R.from([1,0], 'Vec Nat')
  );
  console.log(result.valueOf())
  // [2, 1]
  console.log(result.toString())
  // 2 :: 1 :: <>

  // Internal representations
  console.log(result.typeOf())
  // <TC:Vec <TC:Nat> 2>
  console.log(result.quote())
  // DC:Cons (DC:S (DC:S (DC:Z))) (DC:Cons (DC:S (DC:Z)) (DC:Nil))
});

// let/where bindings
let mirror = new R
  .Sig('mirror', '{a : Type} -> List a -> List a')
  .Def(
    "@ xs := xs ++ xs'",
    "xs' := reverse xs"
  )

// case bindings
let lookupDefault = new R
  .Sig('lookupDefault', '{a : Type} -> Nat -> List a -> a -> a')
  .Def(
    { '@ i xs def := list_lookup i xs': [
      'Nothing := def',
      'Just x  := x'
    ] }
  )

// do syntax?

// mixfix syntax?
let Sigma = new R.Data(
  'Sigma', '(a : Type)(b : a -> Type) : Type',
  [ '[_|_] : (x : a) -> b x -> Sigma a b' ]
)

// records
let Functor = new R.Record(
  'Functor', '(f : Type -> Type) : Type',
  [ { 'map : {a, b : Type} -> (a -> b) -> f a -> f b':
    o => o.map } ] // This is important!!
)
// infixes?
let Applicative = new R.Record(
  'Applicative', '(f : Type -> Type) : Type',
  [ 'pure : {a : Type} -> a -> f a'
    '(<*> l2) : {a, b : Type} -> f (a -> b) -> f a -> f b' ]
)

// implementations
R.ready.then(async () => {
  Functor(
    '{f : Type -> Type} -> Applicative f',
    'map g x := pure g <*> x'
  )
  await R.ready;
})

// proof example
let Id = new R.Type(
  'Id', '(a : Type) : a -> Type',
  [ 'Refl : {x : a} -> (= r4) x x' ]
)
let cong = new R
  .Sig('cong', '{a b : Type}{x, y : a} -> (f : a -> b) -> x = y -> f x = f y')
  .Def('@ f Refl := Refl')

// To use the following signature, make sure pattern matching doesn't imply K
// vecsEqLength : (xs : Vect a n) -> (ys : Vect a m) -> (xs = ys) -> n = m
let VecEq = new R.Namespace(n => ({
  EqVecs: n.Data(
    '(~=~ r4)', 'Vec a n -> Vec a m -> Type',
    [ 'NilCong : Nil ~=~ Nil',
      'ConsCong x y : {xs, ys} -> (x = y) -> (xs ~=~ ys) -> Cons x xs ~=~ Cons y ys' ]
  ),
  vecsEqLength: n
    .Sig('vecsEqLength', '{n m : Nat}{xs : Vec a n}{ys : Vec a m} -> (xs ~=~ ys) -> n = m')
    .Def(
      '@ NilCong := Refl',
      '@ (ConsCong _ e) := cong S (vecsEqLength e)'
    )
}));

R.ready.then(async () => {

})

// After cubical...
let funext = R
  .Sig('funext', '{a : Type}{b : a -> Type}{f g : (x : a) -> b x} -> Type -> Type')
  .Def('@ := {x} -> (f x = g x) -> f = g')
```
