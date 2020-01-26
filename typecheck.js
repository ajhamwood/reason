function testInteger (n) { return Number(n) === n && n % 1 === 0 }
function testCtor (obj, ctor) { return typeof obj !== 'undefined' && obj.constructor === ctor }
function testExtendedCtor (obj, ctor) { return typeof obj !== 'undefined' && ctor.isPrototypeOf(obj.constructor) }
function test (obj, ctor) { return testCtor(obj, ctor) || testExtendedCtor(obj, ctor) }


class Eq {
  // fantasy-land Setoid
  equal (value) {
    if (this.constructor !== value.constructor) return false;
    for (let a in this) {
      if (this[a] !== value[a] && (typeof this[a] !== 'object' || 'equal' in this[a] && !this[a].equal(value[a]))) return false
    }
    return true
  }
}

class Type extends Eq {
  _typedef = { params: [], indexes: [] }
  _typecon = null
  _init (...args) { // TODO: handle _typecon
    if (this._typecon === null) {
      let { params, indexes } = this._typedef,
          a = params.findIndex(x => test(x, String)), b = !!indexes.length - 1;
      for (let arg of args) {
        if (a != -1) {
          if (!test(arg, globalThis[params[a]])) throw new Error('Type mismatch')
          params[a] = {[params[a]]: arg};
          a === params.length - 1 ? a = -1 : a++
        }
        else if (b != -1) {
          if (!test(arg, globalThis[indexes[b]])) throw new Error('Type mismatch')
          indexes[b] = {[indexes[b]]: arg};
          b === indexes.length - 1 ? b = -1 : b++
        }
        else throw new Error('Too many arguments')
      }
    } else {
      // TODO: Actual typechecking...
      let equalType = (type1, type2) => type1.every((v, i) => v === type2[i] ||
        test(v, Array) && test(type2[i], Array) && equalType(v, type2[i]));
      if (args.length >= this._typecon.length) throw new Error('Too many arguments')
      args.forEach((arg, i) => {
        if (!(test(arg, this._typecon[i + 1])) && !equalType(arg._typecon.slice(-1)[0], this._typecon[i + 1]))
          throw new Error('Type mismatch')
      })
    }
  }
}


function makeType (typename, { params = [], indexes = [] }, ctors) {
  let klass;
  return klass = ({ [typename]: class extends Type {
    _typedef = { params: params.slice(), indexes: indexes.slice() }
    constructor (...typeargs) {
      super();
      try { this._init(...typeargs) }
      catch (e) { console.log(e); throw new Error(`Cannot form type ${typename}`) }
      let self = this, typeconArgs = this._typedef.params.concat(this._typedef.indexes)
        .filter(x => !test(x, String)).map(x => Object.values(x)[0]);
      ctors.forEach(({ctorname, typecon, ...builtins}) => {
        let cap = ctorname.charAt(0).toUpperCase() + ctorname.slice(1);
        Object.assign(this, { [ctorname] (...ctorargs) { return new this[cap](...ctorargs) } });
        Object.defineProperty(this, cap, { get () {
          return ({ [cap]: class extends klass {
            _typecon = [this[cap], ...typecon(...(self._typecon === null ?
              typeconArgs : self._typecon.slice(-1)[0].slice(1)))]; // BUG: flat; use closure as Context; requires AST
            toString = () => `[${ctorname} ${typename}]`;
            constructor (...ctorargs) {
              super(...(typecon(...(self._typecon === null ? typeconArgs : self._typecon.slice(-1)[0].slice(1))).slice(-1)[0].slice(1)))
              if (!testCtor(self, klass)) ctorargs.push(self);
              try { this._init(...ctorargs) }
              catch (e) { console.log(e); throw new Error(`Cannot form term ${ctorname} of ${typename}`) }
              for (let m in builtins) this[m] = builtins[m];
              Object.defineProperties(this, this._typecon.slice(1, -1).reduce((a, x, i) =>
                ({ ...a, [i]: { get () { return ctorargs[i] }, enumerable: true } }), {}))
            }
          } })[cap]
        } })
      })
    }
    toString () { return `[${typename}]` }
  } })[typename]
}

let _Vector = makeType('_Vector', {params: ['Function'], indexes: ['Number']}, [
  {ctorname: 'nil', typecon: a => [['_Vector', a, 0]], toString: () => '<>'},  // Pi(Function, App(App(Vector, Bound(0)), new Nat().zero()))
  {ctorname: 'cons', typecon: (a, n) => [a, ['_Vector', a, n], ['_Vector', a, n + 1]], // Pi(Function, Pi(Nat, Lam(Lam(...etc...))))
    toString () { return `${this[0].toString()} :: ${this[1].toString()}`}}
]);

let _List = makeType('_List', {params: ['Function']}, [
  {ctorname: 'nil', typecon: a => [[_List, a]], toString: () => '[]'},
  {ctorname: 'cons', typecon: a => [a, [_List, a], [_List, a]],
    toString () { return `${this[0].toString()} : ${this[1].toString()}` }}
]);

let _Nat = makeType('_Nat', {}, [
  {ctorname: 'zero', typecon: () => [[_Nat]], toString: () => 'Z', valueOf: () => 0 },
  {ctorname: 'succ', typecon: () => [[_Nat], [_Nat]],
    toString () { return 'S ' + this[0].toString() },
    valueOf () { return this[0] + 1 }}
])


// Main closure

var R = (() => {

  // Parser

  class Data {
    constructor (typeDef, ctors = []) {
      let klass, { typeName, typeSig = [] } = typeDef;
      if (!typeName || !typeof typeName === 'string') throw new Error('Bad type name');
      // typecheck should go here
      return klass = ({ [typeName]: class {
        sig = new Tele(...typeSig)
        ctor = typeName
        constructor (...typeParams) {
          let init = (...params) => {
            console.log(this.sig, params)
            return true
          }
          this.state = 'unchecked';
          try { init(...typeParams) }
          catch (e) { throw new Error(`Cannot form type ${name}`) }
          let data = new Decl({data: [
            new Name({global: [typeName]}),
            this.sig,
            ctors.map(({ctorName, ctorSig = [], ...builtins}) => {
              let lcname = ctorName.charAt(0).toLowerCase() + ctorName.slice(1);
              this[lcname] = (...args) => new ({ [ctorName]: class extends klass {
                con = new Tele(...ctorSig)
                ctor = ctorName
                constructor () {
                  super(...ctorSig);
                  try { init(...args) }
                  catch (e) { throw new Error(`Cannot form term ${ctorName} of ${typeName}`) }
                  Object.assign(this, builtins);
                  //this.value = args.map(str => context.lookup(new Name({global: [str]}), 'def')) //?
                  this.value = args
                }
              } })[ctorName]();
              return new Ctor({ctor: [new Name({global: [ctorName]}), new Tele(...ctorSig)]})
            })
          ]});
          typecheck(data).then(res => {
            console.log(res)
            this.state = 'checked'
          }).catch(e => {
            console.log(e);
            this.state = 'failed'
          })
        }
        toString () { return `[${typeName}]` }
      } })[typeName]
    }
  };
  class Sig {
    constructor (string, hint) {
      let pipe = (r => p => r = r.then(p))(Promise.resolve());
      pipe(() => typecheck(new Decl({sig: [ new Name({global: [string]}), hint ]})))
      Object.assign(this, {
        name: new Name({global: [string]}),
        Def: expr => {
          pipe(() => typecheck(new Decl({def: [ new Name({global: [string]}), expr ]})))
            .then(type => Object.assign(this, {
              type, expr, state: 'checked',
              apply: (...args) => typecheck(new Decl({def: [ new Name({global: ['self']}),
                args.reduce((a, x) => new Term({app: [x, a]}), expr) ]}))
            }));
          this.state = 'unchecked';
          return this
        }
      })
    }
  };


  // Abstract syntax tree

  class Context {
    indices = []
    mode = 'term'
    globals = 0 // Is there any utility to keeping track of local/global context?
    fresh = (i => () => i++)(0)
    cons (decl, g) {
      let ret = new Context(this);
      (ret.indices = this.indices.slice()).push(decl);
      ret.mode = this.mode;
      if (g) ret.globals++;
      return ret
    }
    push (decl) {
      this.indices.push(decl);
      this.globals++;
      return this
    }
    concatTele (tele) {
      let ret = new Context(this);
      for (let i of tele.items) switch (i.ctor) {
        case 'term': ret = ret.cons(new Decl({sig: i.value}), false);
        break;
        case 'constraint': ret = ret.cons(new Decl({def: [i.value[0].value[0], i.value[1]]}), false)
      }
      return ret
    }
    '!!' (i) {
      return this.indices[this.indices.length - i - 1].value[1]
    }
    lookup (name, ctor) {
      let ret = this.indices.find(decl => ctor === 'ctor' ?
        (decl.ctor === 'data' && decl.value[2].find(dcon => dcon.value[0].equal(name))) :
        (decl.ctor === ctor && decl.value[0].equal(name)));
      if (ret) return ret.value[1]
    }
    lookupAll (name) {
      return this.indices.flatMap(decl => decl.ctor === 'data' ? decl.value[2].slice().push(decl) : decl)
         .filter(x => x.value[0].equal(name))
    }
    mode (m) {
      if (m === 'term' || m === 'pat') this.mode = m;
      else throw new Error(`Illegal context mode '${m}'`)
    }
    getIndices () { return indices }
  };

  function AST (...args) {
    return class {
      constructor (arg) {
        let kv = Object.entries(arg);
        if (kv.length !== 1) throw new Error('Wrong number of constructors');
        if (!~args.indexOf(kv[0][0])) throw new Error(`${kv[0][0]} not a valid constructor. Looking for: ${args.join(', ')}`);
        [this.ctor, this.value] = kv[0]
      }
    }
  }
  class Term extends AST('ann', 'star', 'pi', 'lam', 'app', 'boundvar', 'freevar'
    // ,'tcon', 'dcon'
    ) {
    equal (operand) {
      return this.ctor === operand.ctor &&
        this.value.every((x, i) => x === operand.value[i] || x.equal(operand.value[i]))
    }
    toString () {
      switch (this.ctor) {
        case 'ann': return `(${this.value[0].toString()} : ${this.value[1].toString()})`;
        case 'star': return 'Type';
        case 'pi': return `Pi(${this.value[0].toString()}, ${this.value[1].toString()})`;
        case 'lam': return `Lam(${this.value[0].toString()})`;
        case 'app': return `${this.value[0].toString()} :@: ${this.value[1].toString()}`;
        case 'boundvar': return `Bound ${this.value[0]}`;
        case 'freevar': return `Free ${this.value[0]}`;
        //
        // case 'tcon':
        // case 'dcon': return `${this.value[0].value[0]} :@: ${this.value.slice(1).map(x => x.toString()).join(' :@: ')}`;
      }
    }
  }
  class Name extends AST('global', 'local', 'quote') {
    equal (operand) {
      return this.ctor === operand.ctor && this.value[0] === operand.value[0]
    }
  }
  class Value extends AST('vlam', 'vstar', 'vpi', 'vneutral') {}
  class Neutral extends AST('nfree', 'napp') {}
  class RType extends AST('value') {}

  class Decl extends AST('sig', 'def', 'recdef', 'data', 'datasig') {}
  class Ctor extends AST('ctor') {}

  class Item extends AST('term', 'constraint') {} // Better name pls
  class Tele { // TODO: meaningfully distinguish params/indices
    items = []
    constructor (...items) {
      /*
      'x:A'   => new TeleItem({term: [new Term({ann: ['x', 'A']})]}) etc
      'A'     => new TeleItem({term: [new Term({freevar: ['A']})]})  ??
      '{x:A}' => Erased
      '{A}'   => Erased?
      '{a=b}' => new TeleItem({constraint: [parse(a), parse(b)]})    ??
      */
      for (let item of items) this[item.ctor](item)
    }
    term (item) { this.items.push(item) }
    constraint (item) { this.items.push(item) }
  }

  class Epsilon extends AST('runtime', 'erased') {} // replace Term/Value ?
  class Arg extends AST('arg') {}                 　//


  // Type checker

  function typecheck (decl, ctx = context) {
    let [name, term, ctors] = decl.value;
    switch (decl.ctor) {
      case 'sig':
      //dup?
      //whnf
      return check(ctx, term, new Value({vstar: []}))
        .then(() => ctx.push(new Decl({sig: [name, evaluate(term, ctx)]})))

      case 'def':
      if (typeof ctx.lookup(name, 'def') === 'undefined') {
        let mbType = ctx.lookup(name, 'sig');
        return typeof mbType === 'undefined' ?
          infer(ctx, term).then(type =>
            ctx.push(new Decl({sig: [name, type]}))
              .push(new Decl({def: [name, evaluate(term, ctx)]}))
          ) :
          check(ctx, term, mbType).then(type => // recursive?
            ctx.push(new Decl({def: [name, evaluate(term, ctx)]}))
          )
      } else throw new Error(name.value[0] + ' already defined');

      case 'data':
      return tcTele(ctx, term).then(tele =>
        Promise.all(ctors.map(ctor =>
          tcTele(ctx.cons(new Decl({datasig: [name, tele]})).concatTele(tele), ctor.value[1])
            .then(ctele => new Ctor({ctor: [ctor.value[0], ctele]}))
        )).then(ctors => {
          let decl = new Decl({data: [name, tele, ctors]});
          ctx.push(decl);
          return decl
        })
      )

      case 'recdef':
      case 'datasig': throw new Error('Internal construct')
    }
  }

  function tcTele (ctx, tele) { // returns a Value...?
    // TODO: convert to sync code
    return Promise.all(tele.items.map(term => {
      switch (tele.ctor) {
        case 'constraint':
        return infer(ctx, tele.value[0])
          .then(type => check(ctx, tele.value[1], type))
          .then(type => constraintToDecls(ctx, ...tele.value))
          .then(decls => (decls.forEach(decl => ctx = ctx.cons(decl, false)), decls))
          .then(decls => [term, ...decls])

        case 'term':  // TODO: combine explicit and implicit bindings
        return term.ctor === 'ann' ?
          infer(ctx, term).then(type =>
            ctx = ctx.cons(new Decl({sig: [term.value[0].value[0], type]}), false)) :
          check(ctx, term, new Term({star: []})).then(type =>
            // wildcard names are numbers
            ctx = ctx.cons(new Decl({sig: [new Name({global: [ctx.fresh()]}), type]}), false))
        // Erased
      }
    })).then(ar => new Tele(...ar.flat()))
  }

  function constraintToDecls (ctx, term1, term2) {
    let lhnf = whnf(term1), rhnf = whnf(term2), decls = [];
    console.log(lhnf, rhnf)
    if (lhnf.equal(rhnf)) return decls;
    else {
      if (lhnf.ctor === 'app' && rhnf.ctor === 'app') {
        decls = decls.concat(constraintToDecls(ctx, lhnf.value[0], rhnf.value[0]));
        decls = decls.concat(constraintToDecls(ctx, lhnf.value[1], rhnf.value[1]));
      }
      else if (lhnf.ctor === 'freevar') return [ new Decl({def: [lhnf.value[0], rhnf]}) ];
      else if (rhnf.ctor === 'freevar') return [ new Decl({def: [rhnf.value[0], lhnf]}) ];
      else throw new Error(`Cannot equate lhs and rhs of constraint ${lhnf.toString()} = ${rhnf.toString()}`)
    }
  }

  function whnf (ctx, term) {
    switch (term.ctor) {
      case 'freevar':
      let mbDef = ctx.lookup(term.value[0], 'def');
      return typeof mbDef === 'undefined' ? term : whnf(ctx, mbDef);

      case 'app':
      let nf = whnf(ctx, term.value[0]);
      switch (nf.ctor) {
        case 'lam':
        let [func] = evaluate(nf.value[0], ctx).value;
        return whnf(ctx, func(term.value[1]));

        case 'freevar':
        let nf2 = whnf(ctx, term.value[1]);
        // let mbRecDef = ctx.lookup(nf.value[0], 'recdef');
        // if (typeof mbRecDef === 'undefined') return whnf(new Term({app: [mbRecDef.value[1], nf2]})); else
        return new Term({app: [nf, nf2]});

        default:
        return new Term({app: [nf, term.value[1]]})
      }

      case 'ann': throw new Error(`Unexpected term at whnf: ${term.toString()}`)
      default: return term
    }
  }

  function infer (ctx, term, index = 0) {
    return Promise.resolve().then(() => {
      switch (term.ctor) {
        case 'star': return new RType({value: [ new Value({vstar: []}) ]});

        case 'ann': return check(ctx, term.value[1], new Value({vstar: []}), index)
          .catch(e => { console.log(e);throw new Error(e.message + '\nAnnotation should have type Type') })
          .then(() => {
            let type = evaluate(term.value[1], ctx);
            return check(ctx, term.value[0], type, index)
              .then(() => new RType({value: [type]}))
          });

        case 'pi': return infer(ctx, term.value[0], index)
          .then(type1 => {
            if (type1.value[0].ctor !== 'vstar') throw new Error('Pi domain should have type Type');
            return infer(
              ctx.cons(new Decl({sig: [ new Name({local: [index]}),
                new RType({value: [ evaluate(term.value[0], ctx) ]}) ]}), true),
              subst(new Term({freevar: [ new Name({local: [index]}) ]}), term.value[1]), index + 1)
              .then(type2 => {
                if (type2.value[0].ctor !== 'vstar') throw new Error('Pi range should have type Type');
                return type2
              })
          });

        case 'app': return infer(ctx, term.value[0], index)
          .then(mbVPi => {
            if (mbVPi.value[0].ctor !== 'vpi') throw new Error('Illegal application');
            let [type, func] = mbVPi.value;
            return check(ctx, term.value[1], type, index)
              .then(() => new RType({value: [ func(evaluate(term.value[1], ctx)) ]}))
          });

        case 'freevar':
        let result = ctx.lookup(term.value[0], 'sig');
        if (result) return result;
        else throw new Error(`Unknown identifier: ${term.value[0].value[0]}`);

        case 'lam': throw new Error('Cannot infer type of lambda')
      }
    })
  }

  function check (ctx, term, type, index = 0) {
    return Promise.resolve().then(() => {
      switch (term.ctor) {
        case 'lam':
        if (type.ctor !== 'vpi') throw new Error(`Lambda has Pi type, not ${type.ctor}`);
        else return check(
          ctx.cons(new Decl({sig: [ new Name({local: [index]}), new RType({value: [type.value[0]]}) ]}), true),
          subst(new Term({freevar: [ new Name({local: [index]}) ]}), term.value[0]),
          type.value[1](vfree(new Name({local: [index]}))), index + 1)

        default: return infer(ctx, term, index)
          .then(res => {
            if (!quote(res.value[0]).equal(quote(type))) throw new Error('Type mismatch');
            else return new RType({value: [type]})
          })
      }
    })
  }

  function evaluate (term, ctx = context) {
    switch (term.ctor) {
      case 'star': return new Value({vstar: []});

      case 'ann': return evaluate(term.value[0], ctx);

      case 'pi': return new Value({vpi: [
        evaluate(term.value[0], ctx),
        x => evaluate(term.value[1],
          ctx.cons(new Decl({sig: [ new Name({global: ['']}), new RType({value: [x]}) ]}), false))
      ]});

      case 'lam': return new Value({vlam: [
        x => evaluate(term.value[0],
          ctx.cons(new Decl({sig: [ new Name({global: ['']}), new RType({value: [x]}) ]}), false))
      ]});

      case 'app': return vapply(evaluate(term.value[0], ctx), evaluate(term.value[1], ctx));

      case 'boundvar': return ctx['!!'](term.value[0]).value[0];

      case 'freevar':
      let mbVal = ctx.lookup(term.value[0], 'def');
      if (mbVal) return mbVal;
      else return vfree(term.value[0])
    }
  }

  function subst (term1, term2, index = 0) {
    switch (term2.ctor) {
      case 'star': return term2;

      case 'ann': return new Term({ann: [
        subst(term1, term2.value[0], index),
        subst(term1, term2.value[1], index)
      ]});

      case 'pi': return new Term({pi: [
        subst(term1, term2.value[0], index),
        subst(term1, term2.value[1], index + 1)
      ]});

      case 'lam': return new Term({lam: [subst(term1, term2.value[0], index + 1)]});

      case 'app': return new Term({app: [
        subst(term1, term2.value[0], index),
        subst(term1, term2.value[1], index)
      ]});

      case 'boundvar': return index === term2.value[0] ? term1 : term2;

      case 'freevar': return term2
    }
  }

  function vfree (name) {
    return new Value({vneutral: [new Neutral({nfree: [name]})]})
  }

  function vapply (value1, value2) {
    switch (value1.ctor) {
      case 'vlam': return value1.value[0](value2);

      case 'vneutral': return new Value({vneutral: [
        new Neutral({napp: [value1.value[0], value2]})]});

      default: throw new Error('Bad value application')
    }
  }

  function quote (value, index = 0) {
    switch (value.ctor) {
      case 'vstar': return new Term({star: []});

      case 'vpi': return new Term({pi: [
        quote(value.value[0], index),
        quote(value.value[1](vfree(new Name({quote: [index]}))), index + 1)
      ]});

      case 'vlam': return new Term({lam: [
        quote(value.value[0](vfree(new Name({quote: [index]}))), index + 1)]});

      case 'vneutral': return nquote(value.value[0], index)
    }
  }

  function nquote (neutral, index) {
    switch (neutral.ctor) {
      case 'nfree': return boundfree(neutral.value[0], index);

      case 'napp': return new Term({app: [
        nquote(neutral.value[0], index),
        quote(neutral.value[1], index)
      ]})
    }
  }

  function boundfree (name, index) {
    switch (name.ctor) {
      case 'quote': return new Term({boundvar: [index - name.value[0] - 1]});

      default: return new Term({freevar: [name]})
    }
  }

  let context = new Context();
  return { Context, context, Data, Sig, Term, Name, Decl, Item, typecheck, evaluate, quote }

})();


// Test cases

var id = new R.Sig('id',
  new R.Term({pi: [
    new R.Term({star: []}),
    new R.Term({pi: [
      new R.Term({boundvar:[0]}),
      new R.Term({boundvar:[1]})
    ]})
  ]})
).Def(
  new R.Term({lam: [
    new R.Term({lam: [
      new R.Term({boundvar:[0]})
    ]})
  ]})
);


var Void = new R.Data({ typeName: 'Void'});

var Unit = new R.Data({ typeName: 'Unit' }, [
  { ctorName: 'tt', toString: () => '()', valueOf: () => null }
]);

// var Bool = new R.Data({ typeName: 'Bool' }, [
//   { ctorName: 'T', toString: () => 'T', valueOf: () => true },
//   { ctorName: 'F', toString: () => 'F', valueOf: () => false }
// ]);
//
// var Nat = new R.Data({ typeName: 'Nat' }, [
//   { ctorName: 'Z', toString: () => 'Z', valueOf: () => 0 },
//   { ctorName: 'S', ctorSig: [
//       new R.Item({term: [ new R.Term({freevar: [ new R.Name({global: ['Nat']}) ]}) ]})
//     ],
//     toString () { return 'S' + this.value[0].toString() },
//     valueOf () { return this.value[0].valueOf() + 1 } }
// ]);
//
// var List = new R.Data({ typeName: 'List', typeSig: [
//     new R.Item({term: [ new R.Term({ann: [
//       new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
//       new R.Term({star: []})
//     ]}) ]})
//   ] }, [
//   { ctorName: 'Nil', toString: () => '[]', valueOf: () => [] },
//   { ctorName: 'Cons', ctorSig: [
//       new R.Item({term: [ new R.Term({freevar: [ new R.Name({global: ['A']}) ]}) ]}),          // Erased!
//       new R.Item({term: [ new R.Term({app: [
//         new R.Term({freevar: [ new R.Name({global: ['List']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['A']}) ]})
//       ]}) ]})
//     ],
//     toString () { return this.value[0].toString() + ' : ' + this.value[1].toString() },
//     valueOf () { return this.value[1].concat([this.value[0]]) } }
// ]);
//
// var Vec = new R.Data({ typeName: 'Vec', typeSig: [
//     new R.Item({term: [ new R.Term({ann: [
//       new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
//       new R.Term({star: []})
//     ]}) ]}),
//     new R.Item({term: [ new R.Term({ann: [
//       new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//       new R.Term({freevar: [ new R.Name({global: ['Nat']}) ]})
//     ]}) ]})
//   ] }, [
//   { ctorName: 'Nil', ctorSig: [
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['Z']}) ]})
//       ]})
//     ],
//     toString: () => '<>', valueOf: () => [] },
//   { ctorName: 'Cons', ctorSig: [
//       new R.Item({term: [ new R.Term({ann: [
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['Nat']}) ]})
//       ]}) ]}),                                                        // Erased!
//       new R.Item({term: [ new R.Term({freevar: [ new R.Name({global: ['A']}) ]}) ]}),
//       new R.Item({term: [ new R.Term({app: [
//         new R.Term({app: [
//           new R.Term({freevar: [ new R.Name({global: ['Vec']}) ]}),
//           new R.Term({freevar: [ new R.Name({global: ['A']}) ]})
//         ]}),
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]})
//       ]}) ]}),
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({app: [
//           new R.Term({freevar: [ new R.Name({global: ['S']}) ]}),
//           new R.Term({freevar: [ new R.Name({global: ['m']}) ]})
//         ]})
//       ]})
//     ],
//     toString () { return this.value[0].toString() + ' :: ' + this.value[1].toString() },
//     valueOf () { return this.value[1].concat([this.value[0]]) } }
// ]);
//
// var Fin = new R.Data({ typeName: 'Fin', typeSig: [
//     new R.Item({term: [ new R.Term({ann: [
//       new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//       new R.Term({freevar: [ new R.Name({global: ['Nat']}) ]})
//     ]}) ]})
//   ] }, [
//   { ctorName: 'Zero', ctorSig: [
//       new R.Item({term: [ new R.Term({ann: [
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['Nat']}) ]})
//       ]}) ]}),                                                       // Erased!
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({app: [
//           new R.Term({freevar: [ new R.Name({global: ['S']}) ]}),
//           new R.Term({freevar: [ new R.Name({global: ['m']}) ]})
//         ]})
//       ]})
//     ],
//     toString: () => `Zero [${this.value[0].toString()}]`,
//     valueOf: () => this.value[0].valueOf() - 1 },
//   { ctorName: 'Succ', ctorSig: [
//       new R.Item({term: [ new R.Term({ann: [
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['Nat']}) ]})
//       ]}) ]}),                                                       // Erased!
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({app: [
//           new R.Term({freevar: [ new R.Name({global: ['S']}) ]}),
//           new R.Term({freevar: [ new R.Name({global: ['m']}) ]})
//         ]})
//       ]}),
//       new R.Item({term: [ new R.Term({app: [
//         new R.Term({freevar: [ new R.Name({global: ['Fin']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]})
//       ]}) ]})
//     ],
//     toString: () => `Succ [${this.value[1].valueOf() - 1}] ` + this.value[1].toString(),
//     valueOf: () => this.value[1].valueOf() - 1 }
// ])
