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
      ctors.forEach(({ctorname, typecon, toString = () => `[${ctorname} ${typename}]`}) => {
        let cap = ctorname.charAt(0).toUpperCase() + ctorname.slice(1);
        Object.assign(this, { [ctorname] (...ctorargs) { return new this[cap](...ctorargs) } });
        Object.defineProperty(this, cap, { get () {
          return ({ [cap]: class extends klass {
            _typecon = [this[cap], ...typecon(...(self._typecon === null ?
              typeconArgs : self._typecon.slice(-1)[0].slice(1)))]; // BUG: flat; use closure as Context; requires AST
            toString = toString;
            constructor (...ctorargs) {
              super(...(typecon(...(self._typecon === null ? typeconArgs : self._typecon.slice(-1)[0].slice(1))).slice(-1)[0].slice(1)))
              if (!testCtor(self, klass)) ctorargs.push(self);
              try { this._init(...ctorargs) }
              catch (e) { console.log(e); throw new Error(`Cannot form term ${ctorname} of ${typename}`) }
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

let Vector = makeType('Vector', {params: ['Function'], indexes: ['Number']}, [
  {ctorname: 'nil', typecon: a => [['Vector', a, 0]], toString: () => '<>'},  // Pi(Function, App(App(Vector, Bound(0)), new Nat().zero()))
  {ctorname: 'cons', typecon: (a, n) => [a, ['Vector', a, n], ['Vector', a, n + 1]], // Pi(Function, Pi(Nat, Lam(Lam(...etc...))))
    toString () { return `${this[0].toString()} :: ${this[1].toString()}`}}
]);

let List = makeType('List', {params: ['Function']}, [
  {ctorname: 'nil', typecon: a => [[List, a]], toString: () => '[]'},
  {ctorname: 'cons', typecon: a => [a, [List, a], [List, a]],
    toString () { return `${this[0].toString()} : ${this[1].toString()}` }}
]);


//Typecheck
class Context extends Map {
  sigs = []
  defs = []
  cons (k, v, isSig) {
    let ret = new Context(this);
    ret.set(k, v);
    ret.sigs = this.sigs.slice();
    ret.defs = this.defs.slice();
    ret[isSig ? 'sigs' : 'defs'].push(k)
    return ret
  }
  push (k, v, isSig) {
    this.set(k, v);
    this[isSig ? 'sigs' : 'defs'].push(k);
    return this
  }
  '!!' (i) {
    return this.get(this.sigs[this.sigs.length - i - 1])
  }
  lookup (val, isSig) {
    let which = isSig ? 'sigs' : 'defs';
    for (let k of this[which]) if (k.equal(val)) return this.get(k)
  }
};

function AST (...args) {
  return class {
    constructor (arg) {
      let kv = Object.entries(arg);
      if (kv.length !== 1) throw new Error('Too many constructors');
      if (!~args.indexOf(kv[0][0])) throw new Error('Not a valid constructor');
      [this.ctor, this.value] = kv[0]
    }
  }
}
class Term extends AST('ann', 'star', 'pi', 'lam', 'app', 'boundvar', 'freevar') {
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
      case 'freevar': return `Free ${this.value[0]}`
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
class Decl extends AST('sig', 'def') {}

function typecheck (ctx, string, term) {
  let name = new Name({global: [string]}),
      mbType = ctx.lookup(name, true);
  if (mbType) {
    return check(ctx, term, mbType.value[0])
      .then(type => {
        let value = evaluate(ctx, term);
        ctx.push(name, value, false);
        //let ret = string + ' : ' + print(quote(mbType.value[0]))
        return quote(mbType.value[0]).toString()
      })
      .catch(e => {
        throw new Error(e.message + `\nwhen checking term ${term.toString()}\nagainst type ${quote(mbType).toString()}`)
      })
  } else {
    return infer(ctx, term).then(type => {
      let value = evaluate(ctx, term);
      ctx.push(name, type, true).push(name, value, false);
      //let ret = string + ' : ' + print(quote(type.value[0]))
      return quote(type.value[0]).toString()
    })
  }
}

function infer (ctx, term, index = 0) {
  return Promise.resolve().then(() => {
    switch (term.ctor) {
      case 'star': return new RType({value: [new Value({vstar: []})]});
      case 'ann': return check(ctx, term.value[1], new Value({vstar: []}), index)
        .catch(e => { console.log(e);throw new Error(e.message + '\nAnnotation should have type Type') })
        .then(() => {
          let type = evaluate(ctx, term.value[1]);
          return check(ctx, term.value[0], type, index)
            .then(() => new RType({value: [type]}))
        });
      case 'pi': return infer(ctx, term.value[0], index)
        .then(type1 => {
          if (type1.value[0].ctor !== 'vstar') throw new Error('Pi domain should have type Type');
          return infer(
            ctx.cons(new Name({local: [index]}), new RType({value: [evaluate(ctx, term.value[0])]}), true),
            subst(new Term({freevar: [new Name({local: [index]})]}), term.value[1]), index + 1)
            .then(type2 => {
              if (type2.value[0].ctor !== 'vstar') throw new Error('Pi range should have type Type');
              return type2
            })
        });
      case 'app': return infer(term.value[0], index)
        .then(mbVPi => {
          if (mbVPi.value[0].ctor !== 'vpi') throw new Error('Illegal application');
          let [type, func] = mbVPi.value;
          return check(ctx, term.value[1], type, index)
            .then(() => new RType({value: [func(evaluate(ctx, term.value[1]))]}))
        });
      case 'freevar':
      let result = ctx.lookup(term.value[0], true);
      if (result) return result;
      else throw new Error(`Unknown identifier: ${term.value[0].value[0]}`);
      case 'lam': throw new error('Cannot infer type of lambda')
    }
  })
}

function check (ctx, term, type, index = 0) {
  return Promise.resolve().then(() => {
    switch (term.ctor) {
      case 'lam':
      if (type.ctor !== 'vpi') throw new Error(`Lambda has Pi type, not ${type.ctor}`);
      else return check(
        ctx.cons(new Name({local: [index]}), new RType({value: [type.value[0]]}), true),
        subst(new Term({freevar: [new Name({local: [index]})]}), term.value[0]),
        type.value[1](vfree(new Name({local: [index]}))), index + 1)
      default: return infer(ctx, term, index)
        .then(res => {
          if (!quote(res.value[0]).equal(quote(type))) throw new Error('Type mismatch');
          else return new RType({value: [type]})
        })
    }
  })
}

function evaluate (ctx, term) {
  switch (term.ctor) {
    case 'star': return new Value({vstar: []});
    case 'ann': return evaluate(ctx, term.value[0]);
    case 'pi': return new Value({vpi: [
      evaluate(ctx, term.value[0]),
      x => evaluate(ctx.cons(new Name({global: ['']}), new RType({value: [x]}), true), term.value[1])
    ]});
    case 'lam': return new Value({vlam: [
      x => evaluate(ctx.cons(new Name({global: ['']}), new RType({value: [x]}), true), term.value[0])
    ]});
    case 'app': return vapply(evaluate(ctx, term.value[0]), evaluate(ctx, term.value[1]));
    case 'boundvar': return ctx['!!'](term.value[0]).value[0];
    case 'freevar':
    let mbVal = ctx.lookup(term.value[0], false);
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
    case 'vlam': return value1.value[1](value2);
    case 'vneutral': return new Value({vneutral: [new Neutral({napp: [value1.value[0], value2]})]});
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
    case 'vlam': return new Term({lam: [quote(value.value[0](vfree(new Name({quote: [index]}))), index + 1)]});
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
