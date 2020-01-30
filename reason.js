var R = (() => {

  // Declarations

  class Readyable { constructor (target, handler) {
    return {
      proxy: new Proxy(({ nop () {} }).nop, new Proxy(Object.create(null), {
        get (_, prop) { return (...as) => (prop in handler ? handler[prop] : Reflect[prop])
          .apply(null, [target, ...as.slice(1)]) }
      })),
      setProxy (t, h) { [target, handler] = [t || target, h || handler] }
    }
  } };
  class Data extends Readyable {
    constructor ({ typeName, typeSig = [], ...tbuiltins }, ctors = []) {
      let { proxy, setProxy } = super(class {}, { get (_, prop) {
        let error = `Typechecking not yet completed for '${typeName}' (while calling '${prop}')`;
        console.warn(error);
        switch (prop) {
          case 'error': return new Error(error)
          default: return () => null
        }
      } });
      if (!typeName || !typeof typeName === 'string') throw new Error('Bad type name');
      let klass = null, ctorsObj = {},
          data = new Decl({data: [
            new Name({global: [typeName]}),
            new Tele(...typeSig),
            ctors.map(({ctorName, ctorSig = [], ...dbuiltins}) => {
              // Enforce capitalised constructor names?
              let ctorNameLower = ctorName.charAt(0).toLowerCase() + ctorName.slice(1);
              ctorsObj[ctorNameLower] = (...ctorParams) => new ({ [ctorName]: class extends klass({sig: new Tele(...ctorSig)}) {
                ctor = ctorName
                constructor () {
                  super(...ctorParams);
                  Object.assign(this, {value: ctorParams, term: new Term({dcon: [
                    new Name({global: [ctorName]}), ctorParams.map(x => x.term)
                  ]}), ...dbuiltins});
                  for (let [ctor, v] of Object.entries(ctorsObj)) if (typeof v === 'function') delete this[ctor]
                }
              } })[ctorName]();
              return new Ctor({ctor: [new Name({global: [ctorName]}), new Tele(...ctorSig)]})
            })
          ]}),
          self = Object.assign((...args) => {
            seqSync(() => setProxy(new (klass({sig: new Tele(...typeSig)}))(...args), Reflect));
            return proxy
          }, { state: 'unchecked', ctor: typeName });
      seqAsync(() => typecheck(data)
        .then(() => ctorsObj.state = 'checked') // type?
        .catch(error => Object.assign(ctorsObj, {state: 'failed', error}))
        .then(() => klass = ({sig}) => ({ [typeName]: class {
          sig = sig
          ctor = typeName
          constructor (...typeParams) {
            if (typeParams.length !== sig.length)
              throw new Error(`Wrong number of arguments provided (${typeParams.length} rather than ${sig.length})`)
            if (ctorsObj.state = 'checked') Object.assign(this, ctorsObj);
            else if (ctorsObj.state = 'failed') throw ctorsObj.error;
            Object.assign(this, {value: typeParams, term: new Term({tcon: [
              new Name({global: [typeName]}), typeParams.map(x => x.term)
            ]}), ...tbuiltins})
          }
          toString () { return `<${typeName}>` }
        } })[typeName] )
      );
      setProxy(self);
      return self
    }
  };
  class Sig extends Readyable {
    constructor (string, hint) {
      let h = { get (obj, prop) {
            if (prop in obj) return obj[prop];
            let error = `Typechecking not yet completed for ${typeof string === 'string' ? `'${string}'` : '#' + string} (while calling '${prop}')`;
            console.warn(error);
            switch (prop) {
              case 'error': return new Error(error);
              default: return null
            }
          } }, { proxy, setProxy } = super(class {}, h),
          Def = expr => {
            self = { ...self, state: 'unchecked', ctor: string };
            delete self.Def;
            let { apply } = { apply (obj, that, args) {
              let wildCard = context.fresh(), child = new Sig(wildCard);
              seqAsync(() => typecheck(new Decl({def: [ new Name({global: [ wildCard ]}),
                child.term = args.reduce((a, x) => new Term({app: [ a, x.term ]}), self.term)
              ]})).then(res => { child.Sig(quote(res.type)).Def(quote(res.value)) }));
              return child
            } };
            seqAsync(() => typecheck(new Decl({def: [ new Name({global: [string]}), expr ]}))
              .then(res => self = { ...self, ...res, state: 'checked' })
              .catch(error => self = { ...self, error, state: 'failed' }))
              .then(() => setProxy(self, { apply }));
            setProxy(self, { ...h, apply });
            return proxy
          },
          self = { term: new Term({freevar: [ new Name({global: [string]}) ]}) },
          seqTypecheck = hint => {
            self = { ...self, Def };
            delete self.Sig;
            seqAsync(() => typecheck(new Decl({sig: [ new Name({global: [string]}), hint ]}))
              .then(res => self = { ...self, ...res, state: 'checked' })
              .catch(error => self = { ...self, error, state: 'failed' }));
            setProxy(self);
            return proxy
          };
      if (typeof hint === 'undefined') self = { ...self, state: 'unchecked', Sig: seqTypecheck };
      else return seqTypecheck(hint);
      setProxy(self);
      return proxy
    }
  };


  // Syntax

  class Context {
    indices = []
    mode = 'term'
    globals = 0 // Is there any utility to keeping track of local/global context?
    fresh = (i => () => i++)(0)
    constructor (obj) { if (obj) Object.assign(this, obj) }
    cons (decl, g) { // TODO: extendLocal
      let ret = new Context(this);
      (ret.indices = this.indices.slice()).push(decl);
      ret.mode = this.mode;
      if (g) ret.globals++;
      return ret
    }
    push (decl) { // TODO: extendGlobal
      this.indices.push(decl);
      this.globals++;
      return this
    }
    concatTele (tele) {
      let ret = new Context(this);
      for (let i of tele.items) switch (i.ctor) {
        case 'term': ret = ret.cons(new Decl({sig: [i.value[0].value[0], i.value[1]]}), false);
        break;
        case 'constraint': ret = ret.cons(new Decl({def: i.value}), false)
      }
      return ret
    }
    '!!' (i) {
      return this.indices[this.indices.length - i - 1].value[1]
    }
    lookup (name, ctor, annot) {
      if (ctor === 'ctor') if (typeof annot === 'undefined') return this.indices.reduce((a, decl, tmp) => decl.ctor === 'data' &&
        (tmp = decl.value[2].find(dcon => dcon.value[0].equal(name))) ?
          (a = a.concat([{tname: decl.value[0], tcon: decl.value[1], dcon: tmp.value[1]}])) : a, []);
      else return this.indices.slice().reduce((res, decl, tmp, ar) => decl.ctor === 'data' && decl.value[0].equal(annot.value[0]) &&
        (tmp = decl.value[2].find(dcon => dcon.value[0].equal(name)).value[1]) && (ar.splice(0), res = { dcon: tmp, tcon: decl.value[1] }), null);
      let ret = this.indices.find(decl => (decl.ctor === ctor || (ctor === 'data' && decl.ctor === 'datasig')) && decl.value[0].equal(name));
      if (ret) return ret.value[1]
    }
    lookupAll (name) {
      return this.indices.flatMap(decl => decl.ctor === 'data' ? decl.value[2].slice().concat([decl]) : decl)
        .filter(x => x.value[0].equal(name))
    }
    mode (m) {
      if (m === 'term' || m === 'pat') this.mode = m;
      else throw new Error(`Illegal context mode '${m}'`)
    }
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
  class Term extends AST('ann', 'star', 'pi', 'lam', 'app', 'boundvar', 'freevar' ,'tcon', 'dcon') {
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

        case 'tcon':
        case 'dcon': return `<${this.value[0].value[0]} ${this.value.slice(1).map(x => `(${x.toString()})`).join(' ')}>`;
      }
    }
  }
  class Name extends AST('global', 'local', 'quote') {
    equal (operand) {
      return this.ctor === operand.ctor && this.value[0] === operand.value[0]
    }
  }
  class Value extends AST('vlam', 'vstar', 'vpi', 'vneutral') {}
  class Neutral extends AST('nfree', 'ntcon', 'ndcon', 'napp') {}

  class Decl extends AST('sig', 'def', 'recdef', 'data', 'datasig') {}
  class Ctor extends AST('ctor') {}

  class Item extends AST('term', 'erased', 'constraint') {} // Better name pls
  class Tele { // TODO: meaningfully distinguish params/indices
    items = []
    length = 0
    constructor (...items) {
      for (let item of items) this[item.ctor](item)
    }
    term (item) {
      this.items.push(item);
      this.length++
    }
    erased (item) { this.items.push(item) }
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
      let value, type = new Value({vstar: []}), mbType = ctx.lookup(name, 'sig');
      if (mbType && term.equal(quote(mbType))) return Promise.resolve({type, value: mbType});
      else return check(ctx, term, type).then(() => {
        ctx.push(new Decl({sig: [name, value = evaluate(term, ctx)]}));
        return {type, value}
      })

      case 'def':
      //dup?
      let mbValue = ctx.lookup(name, 'def');
      if (typeof mbValue === 'undefined') {
        let value, mbType = ctx.lookup(name, 'sig');
        return (typeof mbType === 'undefined' ?
          infer(ctx, term).then(type => {
            ctx.push(new Decl({sig: [name, type]}))
              .push(new Decl({def: [name, value = evaluate(term, ctx)]}));
            return {type, value}
          }) :
          check(ctx, term, mbType).then(() => {// recursive?
            ctx.push(new Decl({def: [name, value = evaluate(term, ctx)]}));
            return {type: mbType, value}
          }))
      } else if (term.equal(quote(mbValue))) return Promise.resolve({type: ctx.lookup(name, 'sig'), value: mbValue})
      else throw new Error(name.value[0] + ' already defined');

      case 'data':
      // dup?
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

  function tcTele (ctx, tele) {
    return Promise.all(tele.items.map(item => {
      switch (item.ctor) {
        case 'constraint':
        return infer(ctx, item.value[0])
          .then(type => check(ctx, item.value[1], type))
          .then(type => constraintToDecls(ctx, ...item.value))
          .then(decls => decls.forEach(decl => ctx = ctx.cons(decl, false)))
          .then(() => item)

        case 'term':
        case 'erased':
        let [name, type] = item.value.length === 2 ? item.value :
          [ new Term({freevar: [ new Name({global: [ctx.fresh()]}) ]}), item.value[0] ];
        return check(ctx, type, new Value({vstar: []}))
          .then(() => ctx = ctx.cons(new Decl({sig: [name.value[0], type = evaluate(type, ctx)]}), false))
          .then(() => new Item({term: [name, type]}))
      }
    })).then(tl => new Tele(...tl))
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
      return typeof mbDef === 'undefined' ? term : whnf(ctx, mbDef.value[0]);

      case 'app':
      let nf = whnf(ctx, term.value[0]);
      switch (nf.ctor) {
        case 'lam':
        let [func] = evaluate(nf.value[0], ctx).value;
        return whnf(ctx, func(term.value[1]));

        case 'freevar':
        let nf2 = whnf(ctx, term.value[1]);
        // let mbRecDef = ctx.lookup(nf.value[0], 'recdef');
        // if (typeof mbRecDef === 'undefined') return whnf(new Term({app: [mbRecDef.value[0].value[1], nf2]})); else
        return new Term({app: [nf, nf2]});

        default:
        return new Term({app: [nf, term.value[1]]})
      }

      case 'ann': throw new Error(`Unexpected term at whnf: ${term.toString()}`)
      default: return term
    }
  }

  function tcArgTele (ctx, terms, tele) { // treat telescope bindings as functions?
    let rtele = new Tele(...tele.items), eterms = [],
        loop = i => {
          if (rtele.items.length === 0) return Promise.resolve();
          switch (rtele.items[0].ctor) {
            case 'constraint':
            if (!item.value[0].equal(item.value[1])) throw new Error(`Expected ${item.value[1]} but found ${item.value[0]}`)
            rtele.items.shift();
            return loop(i + 1)

            case 'erased':
            case 'term': // runtime/erasure must match
            return check(ctx, terms[i], rtele.items[0].value[1])
              .then(() => ritems = new Tele(...doSubst(ctx, [[rtele.items.shift().value[0], terms[i]]], rtele)))
              .then(() => eterms.push(terms[i])).then(() => loop(i + 1))
          }
        }
    return loop(0).then(() => eterms)
  }

  function doSubst (ctx, nameTerms, tele) {
    return tele.items.map(item => {
      switch (item.ctor) {
        case 'constraint':
        let sitem = item.map(x => nameTerms.reduce((acc, [name, term]) => sub(name, term, acc), x));
        constraintToDecls(ctx, ...sitem.value)
          .forEach(decl => ctx = ctx.cons(decl, false))
        return new Item({constraint: sitem})

        case 'erased':
        case 'term':
        return new Item({[item.ctor]: [item.value[0], whnf(ctx, nameTerms.reduce((acc, [name, term]) => sub(name, term, acc), item.value[1]))]})
      }
    })
  }

  function sub (name, term1, term2) { // TODO: incorporate into subst
    switch (term2.ctor) {
      case 'star': return term2;

      case 'ann': return new Term({ann: [
        sub(name, term1, term2.value[0]),
        sub(name, term1, term2.value[1])
      ]});

      case 'pi': return new Term({pi: [
        sub(name, term1, term2.value[0]),
        sub(name, term1, term2.value[1])
      ]});

      case 'lam': return new Term({lam: [ sub(name, term1, term2.value[0]) ]});

      case 'app': return new Term({app: [
        sub(name, term1, term2.value[0]),
        sub(name, term1, term2.value[1])
      ]});

      case 'boundvar': return term2;

      case 'freevar': return name === term2.value[0] ? term1 : term2
    }
  }

  function substTele (ctx, tele1, terms, tele2) {
    return doSubst(ctx, tele1.items.map((item, i) => {
      switch (item.ctor) {
        case 'term': return [item.value[0], terms[i]];
        default: throw new Error('Internal error: substTele given illegal arguments')
      }
    }), tele2)
  }

  function infer (ctx, term, index = 0) {
    return Promise.resolve().then(() => {
      let result;
      switch (term.ctor) {
        case 'star': return new Value({vstar: []});

        case 'ann': return check(ctx, term.value[1], new Value({vstar: []}), index)
          .catch(e => { throw new Error(e.message + '\nAnnotation should have type Type') })
          .then(() => {
            let type = evaluate(term.value[1], ctx);
            return check(ctx, term.value[0], type, index)
              .then(() => type)
          });

        case 'pi': return infer(ctx, term.value[0], index)
          .then(type1 => {
            if (type1.ctor !== 'vstar') throw new Error('Pi domain should have type Type');
            return infer(
              ctx.cons(new Decl({sig: [ new Name({local: [index]}), evaluate(term.value[0], ctx) ]}), true),
              subst(new Term({freevar: [ new Name({local: [index]}) ]}), term.value[1]), index + 1)
              .then(type2 => {
                if (type2.ctor !== 'vstar') throw new Error('Pi range should have type Type');
                return type2
              })
          });

        case 'app': return infer(ctx, term.value[0], index)
          .then(mbVPi => {
            if (mbVPi.ctor !== 'vpi') throw new Error('Illegal application');
            let [type, func] = mbVPi.value;
            return check(ctx, term.value[1], type, index)
              .then(() => func(evaluate(term.value[1], ctx)))
          });

        case 'freevar':
        result = ctx.lookup(term.value[0], 'sig');
        if (result) return result;
        else throw new Error(`Unknown identifier: ${term.value[0].value[0]}`);

        case 'tcon':
        if (term.value.length === 1) term.value.push([]);
        result = ctx.lookup(term.value[0], 'data');
        if (result.length !== term.value[1].length)
          throw new Error(`Data constructor given wrong number of arguments (${term.value[1].length} instead of ${result.length})`);
        return tcArgTele(ctx, term.value[1], result)
          .then(() => new Value({vstar: []}))

        case 'dcon':
        if (typeof term.value[2] !== 'undefined') return check(ctx, term, term.value[2], index);
        if (term.value.length === 1) term.value.push([]);
        let matches = ctx.lookup(term.value[0], 'ctor'), match = matches[0];
        if (matches.length !== 1) throw new Error('Ambiguous data constructor');
        if (match.tcon.length !== 0) throw new Error('Cannot infer data constructor parameters. Try adding an annotation.');
        if (term.value[1].length !== match.tcon.length) throw new Error(
          `Constructor should have ${match.tcon.length} arguments, but was given ${term.value[1].length}`);
        return tcArgTele(ctx, term.value[1], match.dcon)
          .then(res => new Value({dcon: [ term.value[0], res, new Value({tcon: [ match.tname ]}) ]}))

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
          ctx.cons(new Decl({sig: [ new Name({local: [index]}), type.value[0] ]}), true),
          subst(new Term({freevar: [ new Name({local: [index]}) ]}), term.value[0]),
          type.value[1](vfree(new Name({local: [index]}))), index + 1)

        case 'dcon':
        if (typeof term.value[2] !== 'undefined') if (!term.value[2].equal(type)) throw new Error('Type mismatch');
        if (term.value.length === 1) term.value.push([]);
        let match = ctx.lookup(term.value[0], 'ctor', type.value[0]);
        if (match.dcon.length !== term.value[1].length)
          throw new Error(`Data constructor given wrong number of arguments (${match.dcon.length} instead of ${term.value[1].length})`);
        let items = substTele(ctx, match.tcon, term.value[1], match.dcon);
        return tcArgTele(ctx, term.value[1], new Tele(...items))
          .then(eterms => new Term({dcon: [term.value[0], eterms, type]}))

        default: return infer(ctx, term, index)
          .then(res => {
            if (!quote(res).equal(quote(type))) throw new Error('Type mismatch');
            else return type
          })
      }
    })
  }

  function evaluate (term, ctx = context) {
    let mbVal;
    switch (term.ctor) {
      case 'star': return new Value({vstar: []});

      case 'ann': return evaluate(term.value[0], ctx);

      case 'pi': return new Value({vpi: [
        evaluate(term.value[0], ctx),
        x => evaluate(term.value[1],
          ctx.cons(new Decl({sig: [ new Name({global: ['']}), x ]}), false))
      ]});

      case 'lam': return new Value({vlam: [
        x => evaluate(term.value[0],
          ctx.cons(new Decl({sig: [ new Name({global: ['']}), x ]}), false))
      ]});

      case 'app': return vapply(evaluate(term.value[0], ctx), evaluate(term.value[1], ctx));

      case 'boundvar': return ctx['!!'](term.value[0]);

      case 'freevar':
      mbVal = ctx.lookup(term.value[0], 'def');
      if (mbVal) return mbVal;
      else return vfree(term.value[0])

      case 'tcon': return new Value({vneutral: [ new Neutral({ntcon: term.value}) ]});

      case 'dcon': return new Value({vneutral: [ new Neutral({ndcon: term.value}) ]});
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

      case 'freevar':
      case 'tcon':
      case 'dcon': return term2;
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
      case 'nfree':
      let name = neutral.value[0];
      if (name.ctor === 'quote') return new Term({boundvar: [index - name.value[0] - 1]});
      else return new Term({freevar: [name]});

      case 'ntcon': return new Term({tcon: neutral.value});

      case 'ndcon': return new Term({dcon: neutral.value});

      case 'napp': return new Term({app: [
        nquote(neutral.value[0], index),
        quote(neutral.value[1], index)
      ]})
    }
  }

  // API

  const context = new Context(),
        self = { Context, context, Data, Sig, Term, Name, Decl, Item, typecheck, evaluate, quote },
        { seqSync, seqAsync } = ((p, count) => ({
          seqSync: fn => count.synced() ? fn() : seqAsync(fn),
          seqAsync: fn => count.next(p = fn ? p.then(fn) : p)
        }))(Promise.resolve(), ((a, s) => ({synced: () => s === a, next: p => (s++, p.then(() => a++))}))(0, 0));
  Object.defineProperty(self, 'ready', { get () { return seqAsync().then(() => new Promise(r => setTimeout(r, 0))) } });
  return self

})();


// Test cases

var id = new R.Sig('id',
  new R.Term({pi:[
    new R.Term({star:[]}),
    new R.Term({pi:[
      new R.Term({boundvar:[0]}),
      new R.Term({boundvar:[1]})
    ]})
  ]})
).Def(
  new R.Term({lam:[
    new R.Term({lam:[
      new R.Term({boundvar:[0]})
    ]})
  ]})
);
// var id = new R.Sig('id:=(t,x=>x):(T:Type)->T->T')
// var id = new R.Sig('id:=(x=>x):[T:Type]->T->T')


var Void = new R.Data({ typeName: 'Void', valueOf: () => undefined });

var Unit = new R.Data({ typeName: 'Unit', valueOf: () => null }, [
  { ctorName: 'tt', toString: () => '()' }
]);

var Bool = new R.Data({ typeName: 'Bool' }, [
  { ctorName: 'T', toString: () => 'T', valueOf: () => true },
  { ctorName: 'F', toString: () => 'F', valueOf: () => false }
]);

var Nat = new R.Data({ typeName: 'Nat' }, [
  { ctorName: 'Z', toString: () => 'Z', valueOf: () => 0 },
  { ctorName: 'S', ctorSig: [
      new R.Item({term: [ new R.Term({tcon: [ new R.Name({global: ['Nat']}) ]}) ]})
    ],
    toString () { return 'S' + this.value[0].toString() },
    valueOf () { return this.value[0].valueOf() + 1 } }
]);
// var Nat = new R.Data({ typeName: 'Nat' }, [
//   { ctorName: 'Z', toString: () => 'Z', valueOf: () => 0 },
//   { ctorName: 'S', ctorSig: '(Nat)',
//     toString () { return 'S' + this.value[0].toString() },
//     valueOf () { return this.value[0].valueOf() + 1 } }
// ]);

var List = new R.Data({ typeName: 'List', typeSig: [
    new R.Item({term: [
      new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
      new R.Term({star: []})
    ]})
  ] }, [
  { ctorName: 'Nil', toString: () => '[]', valueOf: () => [] },
  { ctorName: 'Cons', ctorSig: [
      new R.Item({term: [ new R.Term({freevar: [ new R.Name({global: ['A']}) ]}) ]}),
      new R.Item({term: [ new R.Term({tcon: [
        new R.Name({global: ['List']}),
        [ new R.Term({freevar: [ new R.Name({global: ['A']}) ]}) ]
      ]}) ]})
    ],
    toString () { return this.value[1].toString() + ' : ' + this.value[0].toString() },
    valueOf () { return this.value[1].valueOf().concat([this.value[0].valueOf()]) } }
]);
// var List = new R.Data({ typeName: 'List', typeSig: '(A:Type)' }, [
//   { ctorName: 'Nil', toString: () => '[]', valueOf: () => [] },
//   { ctorName: 'Cons', ctorSig: '(A)(List A)',
//     toString () { return this.value[0].toString() + ' : ' + this.value[1].toString() },
//     valueOf () { return this.value[1].concat([this.value[0]]) } }
// ]);

let idU, tt, idtt, idB, idt, idf, zero, one, two, Nats, _21;
console.log(Unit().tt());
console.log(id.type && R.quote(id.type), id.state)
R.ready.then(async () => {
  console.log(Unit().tt())
  console.log(id.type && R.quote(id.type), id.state)
  idU = id(Unit());
  tt = id(Unit(), Unit().tt());
  console.log(idU.type && R.quote(idU.type), idU.state)
  await R.ready;

  console.log(idU.type && R.quote(idU.type), idU.state)
  console.log(tt.type && R.quote(tt.type), tt.state);
  idtt = idU(Unit().tt());
  await R.ready;

  console.log(idtt.type && R.quote(idtt.type), idtt.state);
  idB = id(Bool());
  idf = id(Bool(), Bool().f());
  Nat();
  await R.ready;

  idt = idB(Bool().t());
  // R.context.idB = id(Bool()) ??
  zero = Nat().z();
  one = Nat().s(zero);
  two = Nat().s(one);
  Nats = List(Nat());
  await R.ready;

  _21 = Nats.cons(one, Nats.cons(two, Nats.nil()));
  console.log(_21.toString(), _21.valueOf())
})

//
// // Pattern matching
// R.Sig('not')
//
// var Vec = new R.Data({ typeName: 'Vec', typeSig: [
//     new R.Item({term: [
//       new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
//       new R.Term({star: []})
//     ]}),
//     new R.Item({term: [
//       new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//       new R.Term({tcon: [ new R.Name({global: ['Nat']}) ]})
//     ]})
//   ] }, [
//   { ctorName: 'Nil', ctorSig: [
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({dcon: [ new R.Name({global: ['Z']}) ]})
//       ]})
//     ],
//     toString: () => '<>', valueOf: () => [] },
//   { ctorName: 'Cons', ctorSig: [
//       new R.Item({erased: [
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]}),
//         new R.Term({tcon: [ new R.Name({global: ['Nat']}) ]})
//       ]}),
//       new R.Item({term: [ new R.Term({freevar: [ new R.Name({global: ['A']}) ]}) ]}),
//       new R.Item({term: [ new R.Term({tcon: [
//         new R.Name({global: ['Vec']}),
//         [ new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
//           new R.Term({freevar: [ new R.Name({global: ['m']}) ]}) ]
//       ]}) ]}),
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({app: [ new R.Term({dcon: [
//           new R.Name({global: ['S']}),
//           [ new R.Term({freevar: [ new R.Name({global: ['m']}) ]}) ]
//         ]}) ]})
//       ]})
//     ],
//     toString () { return this.value[0].toString() + ' :: ' + this.value[1].toString() },
//     valueOf () { return this.value[1].concat([this.value[0]]) } }
// ]);
// // var Vec = new R.Data({ typeName: 'Vec', typeSig: '(A:Type)(n:Nat)' }, [
// //   { ctorName: 'Nil', ctorSig: '{n=Z}',
// //     toString: () => '<>', valueOf: () => [] },
// //   { ctorName: 'Cons', ctorSig: '{m:Nat}(A)(Vec A m){n=S m}',
// //     toString () { return this.value[0].toString() + ' :: ' + this.value[1].toString() },
// //     valueOf () { return this.value[1].concat([this.value[0]]) } }
// // ]);
//
// var Fin = new R.Data({ typeName: 'Fin', typeSig: [
//     new R.Item({term: [
//       new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//       new R.Term({tcon: [ new R.Name({global: ['Nat']}) ]})
//     ]})
//   ] }, [
//   { ctorName: 'Zero', ctorSig: [
//       new R.Item({erased: [
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]}),
//         new R.Term({tcon: [ new R.Name({global: ['Nat']}) ]})
//       ]}),
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({dcon: [
//           new R.Name({global: ['S']}),
//           [ new R.Term({freevar: [ new R.Name({global: ['m']}) ]}) ]
//         ]})
//       ]})
//     ],
//     toString () { return`Zero [${this.value[0].toString()}]` },
//     valueOf () { return this.value[0].valueOf() - 1 } },
//   { ctorName: 'Succ', ctorSig: [
//       new R.Item({erased: [
//         new R.Term({freevar: [ new R.Name({global: ['m']}) ]}),
//         new R.Term({tcon: [ new R.Name({global: ['Nat']}) ]})
//       ]}),
//       new R.Item({constraint: [
//         new R.Term({freevar: [ new R.Name({global: ['n']}) ]}),
//         new R.Term({dcon: [
//           new R.Name({global: ['S']}),
//           [ new R.Term({freevar: [ new R.Name({global: ['m']}) ]}) ]
//         ]})
//       ]}),
//       new R.Item({term: [ new R.Term({tcon: [
//         new R.Name({global: ['Fin']}),
//         [ new R.Term({freevar: [ new R.Name({global: ['m']}) ]}) ]
//       ]}) ]})
//     ],
//     toString () { return `Succ [${this.value[1].valueOf() - 1}] ` + this.value[1].toString() },
//     valueOf () { return this.value[1].valueOf() - 1 } }
// ])
// // var Fin = new R.Data({ typeName: 'Fin', typeSig: '(n:Nat)' }, [
// //   { ctorName: 'Zero', ctorSig: '{m:Nat}{n=S m}',
// //     toString () { return `Zero [${this.value[0].toString()}]` },
// //     valueOf () { return this.value[0].valueOf() - 1 } },
// //   { ctorName: 'Succ', ctorSig: '{m:Nat}{n=S m}(Fin m)',
// //     toString () { return `Succ [${this.value[1].valueOf() - 1}] ` + this.value[1].toString() },
// //     valueOf () { return this.value[1].valueOf() - 1 } }
// // ])
//
// var Sigma = new Data({ typeName: 'Σ', typeSig: [
//     new R.Item({term: [
//       new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
//       new R.Term({star: []})
//     ]}),
//     new R.Item({term: [
//       new R.Term({freevar: [ new R.Name({global: ['B']})]}),
//       new R.Term({pi: [
//         new R.Term({freevar: [ new R.Name({global: ['A']}) ]}),
//         new R.Term({star: []})
//       ]})
//     ]})
//   ] }, [
//   { ctorName: 'DProd', ctorSig: [
//       new R.Item({term: [
//         new R.Term({freevar: [ new R.Name({global: ['x']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['A']}) ]})
//       ]}),
//       new R.Item({term: [ new R.Term({app: [
//         new R.Term({freevar: [ new R.Name({global: ['B']}) ]}),
//         new R.Term({freevar: [ new R.Name({global: ['x']}) ]})
//       ]}) ]})
//     ],
//     toString () { return `Σ[${this.value[0].toString()}, ${this.value[1](this.value[0]).toString()}]` },
//     valueOf () { return [this.value[0].valueOf(), this.value[1](this.value[0]).valueOf()] } }
// ])
// // var Sigma = new Data({ typeName: 'Σ', typeSig: '(A:Type)(B:A->Type)' }, [
// //   { ctorName: 'DProd', ctorSig: '(x:A)(B x)',
// //     toString () { return `Σ[${this.value[0].toString()}, ${this.value[1](this.value[0]).toString()}]` },
// //     valueOf () { return [this.value[0].valueOf(), this.value[1](this.value[0]).valueOf()] } }
// // ])
