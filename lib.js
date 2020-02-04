var R = (() => {

  // Utilities

  const error = new Proxy({
            append (e1, which, ...args) { try { error[which](...args) } catch (e2) { throw new Error(e1.message + '\n' + e2.message) } }
          }, { get (o, prop) {
            if (prop in o) return o[prop];
            else return (...args) => { throw new Error((({
              duplicate: n => `Name '${n}' already exists`,
              nosig: n => `No signature has been declared for ${n}`,
              notfound: n => `Declaration for ${n} cannot be found`,
              unchecked: () => 'Type error: unchecked',

              lexer: (err, col, info) => `Lexer error: ${err}\nat ${col}\n${info}`,

              internal_ctor_args: () => 'Wrong number of constructor arguments',
              internal_ctor_invalid: (inv, ctors) => `${inv} not a valid constructor. Looking for: ${ctors.join(', ')}`,

              parser_mismatch: (token, index, id, match) => `Parser error: mismatch at '${token.id || ''}'${
                'value' in token ? `, '${token.value}'` : ''}, token #${index}${id ? `: expected '${id}'` : ''}${match ? `, '${match}'` : ''}`,
              parser_nesting: () => 'Parser error: parens nest level too deep',
              parser_notid: () => 'Parser error: not an identifier',
              parser_notvalid: which => `Parser error: not a valid ${which}`,

              tc_mismatch: (tested, given) => `Type error: mismatch at ${tested.toString()}, expecting ${given.toString()}`, // TODO: pretty print
              tc_ann_mismatch: tested => `Type error: annotation should have type Type, found ${tested.toString()}`,
              tc_pi_mismatch: (loc, tested) => `Type error: Pi ${loc} should have type Type, found ${tested.toString()}`,
              tc_app_mismatch: tested => `Type error: illegal application - expected type Pi, found ${tested.toString()}`,
              tc_unknown_id: name => `Type error: unknown identifier ${name.value[0]}`,
              tc_dcon_ambiguity: () => 'Type error: ambiguous data constructor',
              tc_dcon_cannot_infer: () => 'Type error: cannot infer data constructor parameters. Try adding an annotation.',
              tc_dcon_arg_len: (mlen, tlen) => `Type error: data constructor given wrong number of arguments - (${mlen} instead of ${tlen})`,
              tc_lam_mismatch: ctor => `Type error: lambda has Pi type, not ${ctor}`,
              tc_lam_infer: () => 'Type error: cannot infer type of lambda',
              tc_bad_app: () => 'Type error: bad value application',
              tc_erased_var_subst: () => 'Type error: erased variable used in lambda',
              tc_erasure_mismatch: () => 'Type error: erasure mismatch'
            })[prop] || (() => prop))(...args)) }
          } });
  let showDebug = false;
  function triggerProxyPromise () {
    let px = (obj, args) => new Proxy(new obj(...args), { get (p, prop) {
      if (prop === 'catch') return cb => p.catch(err => {
        console.log('catch', err);
        return cb(err)
      });
      else return cb => p[prop](res => cb(res))
    } });
    Promise = new Proxy(Promise, { get (obj, prop) {
      if (prop === 'resolve') return v => px(obj, [r => r(v)]);
      else if (prop === 'reject') return v => px(obj, [r => { throw v }]);
      else return obj[prop]
    }, construct (obj, args) { return px(obj, args) } })
  }

  let active = [],
      contextOld = [];
  function wait (declType, name) {
    if (~active.findIndex(([d, n]) => d === declType && n === name)) error.duplicate(declType, name);
    else active.push([declType, name])
  }
  function unwait (declType, name) {
    let i = active.findIndex(([d, n]) => d === declType && n === name);
    if (!~i) error.notfound(declType, name);
    else contextOld.push(active.splice(i, 1)[0])
  }
  function waiting (declType, name) {
    return !!~active.findIndex(([d, n]) => d === declType && n === name)
  }
  function inContext (declType, name) {
    return !!~contextOld.findIndex(([d, n]) => d === declType && n === name)
  }




  // Interpreter

  // Data(name, tcon, [dcons], {...builtins})
  // Data(name, tcon, [{dcons}], {...builtins})
  class Data {
    constructor (name, tcon, dcons, builtins) {
      wait('data', name);
      let ready = false, self = {},
          tconLex = tokenise({name, sourceString: tcon}),
          dconLexes = dcons.map(dcon => {
            if (typeof dcon === 'string') return tokenise({sourceString: dcon});
            else return tokenise({sourceString: Object.keys(dcon)[0]})
          });
      sequence(() => dconLexes.reduce((p, l) => p = p.then(acc => parse(l, 'con').then(res => (acc[0].value[2].push(res[0]), acc))), parse(tconLex, 'data'))
        .then(decls => typecheck(decls, context)).then(res => {
          ready = true;
          unwait('data', name)
        }));
      return (...args) => {
        if (ready) return Object.assign(self, {
          typeOf () {  },
          quote () {  }
        });
        else error.unchecked()
      }
    }
  }

  // Sig(name, signature)
  // Sig(name, sigdef)
  class Sig {
    constructor (name, declString) {
      wait('sig', name);
      let ready = false, jsTerm = {},
          lex = tokenise({name, sourceString: declString});
      sequence(() => parse(lex, 'sig').then(decls => typecheck(decls, context)).then(res => {
        let [{decl, term, type, value}] = res;
        if (decl === 'sig') Object.assign(jsTerm, {type: term, typeValue: value});
        ready = true;
        unwait('sig', name)
      }));
      return { Def: (...args) => jsTerm = new Def(name, ...args) }
    }
  }

  // Def(name, sigdef, {...builtins})
  class Def {
    constructor (name, declString, builtins) {
      wait('def', name);
      let ready = false, jsTerm = builtins,
          lex = tokenise({name, sourceString: declString});
      sequence(() => parse(lex, 'def').then(decls => typecheck(decls, context)).then(ress => {
        ress.forEach(res => {
          let {decl, term, type, value} = res,
              appliedTerms = [];
          if (decl === 'sig') Object.assign(jsTerm, {type: term, typeValue: value});
          if (decl === 'def') Object.assign(jsTerm, {term, value, typeValue: type, appliedTerms})
        })
        ready = true;
        unwait('def', name)
      }));
      return jsTerm = Object.assign((...args) => {
        if (ready) return jsTerm; // TODO: typecheck and return new term
        else error.unchecked()
      }, jsTerm)
    }
  }



  // Lexer

  function tokenise ({name, sourceString}) {
    let rx_token = /^((\s+)|([a-zA-Z][a-zA-Z0-9_]*[\']*)|([:!$%&*+./<=>\?@\\^|\-~\[\]]{1,5})|(0|-?[1-9][0-9]*)|([(){},"]))(.*)$/,
        rx_digits = /^([0-9]+)(.*)$/,
        rx_hexs = /^([0-9a-fA-F]+)(.*)$/,
        tokens = name ? [{id: name, value: 'name'}] : [], pos = 0, word, char;

    function make (t) { tokens.push(t) }

    function string () {
      word = '';
      return (function next () {
        if (char === '"') {
          snip();
          make({id: char, value: 'string'})
        }
        else if (char === '') error.lexer('Unclosed string', pos);
        else if (char === '\\') {
          nextchar('\\');
          if (char === '') error.lexer('Unclosed string', pos);
          else if (char === '"') nextchar()
        }
        else nextchar();
        return next()
      })()
    }
    function snip () { word = word.slice(0, -1) } // from end
    function nextchar (match) {
      if (match && match !== char) error.lexer(char ?
        `Unexpected char ${char}, looking for ${match}` :
        `Missing expected char ${match}`, pos - 1);
      if (sourceString) {
        word += (char = sourceString[0]);
        sourceString = sourceString.slice(1)
      }
      pos++;
      return char
    }
    function backchar () {
      if (word) {
        char = word.slice(-1);
        sourceString = char + sourceString;
        pos -= 1;
        snip();
      }
      else char = '';
      return char;
    }

    function num () {
      if (word === '0') {
        nextchar();
        if (char === '.') frack();
        else if (char === 'x') {
          somedigits(rx_hexs);
          nextchar()
        }
      } else {
        nextchar();
        frack()
      }
      if (/[0-9a-zA-Z]/.test(char)) error.lexer(`Unexpected character ${char} after number`, col - 1);
      backchar();
      return make({id: word, value: 'num'})
    }
    function frack () {
      if (char === ".") {
        somedigits(rx_digits);
        nextchar();
      }
      if (char === "E" || char === "e") {
        nextchar();
        if (char !== "+" && char !== "-") backchar();
        somedigits(rx_digits);
        nextchar();
      }
    }
    function somedigits (rx) {
      let result = sourceString.match(rx);
      if (result) {
        char = result[1];
        pos += char.length;
        sourceString = result[2];
        word += char
      } else return error.lexer('Expected digits', col)
    }

    return (function lex () {
      let result;
      if (!sourceString) {
        make({value: 'final'});
        return tokens;
      }
      result = sourceString.match(rx_token);
      if (!result) error.lexer('Unexpected character', pos, sourceString[0]);
      word = result[1];
      pos += word.length;
      sourceString = result[7];

      if (result[2]) return lex(); // whitespace
      else if (result[3]) make({id: word}); // regular word
      else if (result[4]) make({id: word, value: 'op'}); // operator
      else if (result[5]) num(); // number
      else if (result[6]) {
        if (word === '"') string(); // string literal
        else make({id: word, value: 'punc'}); // punctuation
      }
      return lex()
    })()
  }




  // Syntax

  function AST (...ctors) {
    return class {
      constructor (arg) {
        let kv = Object.entries(arg);
        if (kv.length !== 1) error.internal_ctor_args();
        if (!~ctors.indexOf(kv[0][0])) error.internal_ctor_invalid(kv[0][0], ctors);
        [this.ctor, this.value] = kv[0]
      }
    }
  }

  class Term extends AST('ann', 'star', 'pi', 'lam', 'app', 'boundvar', 'freevar' ,'tcon', 'dcon') {
    equal (operand) {
      return this.ctor === operand.ctor && this.value.every((x, i) => x === operand.value[i] || x.equal(operand.value[i]))
    }
    toString () {
      switch (this.ctor) {
        case 'ann': return `(${this.value[0].toString()} : ${this.value[1].toString()})`;
        case 'star': return 'Type';
        case 'pi': return `${this.value[2] ? 'Erased' : ''}Pi(${this.value[0].toString()}, ${this.value[1].toString()})`;
        case 'lam': return `${this.value[1] ? 'Erased' : ''}Lam(${this.value[0].toString()})`;
        case 'app': return `${this.value[0].toString()} :@: ${this.value[1].toString()}`;
        case 'boundvar': return `Bound ${this.value[0]}`;
        case 'freevar': return `Free ${this.value[0]}`;

        case 'tcon': return `[TC:${this.value[0].value[0]} ${this.value[1].toString()}]`;
        case 'dcon': return `DC:${this.value[0].value[0]} (${this.value[1].toString()})`;
      }
    }
  }

  class Name extends AST('global', 'local', 'quote') {
    equal (operand) {
      return this.ctor === operand.ctor && this.value[0] === operand.value[0]
    }
    toString () {
      switch(this.ctor) {
        case 'global': return `Global <${this.value[0]}>`
        case 'local': return `Local ${this.value[0]}`
      } }
  }

  class Item extends AST('term', 'erased', 'constraint') {
    equal (operand) { return this.ctor === operand.ctor && this.value.every((x, i) => x.equal(operand.value[i]))}
    toString () {
      switch(this.ctor) {
        case 'term': return `(${this.value.map(x => x.toString()).join(':')})`
        case 'erased': return `{${this.value.map(x => x.toString()).join(':')}}`
        case 'constraint': return `{${this.value.map(x => x.toString()).join('=')}}`
      }
    }
  }
  class Tele { // TODO: meaningfully distinguish params/indices
    items = []
    length = 0
    constructor (...items) {
      for (let item of items) {
        if (item.ctor === 'term') this.length++;
        this.items.push(item)
      }
    }
    term (...args) {
      this.items.push(new Item({term: args}));
      this.length++;
      return this
    }
    erased (...args) {
      this.items.push(new Item({erased: args}));
      return this
    }
    constraint (...args) {
      this.items.push(new Item({constraint: args}));
      return this
    }
    equal (operand) { return this.items.every((x, i) => x.equal(operand.items[i])) }
    toString () { return this.items.map(x => x.toString()).join(' ')  }
  }

  class Decl extends AST('sig', 'def', 'recdef', 'data', 'datasig') {
    toString () {
      switch (this.ctor) {
        case 'sig': return `SIG: ${this.value[0].toString()} : ${this.value[1].toString()}`
        case 'def': return `DEF: ${this.value[0].toString()} := ${this.value[1].toString()}`
        case 'data': return `DATA: ${this.value[0].toString()} ${this.value[1].toString()}` + this.value[2].map(ctor => `\n  ${ctor.toString()}`)
      }
    }
  }
  class Ctor extends AST('ctor') {
    toString () { return `CTOR: ${this.value[0].toString()} : ${this.value[1].toString()}` }
  }

  class Value extends AST('vlam', 'vstar', 'vpi', 'vneutral') {}
  class Neutral extends AST('nfree', 'ntcon', 'ndcon', 'napp') {}




  // Parser

  let { parse } = new (class Parser {
    env = []
    parse (tokens, sourceName) {
      // TODO: mixfix operators

      function debug (msg, res) {
        if (!showDebug) return;
        switch (msg) {
          case 'enclosure_open': console.group('Try enclosure'); break;
          case 'group_end': console.groupEnd(); break;

          case 'End statement?': console.log(`%c${msg}`, 'font-weight: bold', token, index); break;
          case 'Signature?': console.log(`%c${msg}`, 'font-weight: bold; color: goldenrod', token, index); break;
          case 'Definition?': console.log(`%c${msg}`, 'font-weight: bold; color: rebeccapurple', token, index); break;
          case 'Signature with definition?': console.log(`%c${msg}`, 'font-weight: bold; color: turquoise', token, index); break;
          case 'Type/record definition?': console.log(`%c${msg}`, 'font-weight: bold; color: forestgreen', token, index); break;
          case 'Constructor definition?': console.log(`%c${msg}`, 'font-weight: bold; color: dodgerblue', token, index); break;
          case 'Pattern?': console.log(`%c${msg}`, 'font-weight: bold; color: firebrick', token, index); break;
          case 'Let/where/case?': console.log(`%c${msg}`, 'font-weight: bold; color: deeppink', token, index); break;
          case 'Expression:': console.log(msg, res.map(v => v.toString())); break;

          default: console.log(msg, tokens[index], index)
        }
      }

      function next () { return tokens[index++] }
      function advance (msg, match) {
        msg && debug(msg);
        if (match && (('id' in match && tokens[index].id !== match.id) || ('value' in match && tokens[index].value !== match.value)))
        error.parser_mismatch(token, index, match.id, match.value);
        token = next();
      }
      function assertId () { if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index) }

      function alt (fn) {
        let rewind = index;
        return new Promise(r => r(fn())).catch(err => {
          index = rewind;
          throw err
        })
      }
      function debugGroup (msg, fn) {
        return alt(() => {
          console.group(msg);
          return fn().then(result => {
            console.groupEnd();
            return result
          }).catch(err => {
            console.groupEnd();
            throw err
          })
        })
      }
      function altMsg (msg, fn) { return (showDebug ? dfn => debugGroup(msg, dfn) : alt)(fn) }

      function parseStatement (env, all) {
        function endTest (decls) {
          return alt(() => {
            advance('End statement?', {value: 'final'});
            return all.concat(decls)
          })
        }
        return endTest([]).catch(() => {
          switch (sourceName) {
            case 'sig': return alt(() => {
              // term
              advance('Signature?', {value: 'name'});
              let name = token;
              return inferrableTerm([], 'pi')
                .then(result => endTest([new Decl({sig: [ new Name({global: [name.id]}), result ]})]))
                .catch(() => error.parser_notvalid('signature'))
            })

            case 'def': return alt(() => {
              // term : type
              advance('Signature with definition?', {value: 'name'});
              let name = token;
              return inferrableTerm([], 'ann')
                .then(result => {
                  if (result.ctor !== 'ann') throw 'skip';
                  return endTest([ new Decl({sig: [ new Name({global: [name.id]}), result.value[1] ]}),
                    new Decl({def: [ new Name({global: [name.id]}), result.value[0] ]})])
                })
            }).catch(() => alt(() => {
              // term
              advance('Definition?', {value: 'name'})
              let name = token;
              return inferrableTerm([], 'pi')
                .then(result => endTest([new Decl({def: [ new Name({global: [name.id]}), result ]})]))
            })).catch(() => error.parser_notvalid('definition'))

            case 'data': return alt(() => {
              // name bindings : type
              // For now, only allow tcon indexes of type Type, until I can
              // compare Idris or Agda with the constraint solver in pi-forall
              // for how to implement dependent type families
              advance('Type/record definition?', {value: 'name'});
              let name = token;
              return inferrableTerm([], 'data')
                .then(result => endTest([new Decl({data: [ new Name({global: [name.id]}), result, [] ] })]))
                .catch(() => error.parser_notvalid('type definition'))
            })

            case 'con': return alt(() => {
              // name : bindings type (?)
              advance('Constructor definition?');
              assertId();
              let name = token;
              advance('Type constructor separator?', {value: 'op', id: ':'});
              return inferrableTerm([], 'con')
                .then(result => endTest([new Ctor({ctor: [ new Name({global: [name.id]}), result ]})]))
                .catch(() => error.parser_notvalid('constructor definition'))
            })

            case 'pat': return alt(() => {
              // @ terms := term
              advance('Pattern?');
              return Promise.reject()
                .catch(() => error.parser_notvalid('pattern'))
            })

            case 'let': return alt(() => {
              // name := term
              advance('Let/where/case?');
              return Promise.reject()
                .catch(() => error.parser_notvalid('let construct'))
            })
          }
        })
      }

      function enclosure (glyphs, fn) {
        if (level > 20) error.parser_nesting();
        let gly;
        return glyphs.reduce((p, glyph) => p = p.catch(() => alt(() => {
          let [open, close] = ({ parens: ['(', ')'], braces: ['{', '}'] })[gly = glyph]
          advance(`Open ${gly}?`, {value: 'punc', id: open});
          debug('enclosure_open');
          level++;
          return fn().then(result => {
            advance(`Close ${gly}?`, {value: 'punc', id: close});
            debug('group_end');
            level--;
            return result
          }).catch(err => {
            debug('group_end');
            level--;
            throw err
          })
        })), Promise.reject()).then(result => glyphs.length > 1 ? [result, gly] : result)
      }

      function telescope (env, isPi) { // returns { boundvars, types, epsilons }
        function boundvars () {
          // '{a} b c'
          advance('Binding variable?');
          assertId();
          let bvs = [[token, false]]
          return (function loop () { return alt(() => {
            advance('Binding next variable?');
            if (!('id' in token) || 'value' in token) error.parser_notid();
            bvs.unshift([token, false]);
            return loop(bvs)
          }).catch(() => {
            // vars : ...
            advance('Binding operator?', {value: 'op', id: ':'});
            return bvs
          }) })()
        }
        return altMsg('Try bindings', () => {
          let tele = {bvs: [], tys: [], eps: []};
          return (function loop (e, t, ep) {
            // (vars : term) *or* {vars : term}
            return enclosure(['parens', 'braces'], () => boundvars().then(bvs => checkableTerm(isPi ? e : [], 'bind').then(type => [bvs, type])))
              .then(([[bvs, type], gly]) => {
                tele = {
                  bvs: bvs.map(x => x[0]).concat(e),
                  tys: bvs.map(() => type).concat(t),
                  eps: bvs.map(x => ({ parens: false, braces: true })[gly] || x[1]).concat(ep)
                };
                return alt(() => loop(tele.bvs, tele.tys, tele.eps))
              }) // {bnd1} (bnd2)...
              .catch(() => ({boundvars: tele.bvs, types: tele.tys, epsilons: tele.eps}))
          })(env, [], [])
            .catch(() => boundvars().then(bvs =>
              // vars : term
              checkableTerm(env, 'bind').then(tm =>
                ({boundvars: bvs.map(x => x[0]), types: boundvars.map(() => tm), epsilons: bvs.map(x => x[1])})
              )
            ))
        })
      }

      function checkableTerm (env, clause) { // TODO: merge with inferrableTerm
        switch (clause) {
          // lam *or* pi
          case 'bind': return altMsg('Try checkable term', () => lambda(env))
            .catch(() => inferrableTerm(env, 'pi'))

          // (lam) *or* term
          default: return altMsg('Try checkable term', () => enclosure(['parens'], () => lambda(env)))
            .catch(() => inferrableTerm(env, clause))
        }
      }

      function inferrableTerm (env, clause) {
        function arrow (env, term) {
          advance('Function arrow?', {value: 'op', id: '->'});
          return inferrableTerm([''].concat(env), 'pi')
            .then(piBound => new Term({pi: [ term, piBound, false ]}))
        }
        function annot (term) {
          return alt(() => {
            advance('Annotated term?', {value: 'op', id: ':'});
            return checkableTerm(env, 'bind')
              .then(ty => new Term({ann: [term, ty]}))
          }).catch(() => term)
        }

        let data = false;
        switch (clause) {
          case 'data': data = true;
          case 'con': return altMsg(`Try ${data ? 'Type' : 'Constructor'} Definition`, () =>
            alt(() => telescope(env, true).then(tele => {
              data ?
                // {bnd} (bnd)... : term -> term...
                advance('Typedef separator?', {value: 'op', id: ':'}) :
                  // {bnd} (bnd)... -> term -> term...
                advance('Condef arrow? (leftmost)', {value: 'op', id: '->'});
              return tele
            })).catch(() => ({boundvars: [], types: [], epsilons: []}))
              .then(({boundvars, types, epsilons}) => inferrableTerm(boundvars.concat(env), 'pi').then(typeFam =>
                types.reduce((acc, ty, i) => acc = acc[epsilons[i] ? 'erased' : 'term'](new Name({global: [boundvars[i].id]}), ty), new Tele()).term(typeFam)
              ))
          )

          // {bnd} (bnd)...
          case 'pi': return altMsg('Try Pi', () =>
            telescope(env, true).then(({boundvars, types, epsilons}) => {
              // {bnd} (bnd)... -> term -> term...
              advance('Function arrow? (leftmost)', {value: 'op', id: '->'});
              return checkableTerm(boundvars.concat(env), 'bind').then(piBound =>
                types.reduce((acc, ty, i) => acc = new Term({pi: [ty, acc, epsilons[i]]}), piBound)
              )
            })
          ) // lam
            .catch(() => alt(() => lambda(env)))
            // (ann)->...
            .catch(() => alt(() => inferrableTerm(env, 'ann').then(tm =>
              alt(() => arrow(env, tm)).catch(() => tm))
            ))

          // f a b... : term
          case 'ann': return altMsg('Try Annotation', () => inferrableTerm(env, 'app').then(annot))
            // (lam) : term
            .catch(() => enclosure(['parens'], () => lambda(env)).then(annot))

          // f a b...
          case 'app': return inferrableTerm(env, 'var').then(tm => altMsg('Try apply', () => {
            let ts = [];
            debug('Application?');
            // TODO: erased application f {a} b...
            return (function loop () { return checkableTerm(env, 'var').then(cterm => {
              ts.push(cterm);
              return loop()
            }) })().catch(() => ts.reduce((acc, term) => a = new Term({app: [acc, term, false]}), tm))
          }).catch(() => tm))

          // Type
          case 'var': return alt(() => {
            advance('Star?', {id: 'Type'});
            return new Term({star: []})
          }) // a *or* [x=>][(x:X)->] x
            .catch(() => alt(() => {
              advance('Variable term?');
              assertId();
              let i = env.findIndex(bv => bv.id === token.id);
              return ~i ? new Term({boundvar: [i]}) : new Term({freevar: [ new Name({global: [token.id]}) ]})
            })) // (pi)
            .catch(() => enclosure(['parens'], () => inferrableTerm(env, 'pi')))
        }
      }

      function lambda (env) {
        let bvs = [], eps = [],
            nextVar = ep => () => {
              advance(`Lambda next variable${ep ? ' (erased)' : ''}?`);
              if (!('id' in token) || 'value' in token) throw new Error('');
              return Promise.resolve({bv: token, ep})
            },
            loop = (bv, ep) => alt(() => {
              bvs.unshift(bv);
              eps.unshift(ep);
              advance('Lambda comma?', {value: 'punc', id: ','});
              // x, {y}, ...
              return enclosure(['braces'], nextVar(true))
              // x, y, ...
                .catch(() => alt(nextVar(false)))
                .then(({bv, ep}) => loop(bv, ep))
            }).catch(err => { if (!err.message) error.parser_mismatch(token, index) });
        // {x} ...
        return altMsg('Try Lambda', () => enclosure(['braces'], nextVar(true)))
        // x ...
          .catch(() => alt(nextVar(false)))
          .then(({bv, ep}) => loop(bv, ep))
          .then(() => {
            advance('Lambda arrow?', {value: 'op', id: '=>'});
            // x, y, .. => term
            return checkableTerm(bvs.concat(env), 'bind')
              .then(tm => bvs.reduce((a, _, i) => a = new Term({lam: [a, eps[i]]}), tm))
          })
      }

      let token = tokens[0], index = 0, level = 0;
      return parseStatement([], [])
        .then(result => (debug('Expression:', result), result))
    }
  });




  // Typechecking

  class Context {
    decls = []
    fresh = (i => () => i++)(0)
    constructor (obj) { if (obj) this.decls = obj.decls.slice() }
    lookup (name, ctor, annot) {
      if (ctor === 'ctor') {
        let mbCon;
        if (typeof annot === 'undefined') return this.decls.reduce((a, decl) => {
          if (decl.ctor === 'data' && (mbCon = decl.value[2].find(con => con.value[0].equal(name))))
            a.push({tname: decl.value[0], tdef: decl.value[1], con: mbCon.value[1]});
          return a
        }, []);
        else {
          let mbDef = this.decls.find(decl => decl.ctor === 'data' && decl.value[0].equal(annot.value[0]) &&
            (mbCon = decl.value[2].find(con => con.value[0].equal(name))));
          return { tdef: mbDef.value[1], con: mbCon.value[1] }
        }
      }
      let result = this.decls.find(decl => (decl.ctor === ctor || (ctor === 'data' && decl.ctor === 'datasig')) && decl.value[0].equal(name));
      if (result) return result.value[1]
    }
    cons (decl) { return this.push(decl, true) }
    extend (decl) { return this.push(decl, false) }
    push (decl, n) {
      let ret = n ? new Context(this) : this;
      ret.decls.push(decl);
      return ret
    }
    localVal (i) { return this.decls[this.decls.length - i - 1].value[1] }
  }
  const context = new Context();

  function typecheck (decls) {
    function infer (ctx, term, index = 0) { //context, term, number -> value
      return Promise.resolve().then(() => {
        let result, vstar = new Value({vstar: []}), local = new Name({local: [index]});
        switch (term.ctor) {
          case 'star': return vstar

          case 'ann': return check(ctx, term.value[1], vstar, index)
            .catch(e => error.append(e.message, 'tc_ann_mismatch', '?'))
            .then(() => check(ctx, term.value[0], evaluate(term.value[1], ctx), index))

          case 'pi': return infer(ctx, term.value[0], index)
            .then(type1 => {
              if (type1.ctor !== 'vstar') error.tc_pi_mismatch('domain', quote(type1));
              return infer(
                ctx.cons(new Decl({sig: [ local, evaluate(term.value[0], ctx) ]})),
                subst(new Term({freevar: [ local ]}), term.value[1], false), index + 1)
                .then(type2 => {
                  if (type2.ctor !== 'vstar') error.tc_pi_mismatch('range', quote(type2));
                  return vstar
                })
            })

          case 'app': return infer(ctx, term.value[0], index)
            .then(type => {
              if (type.ctor !== 'vpi') error.tc_app_mismatch(quote(type));
              let [dom, func] = type.value, lam = value;
              return check(ctx, term.value[1], dom, index)
                .then(() => func(evaluate(term.value[1], ctx)))
            })

          case 'freevar':
          if (result = ctx.lookup(term.value[0], 'sig')) return result
          error.tc_unknown_id(term.value[0])

          case 'tcon':
          if (term.value.length === 1) term.value.push([]) //?
          result = ctx.lookup(term.value[0], 'data');
          if (result.length !== term.value[1].length) error.tc_dcon_arg_len(term.value[1].length, result.length);
          return tcArgTele(ctx, term.value[1], result).then(() => vstar)

          case 'dcon':
          if (typeof term.value[2] !== 'undefined') return check(ctx, term, term.value[2], index);
          if (term.value.length === 1) term.value.push([]) //?
          let matches = ctx.lookup(term.value[0], 'ctor');
          if (matches.length !== 1) error.tc_dcon_ambiguity();
          let match = matches[0];
          if (match.tdef.length !== 0) error.tc_dcon_cannot_infer();
          if (term.value[1].length !== match.con.length) error.tc_dcon_arg_len(match.con.length, term.value[1].length);
          return tcArgTele(ctx, term.value[1], match.con).then(() => evaluate(new Term({tcon: [ match.tname ]}), ctx))

          case 'lam': error.tc_lam_infer()
        }
      })
    }

    function check (ctx, term, typeVal, index = 0) { //context, term, term, number -> term:term, type:value
      return Promise.resolve().then(() => {
        switch (term.ctor) {
          case 'lam':
          if (typeVal.ctor !== 'vpi') error.tc_lam_mismatch(typeVal.ctor);
          if (term.value[1] !== typeVal.value[2]) error.tc_erasure_mismatch();
          else {
            let local = new Name({local: [index]});
            return check(
              ctx.cons(new Decl({sig: [ local, typeVal.value[0] ]})),
              subst(new Term({freevar: [ local ]}), ...term.value),
              typeVal.value[1](vfree(local)), index + 1)
              .then(() => ({term, type: typeVal}))
          }

          case 'dcon':
          let type = quote(typeVal);
          if (typeof term.value[2] !== 'undefined' && !term.value[2].equal(type)) error.tc_mismatch(term.value[2], type);
          if (term.value.length === 1) term.value.push([]) //?
          let match = ctx.lookup(term.value[0], 'ctor', type.value[0]);
          if (match.con.length !== term.value[1].length) error.tc_dcon_arg_len(match.con.length, term.value[1].length);
          let items = substTele(ctx, match.tdef, term.value[1], match.con);
          return tcArgTele(ctx, term.value[1], new Tele(...items))
            .then(eterms => ({ term: new Term({dcon: [ term.value[0], eterms, typeVal ]}), type: typeVal }))

          default: return infer(ctx, term, index)
            .then(type => {
              let res = quote(type), ty = quote(typeVal);
              if (!res.equal(ty)) error.tc_mismatch(res, ty);
              else return {term, type: typeVal}
            })
        }
      })
    }

    function evaluate (term, ctx) {
      let mbVal, local = x => new Decl({sig: [ new Name({global: ['']}), x ]});
      switch (term.ctor) {
        case 'star': return new Value({vstar: []})
        case 'ann': return evaluate(term.value[0], ctx)
        case 'pi': return new Value({vpi: [ evaluate(term.value[0], ctx), x => evaluate(term.value[1], ctx.cons(local(x))), term.value[2] ]})
        case 'lam': return new Value({vlam: [ x => evaluate(term.value[0], ctx.cons(local(x))), term.value[1] ]})
        case 'app': return vapply(evaluate(term.value[0], ctx), evaluate(term.value[1], ctx), term.value[2])
        case 'boundvar': return ctx.localVal(term.value[0])
        case 'freevar': return (mbVal = ctx.lookup(term.value[0], 'def')) ? mbVal : vfree(term.value[0])
        case 'tcon': return new Value({vneutral: [ new Neutral({ntcon: term.value}) ]})
        case 'dcon': return new Value({vneutral: [ new Neutral({ndcon: term.value}) ]})
      }
    }

    function subst (term1, term2, ep, index = 0) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ subst(term1, term2.value[0], ep, index), subst(term1, term2.value[1], ep, index), term2.value[2] ]})
        case 'pi': return new Term({pi: [ subst(term1, term2.value[0], ep, index), subst(term1, term2.value[1], ep, index + 1), term2.value[2] ]})
        case 'lam': return new Term({lam: [ subst(term1, term2.value[0], ep, index + 1), term2.value[1] ]})
        case 'app': return new Term({app: [ subst(term1, term2.value[0], ep, index), subst(term1, term2.value[1], ep, index) ]})
        case 'boundvar': return index !== term2.value[0] ? term2 : !ep ? term1 : error.tc_erased_var_subst()
        case 'star': case 'freevar': case 'tcon': case 'dcon': return term2
      }
    }

    // TODO: combine Value and Neutral?
    function vfree (name) { return new Value({vneutral: [ new Neutral({nfree: [name]}) ]}) } // TODO: accept tcon and dcon?
    function vapply (value1, value2, epsilon) {
      switch (value1.ctor) {
        case 'vlam': return value1.value[0](value2)
        case 'vneutral': return new Value({vneutral: [ new Neutral({napp: [ value1.value[0], value2, epsilon ]}) ]})
        default: error.tc_bad_app()
      }
    }

    function quote (value, index = 0) {
      let qname = new Name({quote: [index]});
      switch (value.ctor) {
        case 'vstar': return new Term({star: []})
        case 'vpi': return new Term({pi: [ quote(value.value[0], index), quote(value.value[1](vfree(qname)), index + 1), value.value[2]]})
        case 'vlam': return new Term({lam: [ quote(value.value[0](vfree(qname)), index + 1), value.value[1] ]})
        case 'vneutral': return nquote(value.value[0], index)
      }
    }
    function nquote (neutral, index) {
      let name;
      switch (neutral.ctor) {
        case 'nfree': return (name = neutral.value[0]).ctor === 'quote' ?
          new Term({boundvar: [index - name.value[0] - 1]}) :
          new Term({freevar: [name]})
        case 'ntcon': return new Term({tcon: neutral.value})
        case 'ndcon': return new Term({dcon: neutral.value})
        case 'napp': return new Term({app: [ nquote(neutral.value[0], index), quote(neutral.value[1], index), neutral.value[2] ]})
      }
    }

    return decls.reduce((p, decl) => p = p.then(acc => {
      let [name, info, ctors] = decl.value, mbValue, value;
      switch (decl.ctor) {
        case 'sig':
        let typeVal = new Value({vstar: []});
        mbValue = context.lookup(name, 'sig');
        if (typeof mbValue !== 'undefined') {
          if (info.equal(quote(mbValue))) return acc.concat([{decl: 'sig', type: typeVal, value: mbValue, term: info}]);
          else error.duplicate(name);
        } else return check(context, info, typeVal).then(({term, type}) => {
          let value = evaluate(info, context);
          context.extend(new Decl({sig: [ name, value ]}));
          return acc.concat([{decl: 'sig', type, value, term: info}])
        })

        case 'def':
        mbValue = context.lookup(name, 'def');
        if (typeof mbVal !== 'undefined') {
          if (info.equal(quote(mbValue))) return acc.concat([{decl: 'def', type: context.lookup(name, 'sig'), value: mbValue, term: info}]);
          else error.duplicate(name)
        } else {
          let mbType = context.lookup(name, 'sig');
          return (typeof mbType === 'undefined') ?
            infer(context, info).then(type => {
              value = evaluate(info, context);
              context.extend(new Decl(({sig: [name, type]}))).extend(new Decl({def: [name, value]}));
              return acc.concat([{decl: 'def', type, value, term: info}])
            }) :
            check(context, info, mbType).then(({term, type} )=> {
              value = evaluate(info, context);
              context.extend(new Decl({def: [name, value]}));
              return acc.concat([{decl: 'def', type, value, term: info}])
            })
        }

        case 'data': console.log(decl.toString())
      }
    }), Promise.resolve([]))
  }




  // API

  const R = { Data, Sig, Def, context },
        sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  Object.defineProperty(R, 'ready', { get () { return sequence(() => new Promise(r => setTimeout(r, 0))) } });

  return R
})();




// Testing

let id1, id2, Unit, Nat_;
(async () => {
  let passFail = obj => {
    for (let test in obj) try { console.log(obj[test]()) }
      catch (e) { console.log(test, e) }
  }

  // functions, lambdas
  id1 = new R
    .Sig('id', '(T : Type) -> T -> T')
    .Def('(t, x => x)');

  // functions with builtins
  id2 = new R.Def("id'", '({t}, x => x) : {T : Type} -> T -> T',
    { toString () { return this[0].toString() },
    valueOf () { return this[0].valueOf() } }
  );
  await R.ready;
  console.log(id1, id2)

  //
  // // types
  // Unit = new R.Data(
  //   'Unit', 'Type', ['TT : Unit'],
  //   { fromJS: () => Unit().tt() }
  // );
  // Nat_ = new R.Data(
  //   "Nat'", 'Type',
  //   [ 'Z : Nat',
  //     'S : (n:Nat) -> Nat' ]
  // )
  await R.ready;
})()
