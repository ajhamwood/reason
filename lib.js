var R = (() => {

  // Utilities

  const error = {
        duplicate: n => { throw new Error(`Name '${n}' already exists`) },
        nosig: n => { throw new Error(`No signature has been declared for ${n}`) },
        notfound: n => { throw new Error(`Declaration for ${n} cannot be found`) },
        unchecked: () => { throw new Error('Type error: unchecked') },
        lexer: (err, col, info) => { throw new Error(`Lexer error: ${err}\nat ${col}\n${info}`) },
        internal_ctor_args: () => { throw new Error('Wrong number of constructor arguments') },
        internal_ctor_invalid: (inv, ctors) => { throw new Error(`${inv} not a valid constructor. Looking for: ${ctors.join(', ')}`); },
        parser:  () => { throw new Error('Parser error') },
        parser_mismatch: (token, index, id, match) => {
          throw new Error(`Parser error: mismatch at '${token.id || ''}'${'value' in token ? `, '${token.value}'` : ''}, token #${index}${
            id ? `: expected '${id}'` : ''}${match ? `, '${match}'` : ''}`) },
        parser_nesting: () => { throw new Error('Parser error: parens nest level too deep') },
        parser_notid: () => { throw new Error('Parser error: not an identifier') }
      }, showDebug = false, detailedDebug = false;

  let active = [],
      context = [];
  function wait (declType, name) {
    if (~active.findIndex(([d, n]) => d === declType && n === name)) error.duplicate(declType, name);
    else active.push([declType, name])
  }
  function unwait (declType, name) {
    let i = active.findIndex(([d, n]) => d === declType && n === name);
    if (!~i) error.notfound(declType, name);
    else context.push(active.splice(i, 1)[0])
  }
  function waiting (declType, name) {
    return !!~active.findIndex(([d, n]) => d === declType && n === name)
  }
  function inContext (declType, name) {
    return !!~context.findIndex(([d, n]) => d === declType && n === name)
  }

  // Interpreter

  // Data(name, tcon, [dcons], {...builtins})
  // Data(name, tcon, [{dcons}], {...builtins})
  class Data {
    constructor (name, tcon, dcons, builtins) {
      wait('data', name);
      let ready = false, self = {},
          tconLex = tokenise({sourceString: tcon}),
          dconLexes = dcons.map(dcon => {
            if (typeof dcon === 'string') return tokenise({sourceString: dcon});
            else return tokenise({sourceString: Object.keys(dcon)[0]})
          });
      sequence(() => dconLexes.reduce((p, l) => p = p.then(acc => parse(l, 'dcon').then(res => acc.concat(res))), parse(tconLex, 'tcon'))
        .then(typecheck).then(decl => {
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
      let ready = false, self = {},
          lex = tokenise({name, sourceString: declString});
      sequence(() => parse(lex, 'sig').then(typecheck).then(decl => {
        ready = true;
        unwait('sig', name)
      }));
      return { Def: (...args) => new Def(name, ...args) }
    }
  }

  // Def(name, sigdef, {...builtins})
  class Def {
    constructor (name, declString, builtins) {
      wait('def', name);
      let ready = false, self = {},
          lex = tokenise({name, sourceString: declString});
      sequence(() => parse(lex, 'def').then(typecheck).then(decl => {
        ready = true;
        unwait('def', name)
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
      return this.ctor === operand.ctor &&
        this.value.every((x, i) => x === operand.value[i] ||
          ('equal' in x && x.equal(operand.value[i])) ||
          x.every((y, j) => y === operand.value[i][j]))
    }
    toString () {
      switch (this.ctor) {
        case 'ann': return `(${this.value[0].toString()} : ${this.value[1].toString()})`;
        case 'star': return 'Type';
        case 'pi': return `${this.value[2] ? 'Erased' : ''}Pi(${this.value[0].toString()}, ${this.value[1].toString()})`;
        case 'lam': return `Lam(${this.value[0].toString()})`;
        case 'app': return `${this.value[0].toString()} :@: ${this.value[1].toString()}`;
        case 'boundvar': return `Bound ${this.value[0]}`;
        case 'freevar': return `Free ${this.value[0]}`;

        case 'tcon': return `<TC:${this.value[0].value[0]} ${this.value.slice(1).map(x => `${x.toString()}`).join(' ')}>`;
        case 'dcon': return `DC:${this.value[0].value[0]} ${this.value.slice(1).map(x => `(${x.toString()})`).join(' ')}`;
      }
    }
  }

  class Name extends AST('global', 'local', 'quote') {
    equal (operand) {
      return this.ctor === operand.ctor && this.value[0] === operand.value[0]
    }
  }

  // Parser

  function parse (tokens, sourceName) {
    if (detailedDebug) Promise = new Proxy(Promise, { construct (obj, args) {
      return new Proxy(new obj(...args), { get (p, prop) {
        if (prop == 'catch') return cb => p.catch(err => {
          console.log(err);
          return cb(err)
        });
        else return p[prop]
      } })
    } });

    function debug (msg, res) {
      if (!showDebug) return;
      switch (msg) {
        case 'enclosure_open': console.group('Try enclosure'); break;
        case 'group_end': console.groupEnd(); break;

        case 'End statement?': console.log(`%c${msg}`, 'font-weight: bold', token, index); break;
        case 'Signature?': console.log(`%c${msg}`, 'font-weight: bold; color: goldenrod', token, index); break;
        case 'Definition?': console.log(`%c${msg}`, 'font-weight: bold; color: rebeccapurple', token, index); break;
        case 'Sigdef?': console.log(`%c${msg}`, 'font-weight: bold; color: turquoise', token, index); break;
        case 'Type/record constructor?': console.log(`%c${msg}`, 'font-weight: bold; color: forestgreen', token, index); break;
        case 'Data constructor?': console.log(`%c${msg}`, 'font-weight: bold; color: dodgerblue', token, index); break;
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

    function parseStatement (env, result) {
      function endTest (decls) {
        return alt(() => {
          advance('End statement?', {value: 'final'});
          return result.concat(decls)
        })
      }
      return endTest([]).catch(() => {
        switch (sourceName) {
          case 'sig': return alt(() => {
            // term
            advance('Signature?', {value: 'name'});
            return inferrableTerm([], 'pi')
              .then(result => endTest([result]))
          })

          case 'def': return alt(() => {
            // term
            advance('Definition?'/*, {value: 'name'}*/)
            return inferrableTerm([], 'pi')
              .catch(err => { console.log(err); throw err })
              .then(result => endTest([result]))
          }).catch(() => alt(() => {
            // term : type
            advance('Sigdef?');
            return inferrableTerm([], 'ann')
              .catch(err => { console.log(err); throw err })
              .then(result => endTest([result]))
          }))

          case 'tcon': return alt(() => {
            // name telescope : type
            advance('Type/record constructor?');
            throw 'TCon'
          })

          case 'dcon': return alt(() => {
            // name : telescope type (?)
            advance('Data constructor?');
            throw 'DCon'
          })

          case 'pat': return alt(() => {
            // @ terms := term
            advance('Pattern?');
            throw 'Pat'
          })

          case 'let': return alt(() => {
            // name := term
            advance('Let/where/case?');
            throw 'Let'
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

    function telescope (env, isPi) { // returns { boundvars, types }
      function boundvars () {
        // '{a} b c'
        advance('Binding variable?');
        if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index);
        let bvs = [[token, false]]
        return (function loop () { return alt(() => {
          advance('Binding next variable?');
          if (!('id' in token) || 'value' in token) error.parser_notid();
          // TODO: erased pi ...{a}...
          bvs.push([token, false]);
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
                bvs: bvs.map(x => x[0]).reverse().concat(e),
                tys: bvs.map(() => type).concat(t),
                eps: bvs.map(x => ({ parens: false, braces: true })[gly] || x[1]).reverse().concat(ep)
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

    function checkableTerm (env, clause) {
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
      switch (clause) {
        case 'pi': return altMsg('Try Pi', () =>
          // {bnd} (bnd)...
          telescope(env, true).then(({boundvars, types, epsilons}) => {
            advance('Function arrow? (leftmost)', {value: 'op', id: '->'}); //?
            // {bnd} (bnd)... -> term -> term...
            return checkableTerm(boundvars.concat(env), 'bind').then(piBound => {
              let type = types.shift();
              return types.reduce((acc, ty, i) => acc = new Term({pi: [t, acc, epsilons[i]]}), new Term({pi: [type, piBound, epsilons[0]]}))
            })
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
          }) })().catch(() => ts.reduce((acc, term) => a = new Term({app: [acc, term]}), tm))
        }).catch(() => tm))

        // Type
        case 'var': return alt(() => {
          advance('Star?', {id: 'Type'});
          return new Term({star: []})
        }) // a *or* [x=>][(x:X)->] x
        .catch(() => alt(() => {
          advance('Variable term?');
          if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index);
          let i = env.findIndex(bv => bv.id === token.id);
          return ~i ? new Term({boundvar: [i]}) : new Term({freevar: [ new Name({global: [token.id]}) ]})
        })) // (pi)
        .catch(() => enclosure(['parens'], () => inferrableTerm(env, 'pi')))
      }
    }

    function lambda (env) {
      return altMsg('Try Lambda', () => {
        advance('Lambda bound variable?');
        if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index);
        let bvs = [];
        // x, y, ...
        return (function loop () { return alt(() => {
          bvs.push(token);
          advance('Lambda comma?', {value: 'punc', id: ','});
          // TODO: erased lambda {x}, y,...
          advance('Lambda next variable?');
          if (!('id' in token) || 'value' in token) throw new Error('');
          return loop()
        }) // x, y, ... =>
        .catch(err => { if (!err.message) error.parser_mismatch(token, index) }) })().then(() => {
          advance('Lambda arrow?', {value: 'op', id: '=>'});
          // x, y, .. => term
          return checkableTerm(bvs.reverse().concat(env), 'bind')
            .then(tm => bvs.reduce(a => a = new Term({lam: [a]}), tm))
        })
      })
    }

    let token = tokens[0], index = 0, level = 0;
    return parseStatement([], [])
      .then(result => (debug('Expression:', result), result))
      .catch(err => console.log(err))
  }

  // Typechecking

  function typecheck (arg) {
    console.log(...arg.map(x => x.toString()));
    return arg
  }

  // API

  let R = { Data, Sig, Def },
      sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  Object.defineProperty(R, 'ready', { get () { return sequence(() => new Promise(r => setTimeout(r, 0))) } });

  return R
})();

// Testing

(async () => {
  let passFail = obj => {
    for (let test in obj) try { console.log(obj[test]()) }
      catch (e) { console.log(test, e) }
  }

  // Tests
  let id1 = new R
    .Sig('id', '(T : Type) -> T -> T')
    .Def('(t, x => x)');
  let id2 = new R.Def("id'", '(x => x) : {T : Type} -> T -> T',
    { toString () { return this.value[0].toString() },
      valueOf () { return this.value[0].valueOf() } }
  );
  // let test3 = new R.Data('Unit : Type', ['tt : Unit'], { fromJS: () => Unit().tt() });
  // passFail({ test1, test2, test3 })
  await R.ready;

  // passFail({ test1: () => test1, test2, test3 });
  // let test4 = test1.Def('t, x => x');
  // passFail({ test4 });
  // await R.ready;
  //
  // passFail({ test4 })
})()
