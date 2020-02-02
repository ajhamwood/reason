var R = (() => {

  // Utilities

  const error = {
        unchecked: () => { throw new Error('Type error: unchecked') },
        lexer: (err, col, info) => { throw new Error(`Lexer error: ${err}\nat ${col}\n${info}`) },
        parser:  () => { throw new Error('Parser error') },
        parser_mismatch: (token, index, id, match) => {
          throw new Error(`Parser error: mismatch at '${token.id}', '${token.value}', token #${index}: expected '${id}', '${match}'`) },
        parser_nesting: () => { throw new Error('Parser error: parens nest level too deep') },
        parser_notid: () => { throw new Error('Parser error: not an identifier') },
        internal_ctor_args: () => { throw new Error('Wrong number of constructor arguments') },
        internal_ctor_invalid: (inv, ctors) => { throw new Error(`${inv} not a valid constructor. Looking for: ${(inv, ctors).join(', ')}`); }
      }, showDebug = true;

  // Interpreter

  // Data(tcon, [dcons], {...builtins})
  // Data(tcon, [{dcons}], {...builtins})
  class Data {
    constructor (tcon, dcons, builtins) {
      let ready = false, self = {},
          tconLex = tokenise({sourceString: tcon}),
          lexes = [tconLex].concat(dcons.map(dcon => {
            if (typeof dcon === 'string') return tokenise({sourceString: dcon});
            else return tokenise({sourceString: Object.keys(dcon)[0]})
          }));
      lexes.reduce((p, l) => p = p.then(acc => acc.concat([parse(l)])), Promise.resolve([]))
        .then(typecheck).then(decl => {
          ready = true;
          null
        });
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
      let ready = false, self = {},
          lex = tokenise({name, sourceString: declString});
      console.log(lex)
      parse(lex).then(typecheck).then(decl => {
        ready = true;
        null
      });
      return { Def: (...args) => {
        if (ready) return new Def(...args)
        else error.unchecked()
      } }
    }
  }

  // Def(name, sigdef, {...builtins})
  class Def {
    constructor (name, declString, builtins) {
      let ready = false, self = {},
          lex = tokenise({name, sourceString: declString});
      parse(lex).then(typecheck).then(decl => {
        ready = true;
        null
      });
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
    let rx_token = /^((\s+)|([a-zA-Z][a-zA-Z0-9_]*[\']*)|([:!$%&*+./<=>\?@\\^|\-~\[\]]{1,5})|(0|-?[1-9][0-9]*)|([(),"]))(.*)$/,
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
        case 'pi': return `${this.value[2] && 'Erased'}Pi(${this.value[0].toString()}, ${this.value[1].toString()})`;
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

  function parse (lex) {
    function debug (msg, res) {
      if (!showDebug) return;
      switch (msg) {
        case 'parens_open': console.group('Try parens'); break;
        case 'group_end': console.groupEnd(); break;
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
      return endTest([]).catch(() => alt(() => {
        // type
        advance('Signature?', {value: 'name'});
        throw 'Sig'
      })).catch(() => alt(() => {
        // term : type
        advance('Sigdef?');
        return telescope([], false)
          .then(({boundvars, types}) => console.log('@sigdef', boundvars, types))
          .then(() => endTest([]))
      })).catch(() => alt(() => {
        // name telescope : type
        advance('Type/record constructor?');
        throw 'TCon'
      })).catch(() => alt(() => {
        // name : telescope type (?)
        advance('Data constructor?');
        throw 'DCon'
      })).catch(() => alt(() => {
        // @ terms := term
        advance('Pattern?');
        throw 'Pat'
      })).catch(() => {
        // name := term
        advance('Let/where/case?');
        throw 'Let'
      })
    }

    function enclosure (glyphs, fn) {
      if (level > 20) error.parser_nesting();
      let gly
      return glyphs.reduce((p, glyph) => p = p.catch(() => alt(() => {
        let [open, close] = ({ parens: ['(', ')'], braces: ['{', '}'] })[gly = glyph]
        advance('Open enclosure?', {id: 'punc', value: open});
        debug('parens_open');
        level++
        return fn().then(result => {
          advance('Close enclosure?', {id: 'punc', value: close});
          debug('group_end');
          level--;
          return [result]
        }).catch(err => {
          debug('group_end');
          level--;
          throw err
        })
      })), Promise.reject()).then(result => [result, gly])
    }

    function telescope (env, isPi) { // returns { boundvars, types }
      function boundvars () {
        // '{a} b c'
        advance('Binding variable?');
        if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index);
        return (function loop (bvs) { return alt(() => {
          advance('Binding comma?', {id: 'punc', value: ','});
          advance('Binding next variable?');
          if (!('id' in token) || 'value' in token) error.parser_notid();
          // TODO: ...{a}...
          bvs.push([token, false]);
          return loop(bvs)
        }).catch(() => {
          advance('Binding operator?', {id: 'op', value: ':'});
          return bvs
        }) })([token])
      }
      return altMsg('Try bindings', function loop (e, t, ep) {
        return enclosure(['parens', 'braces'], boundvars).then(([{bvs, type}, which]) => {
          checkableTerm(isPi ? e : [], 'bind').then(type => ({
            bvs: bvs.map(x => x[0]).reverse().concat(e),
            tys: bvs.map(() => type).concat(t),
            eps: bvs.map(() => ({ parens: false, braces: true })[which]).concat(ep)
          }))
        }).then(tele => alt(() => loop(tele.bvs, tele.tys, tele.eps))
          .catch(() => ({boundvars: tele.bvs, types: tele.tys})))
      })(env, [], []).catch(() => boundvars().then(bvs =>
        checkableTerm(env, 'bind').then(tm =>
          ({boundvars: bvs.map(x => x[0]), types: boundvars.map(() => tm), epsilon: bvs.map(x => x[1])})
        )
      ))
    }

    function checkableTerm (env, clause) {
      switch (clause) {
        case 'bind': return altMsg('Try checkable term', () => lambda(env))
          .catch(() => inferrableTerm(env, 'pi'));
        default: return altMsg('Try checkable term', () => enclosure(['parens'], () => lambda(env)))
          .catch(() => inferrableTerm(env, clause))
      }
    }

    function inferrableTerm (env, clause) {
      function arrow (env, term) {
        advance('Function arrow?', {id: 'op', value: '->'});
        return inferrableTerm([''].concat(env), 'pi')
          .then(piBound => new Term({pi: [ term, piBound ]}))
      }
      function annot (term) {
        return alt(() => {
          advance('Annotated term?', {id: 'op', value: ':'});
          return checkableTerm(env, 'bind')
            .then(ty => new Term({ann: [term, ty]}))
        })
      }
      switch (clause) {
        // {bnd}(bnd)->type->type
        case 'pi': return altMsg('Try Pi', () =>
          telescope(env, true).then(({boundvars, types, epsilon}) => {
            advance('Function arrow? (leftmost)', {id: 'op', value: '->'}); //?
            checkableTerm(boundvars.concat(env), 'bind').then(piBound => {
              let type = types.shift();
              return types.reduce((acc, ty, i) => acc = new Term({pi: [t, acc, epsilon[i]]}), new Term({pi: [type, piBound, epsilon[0]]}))
            })
          })
        ) .catch(() => alt(() => lambda(env)))
          .catch(() => alt(() => inferrableTerm(env, 'ann').then(ann =>
            alt(() => arrow(env, ann)).catch(() => ann))
          ))

        case 'ann': return altMsg('Try Annotation', () => inferrableTerm(env, 'app').then(annot))
          .catch(() => enclosure(['parens'], () => lambda(env)).then(annot))

        case 'app': return inferrableTerm(env, 'var').then(tm => altMsg('Try apply', () => {
          let ts = [];
          debug('Application?');
          return (function loop () { return inferrableTerm(env, 'var').then(cterm => {
            ts.push(cterm);
            return loop()
          }) })().catch(() => ts.reduce((acc, term) => a = new AST.App(acc, term), tm))
        }).catch(() => tm))

        case 'var': return alt(() => {
          advance('Star?', {value: 'Type'});
          return new Term({star: []})
        }).catch(() => alt(() => {
          advance('Variable term?');
          if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index);
          let i = env.findIndex(bv => bv.id === token.id);
          return ~i ? new Term({boundvar: [i]}) : new Term({freevar: [ new Name({global: [token.id]}) ]})
        })).catch(() => enclosure(['parens', () => inferrableTerm(env, 'pi')]))
      }
    }

    function lambda (env) {
      return altMsg('Try Lambda', () => {
        advance('Lambda bound variable?');
        if (!('id' in token) || 'value' in token) error.parser_mismatch(token, index);
        let bvs = [];
        return (function loop () { return alt(() => {
          bvs.push(token);
          advance('Lambda comma?', {id: 'punc', value: ','});
          advance('Lambda next variable?');
          if (!('id' in token) || 'value' in token) throw new Error('');
          return loop()
        }).catch(err => { if (!err.msg) error.parser_mismatch(token, index) }) })().then(() => {
          advance('Lambda arrow?', {id: 'op', value: '=>'});
          return checkableTerm('bind', bvs.reverse().concat(env))
            .then(tm => bvs.reduce(a => a = new Term({lam: [a]}), tm))
        })
      })
    }

    let token, tokens = lex, index = 0, level = 0;
    return parseStatement([], [])
      .then(result => (debug('Expression:', result), result))
      .catch(error.parser)
  }

  // Typechecking

  function typecheck () {}

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
  let test1 = new R.Sig('id', '(T : Type) -> T -> T');
  // let test2 = new R.Def('id', '(t, x => x)(T : Type) -> T -> T');
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
