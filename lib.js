var Reason = options => {
  let { showDebug } = options;

  // Utilities

  const error = new Proxy({
            append (e1, which, ...args) { try { error[which](...args) } catch (e2) { throw new Error(e1.message + '\n' + e2.message) } }
          }, { get (o, prop) {
            if (prop in o) return o[prop];
            else return (...args) => { throw new Error((({
              // Interpreter errors
              duplicate: n => `Interpreter error: name '${n}' already exists`,
              nosig: n => `Interpreter error: no signature has been declared for ${n}`,
              notfound: n => `Interpreter error: declaration for ${n} cannot be found`,
              unchecked: () => 'Interpreter error: not yet typechecked',
              malf: which => `Interpreter error: malformed ${which}`,

              // Lexer errors
              lexer_unexpected: (char, match, pos) => `Lexer error: unexpected character${char ? ' ' + char : ''}${
                match ? ', looking for ' + match : ''} at position ${pos}`,
              lexer_missing: (match, pos) => `Lexer error: missing expected char ${match} at position ${pos}`,
              lexer_uncl_str: pos => 'Lexer error: unclosed string at position ' + pos,
              lexer_digits: pos => `Lexer error: expected digits at position ${pos}`,

              // AST errors
              internal_ctor_args: () => 'AST error: Wrong number of constructor arguments',
              internal_ctor_invalid: (inv, ctors) => `AST error: ${inv} not a valid constructor. Looking for: ${ctors.join(', ')}`,

              // Parser errors
              parser_mismatch: (token, index, id, match) => `Parser error: mismatch at '${token.id || ''}'${
                'value' in token ? `, '${token.value}'` : ''}, token #${index}${id ? `: expected '${id}'` : ''}${match ? `, '${match}'` : ''}`,
              parser_nesting: () => 'Parser error: parens nest level too deep',
              parser_notid: () => 'Parser error: not an identifier',
              parser_notvalid: which => `Parser error: not a valid ${which}`,

              // Typechecking errors
              tc_mismatch: (tested, given) => `Type error: mismatch at\n    ${tested.toString()}\nexpecting\n    ${given.toString()}`, // TODO: pretty print
              tc_lam_mismatch: ctor => `Type error: lambda has Pi type, not ${ctor}`,
              tc_lam_infer: () => 'Type error: cannot infer type of lambda',
              tc_ann_mismatch: tested => `Type error: annotation should have type Type, found ${tested.toString()}`,
              tc_pi_mismatch: (loc, tested) => `Type error: Pi ${loc} should have type Type, found ${tested.toString()}`,
              tc_app_mismatch: tested => `Type error: illegal application - expected type Pi, found ${tested.toString()}`,
              tc_bad_app: () => 'Type error: bad value application',
              tc_unknown_id: name => `Type error: unknown identifier ${name.value[0]}`,
              tc_dcon_ambiguity: () => 'Type error: ambiguous data constructor',
              tc_dcon_cannot_infer_params: () => 'Type error: cannot infer data constructor parameters. Try adding an annotation.',
              tc_dcon_arg_len: (mlen, tlen) => `Type error: data constructor given wrong number of arguments - (${mlen} instead of ${tlen})`,
              tc_mismatch_con: which => `Type error: ${which} constructor given, but expected ${which === 'type' ? 'data' : 'type'} constructor`,

              tc_erased_var_subst: () => 'Type error: erased variable used in lambda',
              tc_erasure_mismatch: () => 'Type error: erasure mismatch',
              tc_constraint_cannot_eq: (lhs, rhs) => `Cannot equate lhs and rhs of constraint ${lhs.toString()} = ${rhs.toString()}`,

              tc_erased_pat: () => 'Type error: cannot pattern match erased arguments',
              tc_pat_dcon_len: dir => `Type error: ${dir ? 'too many' : 'not enough'} patterns in match for data constructor`,
              tc_pat_len: name => `Type error: wrong number of args to pattern ${name}`,
              tc_pat_cannot_omit: name => `Type error: case for ${name.toString()} cannot be omitted (yet)`,
              tc_dcon_cannot_infer: () => 'Type error: cannot infer data constructor',
              tc_missing_cases: l => `Type error: missing cases for ${l.map(x => x.toString()).join(', ')}`,
              tc_subpat_cannot_dcon: () => 'Type error: cannot use data constructor in subpattern (yet)',

              tc_internal: () => 'Type error: internal construct',

              // Internal error
              internal: fname => `Internal error: at function ${fname}`,
              internal_arg: fname => `Internal error: internal function ${fname} given illegal arguments`,
              internal_cant_find: cname => `Internal error: can't find ${cname}`
            })[prop] || (() => prop))(...args)) }
          } });
  function triggerProxyPromise () { // TODO: replace Promises with a synchronous thenable error monad
    let px = (obj, args) => new Proxy(new obj(...args), { get (p, prop) {
      if (prop === 'catch') return cb => p.catch(err => {
        console.groupCollapsed(`%c${err && err.message}`, 'font-weight: bold; color: red');
        console.log(err);
        console.groupEnd();
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

  let active = [];
  function wait (declType, name) {
    if (~active.findIndex(([d, n]) => d === declType && n === name)) error.duplicate(declType, name);
    else active.push([declType, name])
  }
  function unwait (declType, name) {
    let i = active.findIndex(([d, n]) => d === declType && n === name);
    if (!~i) error.notfound(declType, name)
  }
  function waiting (declType, name) {
    return !!~active.findIndex(([d, n]) => d === declType && n === name)
  }




  // Interpreter

  // Data(name, tcon, [dcons], {...builtins})
  // Data(name, tcon, [{dcons}], {...builtins})
  class Data {
    constructor (name, ddef, cdefs, builtins) {
      wait('data', name);
      let ready = false, jsTerm = {},
          ddefLex = tokenise({name, sourceString: ddef}),
          cdefLexes = cdefs.map(cdef => {
            if (typeof cdef === 'string') return tokenise({sourceString: cdef});
            else return tokenise({sourceString: Object.keys(cdef)[0]})
          });
      sequence(() => cdefLexes.reduce((p, l) => p.then(acc => parse(l, 'cdef').then(res => (acc[0].value[2].push(res[0]), acc))), parse(ddefLex, 'ddef'))
        .then(decls => typecheck(decls, context)).then(res => {
          let [{declName, params, type, ctors}] = res,
              appliedTerms = [];
          if (declName === 'data') Object.assign(jsTerm, {params, type, ctors, appliedTerms})
          ready = true;
          unwait('data', name)
        }));
      return jsTerm = Object.assign((...args) => {
        if (ready) {
          jsTerm.appliedTerms = jsTerm.appliedTerms.concat(args);
          return jsTerm
        } else error.unchecked()
      }, jsTerm)
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
        let [{declName, term, type, value}] = res;
        if (declName === 'sig') Object.assign(jsTerm, {type: term, typeValue: value});
        ready = true;
        unwait('sig', name)
      }));
      return { Def: (...args) => jsTerm = Object.assign(new Def(name, ...args), jsTerm) }
    }
  }

  // Def(name, sigdef, {...builtins})
  // Def(name, [pats])
  class Def {
    constructor (name, declStrings, builtins) {
      wait('def', name);
      let ready = false, jsTerm = builtins, lex;
      if (typeof declStrings === 'string') {
        lex = tokenise({name, sourceString: declStrings});
        sequence(() => parse(lex, 'def').then(decls => typecheck(decls, context)).then(ress => {
          ress.forEach(res => {
            let {declName, term, type, value} = res,
                appliedTerms = [];
            if (declName === 'sig') Object.assign(jsTerm, {type: term, typeValue: value});
            if (declName === 'def') Object.assign(jsTerm, {term, value, typeValue: type, appliedTerms})
          })
          ready = true;
          unwait('def', name)
        }));
      } else if (Array.prototype.isPrototypeOf(declStrings)) {
        sequence(() => declStrings.map(declString => tokenise({name, sourceString: declString}))
          .reduce((p, lex) => p.then(acc => parse(lex, 'pat').then(res => acc.concat([res]))), Promise.resolve([]))
          .then(decls => typecheck(decls, context))).then(ress => {
            // ress.forEach(res => {
            //   let {declName, term, type, value} = res,
            //       appliedTerms = [];
            //   if (declName === 'sig') Object.assign(jsTerm, {type: term, typeValue: value});
            //   if (declName === 'def') Object.assign(jsTerm, {term, value, typeValue: type, appliedTerms})
            // })
            jsTerm.pats = ress;
            ready = true;
            unwait('def', name)
          })
      } else {
        let e = Object.entries(declStrings);
        if (e.length !== 1) error.malf('definition');
        let [caseDef, pats] = e[0], caseLex = tokenise({name, sourceString: caseDef}),
            patLexes = pats.map(pat => tokenise({sourceString: pat}));
        sequence(() => parse(caseLex, 'case').then(([bvs, fn]) => patLexes.reduce((p, pat) =>
          p.then(acc => parse(pat, 'pat', {casePat: true, bvs}).then(res => acc.concat([res]))), Promise.resolve([]))
            .then(matches => [fn(matches.flat())]))
            .then(decls => typecheck(decls, context)).then(ress => {
              ress.forEach(res => {
                let {declName, term, type, value} = res,
                    appliedTerms = [];
                if (declName === 'sig') Object.assign(jsTerm, {type: term, typeValue: value});
                if (declName === 'def') Object.assign(jsTerm, {term, value, typeValue: type, appliedTerms})
              });
              ready = true;
              unwait('def', name)
            })
        )
      }
      return jsTerm = Object.assign((...args) => {
        if (ready) {
          jsTerm.appliedTerms = jsTerm.appliedTerms.concat(args);
          return jsTerm; // TODO: typecheck and return new term
        }else error.unchecked()
      }, jsTerm)
    }
  }



  // Lexer

  function tokenise ({name, sourceString}) { // TODO: refactor using alt()
    let rx_token = /^((\s+)|([a-zA-Z][a-zA-Z0-9_]*[\']*)|([:!$%&*+.,/<=>\?@\\^|\-~\[\]]{1,5})|(0|-?[1-9][0-9]*)|([(){}"]))(.*)$/,
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
        else if (char === '') error.lexer_uncl_str(pos);
        else if (char === '\\') {
          nextchar('\\');
          if (char === '') error.lexer_uncl_str(pos);
          else if (char === '"') nextchar()
        }
        else nextchar();
        return next()
      })()
    }
    function snip () { word = word.slice(0, -1) } // from end
    function nextchar (match) {
      if (match && match !== char) char ?
        error.lexer_unexpected(char, match, pos - 1) :
        error.lexer_missing(match, pos - 1);
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
      if (/[0-9a-zA-Z]/.test(char)) error.lexer_unexpected(char, null, col);
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
      } else return error.lexer_digits(col)
    }

    return (function lex () {
      let result;
      if (!sourceString) {
        make({value: 'final'});
        return tokens;
      }
      result = sourceString.match(rx_token);
      if (!result) error.lexer_unexpected(sourceString[0], null, pos);
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

  class Term extends AST('ann', 'star', 'pi', 'lam', 'app', 'boundvar', 'freevar' ,'tcon', 'dcon', 'case') {
    equal (operand) {
      return this.ctor === operand.ctor &&
        this.value.every((x, i) => x === operand.value[i] ||
          ('equal' in x && x.equal(operand.value[i])) ||
          ('every' in x && x.every((y, j) => y === operand.value[i][j])))
    }
    toString () {
      switch (this.ctor) {
        case 'ann': return `(${this.value[0].toString()} : ${this.value[1].toString()})`
        case 'star': return 'Type'
        case 'pi': return `${this.value[2] ? 'Erased' : ''}Pi(${this.value[0].toString()}, ${this.value[1].toString()})`
        case 'lam': return `${this.value[1] ? 'Erased' : ''}Lam(${this.value[0].toString()})`
        case 'app': return `${this.value[0].toString()} :@: ${this.value[1].toString()}`
        case 'boundvar': return `Bound ${this.value[0]}`
        case 'freevar': return `Free ${this.value[0]}`

        case 'tcon': return `TC:${this.value[0].toString()}${this.value[1].map(x => ` (${x.toString()})`).join('')}`
        case 'dcon': return `DC:${this.value[0].toString()}${this.value[1].map(x => ` ${x.toString()}`).join('')}`

        case 'case': return `Case ${this.value[0].toString()} |${this.value[1].map(x => `\n  ${x.toString()}`).join('')}`
      }
    }
  }

  class Name extends AST('global', 'local', 'quote') {
    equal (operand) {
      return this.ctor === operand.ctor && this.value[0] === operand.value[0]
    }
    toString () {
      switch(this.ctor) {
        case 'global': return typeof this.value[0] === 'number' ? '_' + this.value[0] : `Global <${this.value[0]}>`
        case 'local': return `Local ${this.value[0]}`
      } }
  }

  class Item extends AST('term', 'erased', 'constraint') { // TODO combine term and erased - (name, term, ep)
    equal (operand) { return this.ctor === operand.ctor && this.value.every((x, i) => x.equal(operand.value[i]))}
    toString () {
      switch(this.ctor) {
        case 'term': return `(${this.value.map(x => x.toString()).join(':')})`
        case 'erased': return `{${this.value.map(x => x.toString()).join(':')}}`
        case 'constraint': return `{${this.value.map(x => x.toString()).join('=')}}`
      }
    }
  }
  class Tele {
    items = []
    length = 0
    constructor (...items) {
      for (let item of items) {
        if (item.ctor === 'term') this.length++;
        this.items.push(item)
      }
    }
    term (...args) {
      this.items.push(new Item({term: args.filter(x => typeof x !== 'undefined')}));
      this.length++;
      return this
    }
    erased (...args) {
      this.items.push(new Item({erased: args.filter(x => typeof x !== 'undefined')}));
      return this
    }
    constraint (...args) {
      this.items.push(new Item({constraint: args.filter(x => typeof x !== 'undefined')}));
      return this
    }
    tail () { return new Tele(...this.items.slice(0, -1)) }
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

  class Arg extends AST('arg') { // Only dcons and patdcons have Args
    toString () { return this.value[1] ? `{${this.value[0].toString()}}` : `(${this.value[0].toString()})` }
  }

  class Pat extends AST('patdcon', 'patvar') { // TODO: add inaccessible patterns
    toString () {
      switch (this.ctor) {
        case 'patdcon': return `PatDCon ${this.value[0].toString()}${this.value[1].map(x => ` ${x.toString()}`)}`
        case 'patvar': return 'PatVar ' + this.value[0].toString()
      }
    }
  }
  class Match extends AST('match') {
    toString () { return `PatMatch @ ${this.value[0].toString()} := ${this.value[1].toString()}` }
  }




  // Parser

  let parser = new (class Parser {
    tnames = []
    dnames = []
    fresh = (i => () => i++)(0)
    parse (tokens, sourceName, parseOptions = {}) {
      // TODO: mixfix operators
      // triggerProxyPromise()

      function debug (msg, res) {
        if (!showDebug) return;
        switch (msg) {
          case 'group_end': console.groupEnd(); break;

          case 'End statement?': console.log(`%c${msg}`, 'font-weight: bold', token, index); break;
          case 'Signature?': console.log(`%c${msg}`, 'font-weight: bold; color: goldenrod', token, index); break;
          case 'Definition?': console.log(`%c${msg}`, 'font-weight: bold; color: rebeccapurple', token, index); break;
          case 'Signature with definition?': console.log(`%c${msg}`, 'font-weight: bold; color: turquoise', token, index); break;
          case 'Type/record definition?': console.log(`%c${msg}`, 'font-weight: bold; color: forestgreen', token, index); break;
          case 'Constructor definition?': console.log(`%c${msg}`, 'font-weight: bold; color: dodgerblue', token, index); break;
          case 'Pattern?': console.log(`%c${msg}`, 'font-weight: bold; color: firebrick', token, index); break;
          case 'Case statement?': console.log(`%c${msg}`, 'font-weight: bold; color: deeppink', token, index); break;
          case 'Let/where?': console.log(`%c${msg}`, 'font-weight: bold; color: deepskyblue', token, index); break;
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
      function altNames (fn) {
        let rewind = index, tnames = [], dnames = [];
        return new Promise(r => r(fn.bind({tnames, dnames})())).then(res => {
          parser.tnames = parser.tnames.concat(tnames);
          parser.dnames = parser.dnames.concat(dnames.filter(c => !~parser.dnames.indexOf(c)));
          return res
        }).catch(err => {
          index = rewind;
          throw err
        })
      }
      function altMsg (msg, fn) {
        return alt(!showDebug ? fn : () => {
          console.group(msg);
          return fn()
        }).then(result => {
          console.groupEnd();
          return result
        }).catch(err => {
          console.groupEnd();
          throw err
        })
      }

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

            case 'ddef': return altNames(function () {
              // name bindings : type
              advance('Type/record definition?', {value: 'name'});
              let name = token;
              this.tnames.push(name.id);
              return dataDef([], 'ddef')
                .then(result => endTest([new Decl({data: [ new Name({global: [name.id]}), result, [] ] })]))
                .catch(() => error.parser_notvalid('type definition'))
            })

            case 'cdef': return altNames(function () {
              // name : bindings type (?)
              advance('Constructor definition?');
              assertId();
              let name = token;
              this.dnames.push(name.id);
              advance('Type constructor separator?', {value: 'op', id: ':'});
              return dataDef([], 'cdef')
                .then(result => endTest([new Ctor({ctor: [ new Name({global: [name.id]}), result ]})]))
                .catch(() => error.parser_notvalid('constructor definition'))
            })

            case 'case': return alt(() => {
              // args | term
              advance('Case statement?');
              let name = token.id;
              return caseOf([])
                .then(([bvs, fn]) => endTest([bvs, x => new Decl({def: [ new Name({global: [name]}), fn(x) ]})]))
                .catch(() => error.parser_notvalid('case statement'))
            })

            case 'pat': return alt(() => {
              // @ args := term
              let name;
              if (parseOptions.casePat) debug('Pattern?');
              else {
                advance('Pattern?');
                name = token.id;
                advance('Pattern marker?', {value: 'op', id: '@'});
              }
              return pattern(parseOptions.bvs || [])
                .then(([pat, env]) => {
                  advance('Pattern equation separator?', {value: 'op', id: ':='});
                  return checkableTerm(env, 'ann')
                    .then(term => endTest([new Match({match: [pat, term]})])) // This should be a binder
                })
                .catch(() => error.parser_notvalid('pattern'))
            })

            case 'let': return alt(() => {
              // name := term
              advance('Let/where?');
              return Promise.reject()
                .catch(() => error.parser_notvalid('let construct'))
            })
          }
        })
      }

      function enclosure (glyphs, fn) {
        if (level > 20) error.parser_nesting();
        let gly;
        return glyphs.reduce((p, glyph) => p.catch(() => altMsg('Try enclosure', () => {
          let [open, close] = ({ parens: ['(', ')'], braces: ['{', '}'] })[gly = glyph]
          level++;
          advance(`Open ${gly}?`, {value: 'punc', id: open});
          return fn().then(result => {
            advance(`Close ${gly}?`, {value: 'punc', id: close});
            return result
          })
        }).then(result => {
          level--;
          return result
        }).catch(err => {
          level--;
          throw err
        })), Promise.reject()).then(result => glyphs.length > 1 ? [result, gly] : result)
      }

      function bindings (env, isPi) { // returns { boundvars, types, epsilons }
        function bindvars () { // If a lone binding is in context, it's a value. Otherwise, it's a type.
          // '{a} b c'
          advance('Binding variable?');
          assertId();
          let bvs = [[token, false]]
          return (function loop () { return alt(() => {
            advance('Binding next variable?');
            if (!('id' in token) || 'value' in token) error.parser_notid();
            bvs.unshift([token, false]);
            return loop()
          }).catch(() => {
            // vars : ...
            advance('Binding operator?', {value: 'op', id: ':'});
            return bvs
          }) })()
        }
        return altMsg('Try bindings', () => {
          let tele = {bvs: [], tys: [], eps: []};
          return (function loop (e, t, ep) {
            // (bnd) *or* {bnd}
            return enclosure(['parens', 'braces'], () =>
              bindvars().then(bvs => checkableTerm(isPi ? e : [], 'bind').then(type => [bvs, type])))
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
            .catch(() => bindvars().then(bvs =>
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

        switch (clause) {
          // {bnd} (bnd)...
          case 'pi': return altMsg('Try Pi', () =>
            bindings(env, true).then(({boundvars, types, epsilons}) => {
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
          case 'ann': return altMsg('Try Annotation', () => inferrableTerm(env, 'ctor'))
            .catch(() => alt(() => inferrableTerm(env, 'app'))).then(annot)
            // (lam) : term
            .catch(() => enclosure(['parens'], () => lambda(env)).then(annot))

          // t a b...
          case 'ctor': return altMsg('Try Constructor', () => {
            advance('Constructor term?');
            assertId();
            let ts = [], eps = [], name = token.id, ctor;
            if (~parser.tnames.indexOf(name)) ctor = 'tcon';
            else if (~parser.dnames.indexOf(name)) ctor = 'dcon';
            else throw new Error('');
            return (function loop () { return (ctor === 'tcon' ?
              checkableTerm(env, 'var').then(cterm => [cterm, false]) :
              enclosure(['braces'], () => checkableTerm(env, 'var').then(cterm => [cterm, true]))
                .catch(() => checkableTerm(env, 'var').then(cterm => [cterm, false])))
                .then(([term, ep]) => {
                  ts.push(term);
                  eps.push(ep);
                  return loop()
                })
            })().catch(() => new Term({[ctor]: [ new Name({global: [name]}),
              ts.map((x, i) => ctor === 'tcon' ? x : new Arg({arg: [ x, eps[i] ]}))
            ]}))
          })

          // f a b...
          case 'app': return inferrableTerm(env, 'var').then(tm => altMsg('Try apply', () => {
            let ts = [], eps = [];
            debug('Application?');
            return (function loop () { return enclosure(['braces'], () => checkableTerm(env, 'var').then(cterm => [cterm, true]))
              .catch(() => checkableTerm(env, 'var').then(cterm => [cterm, false]))
              .then(([term, ep]) => {
                ts.push(term);
                eps.push(ep);
                return loop()
              })
            })().catch(() => ts.reduce((acc, term, i) => acc = new Term({app: [acc, term, eps[i]]}), tm))
          }).catch(() => tm))

          // Type
          case 'var': return alt(() => {
            advance('Star?', {id: 'Type'});
            return new Term({star: []})
          }) // data constructor
            .catch(() => alt(() => inferrableTerm(env, 'ctor')))
             // a *or* [x=>][(x:X)->] x
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
              advance('Lambda comma?', {value: 'op', id: ','});
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

      function dataDef (env, clause) {
        let data = clause === 'ddef';
        return altMsg(`Try ${data ? 'Type' : 'Constructor'} Definition`, () =>
          alt(() => bindings(env, false).then(tele => {
            data ?
              // {bnd} (bnd)... : term -> term...
              advance('Typedef separator?', {value: 'op', id: ':'}) :
                // {bnd} (bnd)... -> term -> term...
              advance('Condef arrow? (leftmost)', {value: 'op', id: '->'});
            return tele
          })).catch(() => ({boundvars: [], types: [], epsilons: []}))
            .then(({boundvars, types, epsilons}) => inferrableTerm(env, 'pi').then(typeFam =>
              types.reduceRight((acc, ty, i) => acc[epsilons[i] ? 'erased' : 'term'](new Name({global: [boundvars[i].id]}), ty), new Tele())
                .term(new Name({global: [parser.fresh()]}), typeFam)
            ))
        )
      }

      function pattern (env, name) {
        function atomic () {
          // (pat)
          return enclosure(['parens'], () => pattern(env, name).then(([res, env]) => res))
            // _
            .catch(() => alt(() => {
              advance('Wildcard?', {id: '_'});
              return new Pat({patvar: [new Name({global: [parser.fresh()]})]})
            }))
            // t *or* x
            .catch(() => {
              advance('Variable or constructor term?');
              assertId();
              let nestedName = token.id;
              if (~parser.tnames.indexOf(nestedName)) error.tc_mismatch_con('type');
              else if (~parser.dnames.indexOf(nestedName)) return new Pat({patdcon: [new Name({global: [nestedName]}), []]})
              else return new Pat({patvar: [new Name({global: [nestedName]})]})
            })
        }
        return altMsg('Try Constructor Pattern', () => {
          advance('Constructor term?');
          assertId();
          let name = token.id, ts = [];
          if (~parser.tnames.indexOf(name)) error.tc_mismatch_con('type');
          else if (~parser.dnames.indexOf(name)) return (function loop () {
            // {x}
            return enclosure(['braces'], () => pattern(env, name).then(([term, env]) => [term, true]))
              // x
              .catch(() => alt(() => atomic()).then(term => [term, false]))
              .then(([term, ep]) => {
                ts.push(new Arg({arg: [term, !!ep]}));
                return loop()
              })
          })().catch(() => new Pat({patdcon: [new Name({global: [name]}), ts]}));
          else throw new Error('')
        }).catch(atomic)
          .then(res => [res, env])
      }

      function caseOf (env) {
        return altMsg('Try Case Statement', () => {
          let bvs = [], eps = [], adv = () => { advance('Next case variable?'); assertId(); return token };
          return (function loop () { return enclosure(['braces'], () => alt(adv).then(bv => [bv, true]))
            .catch(() => alt(adv).then(bv => [bv, false]))
            .then(([bv, ep]) => {
              bvs.unshift(bv);
              eps.unshift(ep);
              return loop()
            })
          })().catch(() => advance('Case separator?', {value: 'op', id: '|'}))
            .then(() => checkableTerm(bvs.concat(env), 'ann').then(tm =>
              [bvs, x => bvs.reduce((acc, _, i) => new Term({lam: [acc, eps[i]]}), new Term({case: [tm, x]}))]
            ))
        })
      }

      let token = tokens[0], index = 0, level = 0;
      return parseStatement([], [])
        .then(result => (debug('Expression:', result), result))
    }
  }), { parse } = parser;




  // Typechecking

  class Context {
    decls = []
    constructor (obj) { if (obj) this.decls = obj.decls.slice() }
    lookup (name, ctor, annot) {
      if (ctor === 'ctor') {
        let mbCdef;
        if (typeof annot === 'undefined') return this.decls.reduce((a, decl) => {
          if (decl.ctor === 'data' && (mbCdef = decl.value[2].find(cdef => cdef.value[0].equal(name))))
            a.push({tname: decl.value[0], ddef: decl.value[1], cdef: mbCdef.value[1]});
          return a
        }, []);
        else {
          let mbDdef = this.decls.find(decl => decl.ctor === 'data' && decl.value[0].equal(annot) &&
            (mbCdef = decl.value[2].find(cdef => cdef.value[0].equal(name))));
          return { ddef: mbDdef ? mbDdef.value[1] : null, cdef: mbCdef ? mbCdef.value[1] : null }
        }
      }
      let result = this.decls.find(decl => (decl.ctor === ctor || (ctor === 'data' && decl.ctor === 'datasig')) && decl.value[0].equal(name));
      if (result) return ctor === 'data' ? { ddef: result.value[1], cdef: result.ctor === 'datasig' ? null : result.value[2] } : result.value[1]
    }
    cons (decl) { return this.push(decl, true) }
    extend (decl) { return this.push(decl, false) }
    push (decl, n) {
      let ret = n ? new Context(this) : this;
      if (Array.prototype.isPrototypeOf(decl)) ret.decls = ret.decls.concat(decl);
      else ret.decls.push(decl);
      return ret
    }
    localVal (i) { return this.decls[this.decls.length - i - 1].value[1] }
    concatTele (tele) {
      return tele.items.reduce((acc, item) => { switch (item.ctor) {
        case 'term': case 'erased': return acc.cons(new Decl({sig: [item.value[0].value[0], item.value[1]]}))
        case 'constraint': return acc.cons({def: item.value})
      } }, new Context(this))
    }
  }
  const context = new Context();

  function typecheck (decls) {
    // triggerProxyPromise()

    // Infer/check
    function infer (args) { //context, term, number -> value
      let { ctx, term, index = 0 } = args, innerArgs;
      return Promise.resolve().then(() => {
        let result, vstar = new Value({vstar: []}), local = new Name({local: [index]});
        switch (term.ctor) {
          case 'star': return vstar

          case 'ann':
          let annTerm = term.value[0];
          return check(ctx, term.value[1], vstar, index)
            .catch(e => error.append(e.message, 'tc_ann_mismatch', '?'))
            .then(({term}) => check(ctx, annTerm, evaluate(term, ctx), index))

          case 'pi': return infer(innerArgs = {ctx, term: term.value[0], index})
            .then(type1 => {
              term.value[0] = innerArgs.term;
              if (type1.ctor !== 'vstar') error.tc_pi_mismatch('domain', quote(type1));
              return infer(innerArgs = {
                ctx: ctx.cons(new Decl({sig: [ local, evaluate(term.value[0], ctx) ]})),
                term: subst(new Term({freevar: [ local ]}), term.value[1], false), index: index + 1})
                .then(type2 => {
                  term.value[1] = innerArgs.term;
                  if (type2.ctor !== 'vstar') error.tc_pi_mismatch('range', quote(type2));
                  return vstar
                })
            })

          case 'app':
          return infer({ctx, term: term.value[0], index})
            .then(type => {
              if (type.ctor !== 'vpi') error.tc_app_mismatch(quote(type));
              let [dom, func] = type.value;
              return check(ctx, term.value[1], dom, index)
                .then(({term}) => func(evaluate(term, ctx)))
            })

          case 'freevar':
          if (result = ctx.lookup(term.value[0], 'sig')) return result
          error.tc_unknown_id(term.value[0])

          case 'tcon':
          if (term.value.length === 1) term.value.push([]) //?
          result = ctx.lookup(term.value[0], 'data').ddef;
          if (result.items.length - 1 > term.value[1].length) error.tc_dcon_arg_len(term.value[1].length, result.items.length - 1);
          else if (result.items.length - 1 < term.value[1].length)
            return infer({ctx, term: args.term = term.value[1].slice(result.items.length - 1).reduce((acc, tm) => new Term({app: [acc, tm, false]}),
              new Term({tcon: [term.value[0], term.value[1].slice(0, result.items.length - 1)]})), index});
          return tcArgTele(ctx, term.value[1].map(x => new Arg({arg: [x, false]})), result.tail()).then(() => result.items.slice(-1)[0].value[1])

          case 'dcon':
          if (typeof term.value[2] !== 'undefined') return check(ctx, term, term.value[2], index);
          if (term.value.length === 1) term.value.push([]) //?
          let matches = ctx.lookup(term.value[0], 'ctor');
          if (matches.length !== 1) error.tc_dcon_ambiguity();
          let match = matches[0];
          if (match.ddef.length !== 1) error.tc_dcon_cannot_infer_params();
          if (match.cdef.length - 1 > term.value[1].length) error.tc_dcon_arg_len(term.value[1].length, match.cdef.length - 1);
          else if (match.cdef.length - 1 < term.value[1].length)
            return infer({ctx, term: args.term = term.value[1].slice(match.cdef.length - 1).reduce((acc, tm) => new Term({app: [acc, ...tm.value]}),
              new Term({dcon: [term.value[0], term.value[1].slice(0, match.cdef.length - 1)].concat([term.value[2]].filter(x => x))})), index});
          return tcArgTele(ctx, term.value[1], match.cdef.tail()).then(() => evaluate(new Term({tcon: [ match.tname, [] ]}), ctx))

          case 'lam': error.tc_lam_infer()

          case 'case': throw new Error('here')
        }
      })
    }

    function check (ctx, term, typeVal, index = 0) { //context, term, term, number -> term:term, type:value
      let innerArgs;
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
              .then(({term}) => ({term: new Term({lam: [unsubst(new Term({boundvar: [ index ]}), term), typeVal.value[2]]}), type: typeVal}))
          }

          case 'dcon':
          let type = quote(typeVal);
          if (typeof term.value[2] !== 'undefined' && 'equal' in term.value[2] && !term.value[2].equal(type)) error.tc_mismatch(term.value[2], type);
          if (term.value.length === 1) term.value.push([]) //?
          let match = ctx.lookup(term.value[0], 'ctor', type.value[0]);
          if (match.cdef.length - 1 > term.value[1].length) error.tc_dcon_arg_len(term.value[1].length, match.cdef.length - 1);
          if (match.cdef.length - 1 < term.value[1].length)
            return check(ctx, term.value[1].slice(match.cdef.length - 1).reduce((acc, tm) => new Term({app: [acc, ...tm.value]}),
              new Term({dcon: [term.value[0], term.value[1].slice(0, match.cdef.length - 1)].concat([term.value[2]].filter(x => x))})), typeVal, index);
          let items = substTele(ctx, match.ddef, type.value[1], match.cdef);
          return tcArgTele(ctx, term.value[1], new Tele(...items.slice(0, -1)))
            .then(args => ({ term: new Term({dcon: [ term.value[0], args, typeVal ]}), type: typeVal }))

          case 'case': return infer(innerArgs = {ctx, term: term.value[0], index})
            .then(type => {
              term.value[0] = innerArgs.term;
              let typeTerm = quote(type);
              if (typeTerm.ctor !== 'tcon' && typeTerm.ctor !== 'app') error.tc_mismatch(typeTerm, 'Type Constructor');
              return term.value[1].reduce((p, match) => p.then(acc => {
                let [decls1, evars] = declarePat(ctx, match.value[0], false, typeTerm),
                    decls2 = equateWithPat(ctx, term.value[0], match.value[0], typeTerm);
                return check(ctx.cons(decls1.concat(decls2)), match.value[1], type, index)
                  .then(({term}) => acc.concat([new Match({match: [match.value[0], term]})]))
              }), Promise.resolve([]))
                .then(matches => exhaustivityCheck(ctx, term.value[0], typeTerm, term.value[1].map(x => x.value[0]))
                  .then(() => ({term: new Term({case: [term.value[0], matches, typeVal]}), type: typeVal})))
            })

          default: return infer(innerArgs = {ctx, term, index})
            .then(type => {
              let res = quote(type), ty = quote(typeVal);
              if (!res.equal(ty)) error.tc_mismatch(res, ty);
              else return {term: innerArgs.term, type: typeVal}
            })
        }
      })
    }

    // Terms
    function subst (term1, term2, ep, index = 0) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ subst(term1, term2.value[0], ep, index), subst(term1, term2.value[1], ep, index) ]})
        case 'pi': return new Term({pi: [ subst(term1, term2.value[0], ep, index), subst(term1, term2.value[1], ep, index + 1), term2.value[2] ]})
        case 'lam': return new Term({lam: [ subst(term1, term2.value[0], ep, index + 1), term2.value[1] ]})
        case 'app': return new Term({app: [ subst(term1, term2.value[0], ep, index), subst(term1, term2.value[1], ep, index), term2.value[2] ]})
        case 'boundvar': return index !== term2.value[0] ? term2 : !ep ? term1 : error.tc_erased_var_subst()
        case 'tcon': return new Term({tcon: [ term2.value[0], term2.value[1].map(tm => subst(term1, tm, ep, index)) ]})
        case 'dcon': return new Term({dcon: [ term2.value[0],
          term2.value[1].map(arg => new Arg({arg: [ subst(term1, arg.value[0], ep, index), arg.value[1]]})) ].concat([term2.value[2]].filter(x => x))})
        case 'case': return new Term({case: [ subst(term1, term2.value[0], ep, index),
          term2.value[1].map(match => new Match({match: [ match.value[0], subst(term1, match.value[1], ep, index) ]})) ].concat([term2.value[2]].filter(x => x))})
        case 'star': case 'freevar': return term2
      }
    }
    function unsubst (term1, term2, index = 0) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ unsubst(term1, term2.value[0], index), unsubst(term1, term2.value[1], index) ]})
        case 'pi': return new Term({pi: [ unsubst(term1, term2.value[0], index), unsubst(term1, term2.value[1], index + 1), term2.value[2] ]})
        case 'lam': return new Term({lam: [ unsubst(term1, term2.value[0], index + 1), term2.value[1] ]})
        case 'app': return new Term({app: [ unsubst(term1, term2.value[0], index), unsubst(term1, term2.value[1], index), term2.value[2] ]})
        case 'freevar': return term2.value[0].ctor === 'local' && index === term2.value[0].value[0] ? term1 : term2
        case 'tcon': return new Term({tcon: [ term2.value[0], term2.value[1].map(tm => unsubst(term1, tm, index)) ]})
        case 'dcon': return new Term({dcon: [ term2.value[0],
          term2.value[1].map(arg => new Arg({arg: [ unsubst(term1, arg.value[0], index), arg.value[1]]})) ].concat([term2.value[2]].filter(x => x))})
        case 'case': return new Term({case: [ unsubst(term1, term2.value[0], index),
          term2.value[1].map(match => new Match({match: [ match.value[0], unsubst(term1, match.value[1], index) ]})) ].concat([term2.value[2]].filter(x => x))})
        case 'star': case 'boundvar': return term2
      }
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
        case 'tcon': return new Value({vneutral: [ new Neutral({ntcon: [ term.value[0], term.value[1].map(tm => evaluate(tm, ctx)) ]}) ]})
        case 'dcon': return new Value({vneutral: [ new Neutral({ndcon: [ term.value[0],
          term.value[1].map(arg => new Arg({arg: [ evaluate(arg.value[0], ctx), arg.value[1] ]})) ].concat([term.value[2]].filter(x => x))}) ]})

        case 'case': // reduce to one branch
        // console.log('eval case', ctx.decls.slice(), term, quote(evaluate(term.value[0], ctx)))
        let match = term.value[1].find(match => quote(evaluate(term.value[0], ctx)).value[0].equal(match.value[0].value[0]));
        // console.log('eval match', equateWithPat(ctx, quote(evaluate(term.value[0], ctx)), match.value[0], quote(term.value[2])))
        return evaluate(match.value[1], ctx.cons(equateWithPat(ctx, quote(evaluate(term.value[0], ctx)), match.value[0], quote(term.value[2]))))
      }
    }

    // Values
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
        case 'ntcon': return new Term({tcon: [ neutral.value[0], neutral.value[1].map(v => quote(v, index)) ]})
        case 'ndcon': return new Term({dcon: [ neutral.value[0],
          neutral.value[1].map(arg => new Arg({arg: [ quote(arg.value[0], index), arg.value[1] ]})) ].concat([neutral.value[2]].filter(x => x))})
        case 'napp': return new Term({app: [ nquote(neutral.value[0], index), quote(neutral.value[1], index), neutral.value[2] ]})
      }
    }

    // Telescopes
    function tcTele (ctx, tele) {
      return tele.items.reduce((p, item) => p.then(acc => {
        switch (item.ctor) {
          case 'term': case 'erased':
          let [name, type] = item.value;
          return check(ctx, type, new Value({vstar: []}))
            .then(({term}) => ctx.extend(new Decl({sig: [ name, type = evaluate(term, ctx) ]})))
            .then(() => acc.concat([new Item({[item.ctor]: [ new Term({freevar: [name]}), type ]})]))

          case 'constraint':
          return infer({ctx, term: item.value[0]})
            .then(type => check(ctx, item.value[1]), type)
            .then(({term}) => constraintToDecls(ctx, item.value[0], item.value[1] = term))
            .then(decls => decls.forEach(decl => ctx.extend(decl)))
            .then(() => acc.concat([item]))
        }
      }), Promise.resolve([])).then(items => new Tele(...items))
    }

    function constraintToDecls (ctx, term1, term2) {
      let decls = [];
      if (term1.equal(term2)) return decls;
      if (term1.ctor === 'app' && term2.ctor === 'app') decls = decls
        .concat(constraintToDecls(ctx, term1.value[0], term2.value[0]))
        .concat(constraintToDecls(ctx, term1.value[1], term2.value[1]));
      else if (term1.ctor === 'freevar') return [ new Decl({def: [term1.value[0], term2]}) ];
      else if (term2.ctor === 'freevar') return [ new Decl({def: [term2.value[0], term1]}) ];
      else error.tc_constraint_cannot_eq()
    }

    function tcArgTele (ctx, args, tele) {
      let rightItems = tele.items.slice(), runtimeArgs = [],
          loop = i => {
            if (rightItems.length === 0) return Promise.resolve();
            let item = rightItems[0], arg = args[i];
            if (['erased', 'term'][arg.value[1]] === item.ctor) throw error.tc_erasure_mismatch();
            switch (item.ctor) {
              case 'term': return check(ctx, arg.value[0], item.value[1]).then(({term}) => {
                arg.value[0] = term;
                rightItems = doSubst(ctx, [[rightItems.shift().value[0], arg.value[0]]], new Tele(...rightItems));
                runtimeArgs.push(arg)
                return loop(i + 1)
              })

              case 'erased': rightItems.splice(0, 1);
              return loop(i)

              case 'constraint':
              if (item.value[0].equal(item.value[1])) return loop(i + 1);
              error.tc_mismatch(...item.value)
            }
          };
      return loop(0).then(() => runtimeArgs)
    }

    function doSubst (ctx, nameTerms, tele) {
      return tele.items.map(item => {
        let ep = true;
        switch (item.ctor) {
          case 'term': ep = false; case 'erased':
          let type = nameTerms.reduce((acc, [name, term]) => substFV(term, acc, name), quote(item.value[1]));
          return new Item({[item.ctor]: [item.value[0], evaluate(type, ctx)]})

          case 'constraint':
          let substItems = item.map(side => nameTerms.reduce((acc, [name, term]) => substFV(term, acc, name), side));
          constraintToDecls(ctx, ...substItem.value).forEach(decl => ctx.extend(decl));
          return new Item({constraint: substItems})
        }
      })
    }

    function substFV (term1, term2, name) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ substFV(term1, term2.value[0], name), substFV(term1, term2.value[1], name) ]})
        case 'pi': return new Term({pi: [ substFV(term1, term2.value[0], name), substFV(term1, term2.value[1], name), term2.value[2] ]})
        case 'lam': return new Term({lam: [ substFV(term1, term2.value[0], name), term2.value[1] ]})
        case 'app': return new Term({app: [ substFV(term1, term2.value[0], name), substFV(term1, term2.value[1], name), term2.value[2] ]})
        case 'freevar': return name.equal(term2) ? term1 : term2
        case 'tcon': return new Term({tcon: [ term2.value[0], term2.value[1].map(tm => substFV(term1, tm, name)) ]})
        case 'dcon': return new Term({dcon: [ term2.value[0],
          term2.value[1].map(arg => new Arg({arg: [ substFV(term1, arg.value[0], name), arg.value[1]]})) ].concat([term2.value[2]].filter(x => x))})
        case 'case': return new Term({case: [ substFV(term1, term2.value[0], name),
          term2.value[1].map(match => new Match({match: [ match.value[0], substFV(term1, match.value[1], name) ]})) ]})
        case 'star': case 'boundvar': return term2
      }
    }

    function substTele (ctx, tele1, terms, tele2) {
      return doSubst(ctx, tele1.items.map((item, i) => {
        switch (item.ctor) {
          case 'term': return [item.value[0], terms[i]];
          default: error.internal_arg('substTele')
        }
      }), tele2)
    }

    // Pattern matching
    // TODO: case splitting
    function declarePat (ctx, pat, ep, type) { // adds bindings to the ctx recursively for each patvar in the pattern
      switch (pat.ctor) {
        case 'patvar':
        let name = pat.value[0];
        return [[new Decl({sig: [name, type]})], ep ? [name] : []]

        case 'patdcon':
        if (ep) error.tc_erased_pat();
        let itemsi = [], typei = type;
        while (typei.ctor === 'app') {
          itemsi.unshift(typei.value[1]);
          typei = typei.value[0]
        }
        let result = ctx.lookup(pat.value[0], 'ctor', typei.value[0]),
            items = substTele(ctx, result.ddef, typei.value[1].concat(itemsi), result.cdef);
        return declarePats(ctx, ...pat.value, items.slice(0, -1))
      }
    }
    function declarePats (ctx, name, patArgs, items) {
      let rightItems = items, decls = [], decls1, names = [], names1, i = 0;
      while (
        (i !== patArgs.length && !rightItems.length && error.tc_pat_dcon_len(false)) ||
        (i === patArgs.length && rightItems.length && error.tc_pat_dcon_len(true)) ||
        i !== patArgs.length || rightItems.length
      ) {
        let ep = true, pat = patArgs[i].value[0];
        switch (rightItems[0].ctor) {
          case 'term': ep = false; case 'erased':
          [decls1, names1] = declarePat(ctx, pat, ep, rightItems[0].value[1]);
          let term = quotePat(ctx, pat, quote(rightItems[0].value[1]));
          rightItems = doSubst(ctx, [[rightItems.shift().value[0], term]], new Tele(...rightItems));
          decls = decls.concat(decls1);
          names = names.concat(names1);
          i++; break;

          case 'constraint':
          decls1 = constraintToDecls(ctx, rightItems.shift());
          ctx.extend(decls1);
          decls = decls.concat(decls1)
        }
      }
      return [decls, names]
    }
    function quotePat (ctx, pat, type) {
      if (pat.ctor === 'patvar') return new Term({freevar: [pat.value[0]]});
      else if (pat.ctor === 'patdcon' && type.ctor !== 'tcon' && type.ctor !== 'app') error.internal_arg('quotePat');
      let itemsi = [], typei = type;
      while (typei.ctor === 'app') {
        itemsi.unshift(typei.value[1]);
        typei = typei.value[0]
      }
      let result = ctx.lookup(pat.value[0], 'ctor', typei.value[0]),
          items = substTele(ctx, result.ddef, typei.value[1].concat(itemsi), result.cdef),
          rightItems = items.slice(0, -1), args = [], i = 0;
      while (
        (!(rightItems.length ^ (i === pat.value[1].length)) && error.tc_pat_len(pat.value[0])) ||
        rightItems.length
      ) {
        let ep = true;
        switch (rightItems[0].ctor) {
          case 'term': ep = false; case 'erased':
          let t = quotePat(ctx, pat.value[1][i].value[0], quote(rightItems.shift().value[1]));
          args.push(new Arg({arg: [t, ep]}));
          i++; break;

          case 'constraint':
          rightItems.splice(0, 1);
          ctx.extend(constraintToDecls(ctx, ...type.value)) //???
        }
      }
      return new Term({dcon: [pat.value[0], args, type]})
    }

    function equateWithPat (ctx, term, pat, type) {
      switch (term.ctor) {
        case 'freevar': return [new Decl({def: [ term.value[0], quotePat(ctx, pat, type) ]})]

        case 'dcon':
        if (!term.value[0].equal(pat.value[0])) return [];//error.tc_pat_cannot_omit(pat.value[0]);
        let itemsi = [], typei = type; // move into a helper
        while (typei.ctor === 'app') {
          itemsi.unshift(typei.value[1]);
          typei = typei.value[0]
        }
        let result = ctx.lookup(term.value[0], 'ctor', typei.value[0]),
            items = substTele(ctx, result.ddef, typei.value[1].concat(itemsi), result.cdef),
            rightItems = items.slice(0, -1), decls = [], i = 0;
        for (; rightItems.length; i++) {
          let thisItem = rightItems.shift();
          switch (thisItem.ctor) {
            case 'term': case 'erased':
            decls = decls.concat(equateWithPat(ctx, term.value[1][i].value[0], pat.value[1][i].value[0], quote(thisItem.value[1])));
            rightItems.forEach(item => item.value[0] = substFV(thisItem.value[0], item.value[0], term.value[1][i].value[0]));
            break;

            case 'contraint':
            ctx.extend(constraintToDecls(ctx, ...items[i].value));
          }
        }
        return decls

        default: return []
      }
    }

    function exhaustivityCheck (ctx, term, type, pats) {
      function checkImpossible (cdefs) {
        return cdefs.reduce((p, cdef) => p.then(acc =>
          tcTele(ctx, new Tele(...substTele(ctx, result.ddef, type, cdef.value[1])))
            .then(() => [cdef.value[0]])
            .catch(() => [])
            .then(res => acc.concat(res))
        ), Promise.resolve([]))
      }
      function removeDcon (name, cdefs) {
        for (let i = 0; i < cdefs.length; i++) if (name.equal(cdefs[i].value[0]))
          return [cdefs[i], cdefs.slice(0, i).concat(cdefs.slice(i + 1))];
        error.internal_cant_find(name)
      }
      function relatedPats (name, pats) {
        let argss = [], pats1 = []
        for (let i = 0; i < pats.length; i++) switch (pats[i].ctor) {
          case 'patdcon':
          if (name === pats[i].value[0]) args.push(pats[i].value[1]);
          else pats1.push(pats[i]);
          break;

          case 'patvar':
          argss = [];
          pats1.push(pats[i])
        }
        return [argss, pats1]
      }
      function checkSubPats (name, items, argss) { // All subpatterns must be PatVars
        let patss = argss;
        items.forEach((item, i) => {
          switch (item.ctor) {
            case 'term': case 'erased':
            if (patss.length !== 0 && patss.every(args => pats.length !== 0)) {
              let {hds, tls} = patss.reduce((acc, args) => {
                    acc.hds.push(patss[0][0].value[0]);
                    acc.tls.push(patss.slice(1));
                    return acc
                  }, {hds: [], tls: []});
              if (hds.length === 1 && hds[0].ctor === 'patvar') patss = tls;
              else error.tc_subpat_cannot_dcon()
            } else error.internal('checkSubPats')
          }
        })
      }
      if (pats.length > 0 && pats[0].ctor === 'patvar') return;
      if (type.ctor !== 'tcon') error.tc_mismatch(type, 'Type Constructor');
      let result = ctx.lookup(type.value[0], 'data');
      if (result.cdef === null) error.tc_dcon_cannot_infer();
      (function loop (ps, dcons) {
        if (ps.length === 0) {
          if (dcons.length === 0) return;
          else return checkImpossible(dcons)
            .then(l => l.length === 0 || error.tc_missing_cases(l))
        } else ps.forEach((pat, i) => {
          switch (pat.ctor) {
            case 'patvar': return;
            case 'patdcon':
            let [cd, dcons1] = removeDcon(pat.value[0], dcons);
            let items = substTele(ctx, result.ddef, type, cd.value[1]),
                [argss, pats1] = relatedPats(pat.value[0], ps.slice(i + 1));
            checkSubPats(pat.value[0], items.slice(0, -1), [pat.value[1], ...argss]);
            return loop(pats1, dcons1)
          }
        })
      })(pats, result.cdef);
      return Promise.resolve()
    }

    // Main typecheck
    return decls.reduce((p, decl) => p.then(acc => {
      console.log(decl.toString());
      let [name, info, ctors] = decl.value, mbValue, value;
      switch (decl.ctor) {
        case 'sig':
        let typeVal = new Value({vstar: []});
        mbValue = context.lookup(name, 'sig');
        if (typeof mbValue !== 'undefined') {
          if (info.equal(quote(mbValue))) return acc.concat([{declName: 'sig', type: typeVal, value: mbValue, term: info}]);
          else error.duplicate(name);
        } else return check(context, info, typeVal).then(({term, type}) => {
          let value = evaluate(term, context);
          context.extend(new Decl({sig: [ name, value ]}));
          return acc.concat([{declName: 'sig', type, value, term: info}])
        })

        case 'def':
        mbValue = context.lookup(name, 'def');
        if (typeof mbValue !== 'undefined') {
          if (info.equal(quote(mbValue))) return acc.concat([{declName: 'def', type: context.lookup(name, 'sig'), value: mbValue, term: info}]);
          else error.duplicate(name)
        } else {
          let mbType = context.lookup(name, 'sig'), args;
          return (typeof mbType === 'undefined') ?
            infer(args = {ctx: context, term: info}).then(type => {
              value = evaluate(args.term, context);
              context.extend(new Decl(({sig: [name, type]}))).extend(new Decl({def: [name, value]}));
              return acc.concat([{declName: 'def', type, value, term: args.term}])
            }) :
            check(context, info, mbType).then(({term, type}) => {
              value = evaluate(term, context);
              context.extend(new Decl({def: [name, value]}));
              return acc.concat([{declName: 'def', type, value, term}])
            })
        }

        case 'data':
        return tcTele(new Context(context), info).then(tele =>
          ctors.reduce((p, ctor) => p.then(acc =>
            tcTele(context.cons(new Decl({datasig: [name, tele]})).concatTele(tele), ctor.value[1])
              .then(ctorTele => acc.concat([new Ctor({ctor: [ctor.value[0], ctorTele]})]))
          ), Promise.resolve([])).then(ctors => {
            let decl = new Decl({data: [name, tele, ctors]});
            context.extend(decl);
            return [{declName: 'data', params: tele.tail(), type: tele.items.slice(-1), ctors}]
          })
        )

        case 'recdef': case 'datasig': error.tc_internal()
      }
    }), Promise.resolve([]))
  }




  // API

  const R = { Data, Sig, Def, context },
        sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  Object.defineProperty(R, 'ready', { get () { return sequence(() => new Promise(r => setTimeout(r, 0))) } });

  return R
};




// Testing

const R = Reason({showDebug: false});

let id1, id2, Void, Unit, Nat_, Vec_, Fin_, Sigma_;
let id3, plus, one_plus_one, half, tail;
let Id_, cong, Leq_;

(async () => {
  let passFail = obj => {
    for (let test in obj) try { console.log(obj[test]()) }
      catch (e) { console.log(test, e) }
  }

  // // functions, lambdas
  // id1 = new R
  //   .Sig('id', '(T : Type) -> T -> T')
  //   .Def('(t, x => x)');
  //
  // // functions with builtins
  // id2 = new R.Def("id'", '({t}, x => x) : {T : Type} -> T -> T',
  //   { toString () { return this[0].toString() },
  //   valueOf () { return this[0].valueOf() } }
  // );
  //
  // // types
  // Void = new R.Data('Void', 'Type', []);
  // Unit = new R.Data(
  //   'Unit', 'Type', ['TT : Unit'],
  //   { fromJS: () => Unit().tt() }
  // );

  Nat_ = new R.Data(
    "Nat'", 'Type',
    [ "Z : Nat'",
      "S : (n:Nat') -> Nat'" ]
  );

  // List_ = new R.Data("List'", "(A:Type):Type", [ "Nil:List' A", "Cons:(x:A)(xs:List' A)->List' A" ]);
  // Vec_ = new R.Data(
  //   "Vec'", "(A : Type) : Nat' -> Type",
  //   [ "Nil : Vec' A Z",
  //     "Cons : {n : Nat'}(x : A)(xs : Vec' A n) -> Vec' A (S n)" ]
  // );
  //
  // Fin_ = new R.Data(
  //   "Fin'", "(n:Nat') : Type",
  //   [ "Zero:{n:Nat'}->Fin'(S n)",
  //     "Succ:{n:Nat'}(i:Fin' n)->Fin'(S n)" ]
  // );
  //
  // Sigma_ = new R.Data(
  //   "Sigma'", "(A:Type)(B:A->Type):Type",
  //   [ "DProd:(x:A)(y:B x)->Sigma' A B" ]
  // )

  // pattern matching
  plus = new R
    .Sig("plus", "Nat' -> Nat' -> Nat'")
    // .Def([
    //   "@ Z n := n",
    //   "@ (S m) n := S (plus m n)"
    // ])
    .Def({
      "x y | x":
      [ "Z   := y",
        "S m := S (plus m y)" ]
    });

  one_plus_one = new R.Sig(
    "one_plus_one", "Nat'"
  ).Def(
    "plus (S Z) (S Z)"
  );
  // half = new R.Sig(
  //   "half", "Nat' -> Nat'"
  // ).Def({
  //   "x | x":
  //   [ "Z       := Z",
  //     "S  Z    := Z",
  //     "S (S m) := S (half m)" ]
  // })
  //
  // tail = new R.Sig(
  //   "tail", "{A : Type}{m : Nat'} -> Vec' A (S m) -> Vec' A m"
  // ).Def({
  //   "{A} {m} v | v":
  //   [ "Cons {m} y ys := ys" ]
  // })

  // id3 = new R // Cannot pattern match because x could be a function
  //   .Sig("id''", "(T : Type) -> T -> T")
  //   // .Def(["@ x := x"]);
  //   .Def({"t x | x": [ "n := n" ]});

  // // proof example
  // Id_ = new R.Data(
  //   "Id'", "{A : Type}(x : A) : A -> Type",
  //   [ "Refl : {x : A} -> Id' x x" ]
  // )
  // cong = new R
  //   .Sig("cong", "{a b : Type}{x, y : a} -> (f : a -> b) -> Id' x y -> Id' (f x) (f y)")
  //   .Def("@ f Refl := Refl")

  // Leq_ = new R.Data(
  //   "Leq'", "Nat' -> Nat' -> Type",
  //   [ "lz : (n : Nat') -> Leq' (Z) n", // TODO: all right identifiers parse as arguments, including tnames and dnames
  //     "ls : (m n : Nat') (p : Leq' m n) -> Leq' (S m) (S n)" ]
  // )
})()
