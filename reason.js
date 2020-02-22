var Reason = (options = {}) => {
  let { debug = {} } = options;

  // Errors and logging

  const error = new Proxy({
          append (e1, which, ...args) { try { error[which](...args) } catch (e2) { throw new Error(e1.message + '\n' + e2.message) } }
        }, { get (o, prop) {
          if (prop in o) return o[prop];
          else return (...args) => { throw new Error((({
            // Interpreter errors
            duplicate: n => `Interpreter error: ${n} already exists`,
            mixfix_overlap: (tested, given) => `Interpreter error: ${tested} overlaps syntax with ${given}`,
            nosig: n => `Interpreter error: no signature has been declared for ${n}`,
            notfound: n => `Interpreter error: declaration for ${n} cannot be found`,
            unchecked: () => 'Interpreter error: not yet typechecked',
            malf: which => `Interpreter error: malformed ${which}`,
            bad_id_name: (role, name) => `Interpreter error: bad ${role} name in ${name}`,

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
            parser_notid: (token, index) => `Parser error: ${token} not an identifier at position ${index}`,
            parser_notvalid: which => `Parser error: not a valid ${which}`,
            parser_mixfix_miss_id: (which, unapp) => `Parser error: missing identifiers ${unapp} of mixfix operator ${which}`,
            parser_mixfix_bad: (which, mf) => `Parser error: unexpected identifier ${which} in mixfix ${mf}`,

            // Pretty printer errors
            print_value: quoted => `Print error: warning - tried to print a Value (quoted: ${quoted})`,
            print_bad: val => `Print error: unprintable argument ${val}`,

            // Typechecking errors
            tc_mismatch: (tested, given, term) => `Type error: mismatch at\n    ${print(tested)}\nexpecting\n    ${print(given)}${
              term ? `\nat term\n    ${print(term)}` : ''}`,
            tc_cannot_infer: which => `Type error: cannot infer type of ${which}`,
            tc_lam_mismatch: ctor => `Type error: lambda has Pi type, not ${ctor}`,
            tc_ann_mismatch: tested => `Type error: annotation should have type Type, found ${print(tested)}`,
            tc_pi_mismatch: (loc, tested) => `Type error: Pi ${loc} should have type Type, found ${print(tested)}`,
            tc_app_mismatch: tested => `Type error: illegal application - expected type Pi, found ${print(tested)}`,
            tc_bad_app: () => 'Type error: bad value application',
            tc_unknown_id: name => `Type error: unknown identifier ${name[0]}`,
            tc_dcon_ambiguity: () => 'Type error: ambiguous data constructor',
            tc_dcon_cannot_infer_params: () => 'Type error: cannot infer data constructor parameters. Try adding an annotation.',
            tc_dcon_arg_len: (mlen, tlen) => `Type error: data constructor given wrong number of arguments - (${mlen} instead of ${tlen})`,
            tc_mismatch_con: which => `Type error: ${which} constructor given, but expected ${which === 'type' ? 'data' : 'type'} constructor`,
            tc_term_not_found: (ctor, type) => `Type error: constructor ${ctor} not found${type ? ` for type ${type}` : ''}`,

            tc_erased_var_subst: () => 'Type error: erased variable used in lambda',
            tc_erasure_mismatch: () => 'Type error: erasure mismatch',
            tc_constraint_cannot_eq: (lhs, rhs) => `Cannot equate lhs and rhs of constraint ${print(lhs)} = ${print(rhs)}`,

            tc_erased_pat: () => 'Type error: cannot pattern match erased arguments',
            tc_pat_dcon_len: dir => `Type error: ${dir ? 'too many' : 'not enough'} patterns in match for data constructor`,
            tc_pat_len: name => `Type error: wrong number of args to pattern ${name}`,
            tc_pat_cannot_omit: name => `Type error: case for ${print(name)} cannot be omitted (yet)`,
            tc_dcon_cannot_infer: () => 'Type error: cannot infer data constructor',
            tc_missing_cases: l => `Type error: missing cases for ${l.map(x => print(x)).join(', ')}`,
            tc_subpat_cannot_dcon: () => 'Type error: cannot use data constructor in subpattern (yet)',

            tc_internal: msg => 'Type error: internal construct' + msg ? '\n  ' + msg : '',

            // Internal error
            internal: fname => `Internal error: at function ${fname}`,
            internal_arg: fname => `Internal error: internal function ${fname} given illegal arguments`,
            internal_cant_find: cname => `Internal error: can't find ${cname}`
          })[prop] || (() => prop))(...args)) }
        } }),
        Alt = Object.assign(class {
          constructor (fn) {
            let thrown = false, value, newThis = this,
                error = v => (thrown = true, v),
                join = v => newThis = Alt.prototype.isPrototypeOf(v) ? v : newThis;
            Object.assign(this, {
              left (fn) {
                if (!thrown) return this;
                thrown = false;
                join(value = fn(value, error));
                return newThis },
              right (fn) {
                if (thrown) return this;
                join(value = fn(value, error));
                return newThis },
              map (fn) {
                if (!thrown) value = value.map(v => join(fn(v, error)));
                return newThis } });
            return fn(
              v => {
                join(value = v);
                return newThis },
              e => {
                thrown = true;
                join(value = e);
                return newThis } )
          }
        }, {
          pure: v => new Alt(r => r(v)),
          throw: e => new Alt((_, l) => l(e))
        }),
        log = (...args) => console.log(...[].concat(...args.map(e => ['\n  - ', e])).slice(1)); // TODO expand logging

  let active = [];
  function wait (declType, name) {
    let match;
    if (~active.findIndex(([d, n]) => d === declType && n === name )) error.duplicate(name);
    else if (typeof name === 'string' && ((~(match = findMixfix(name, active.map(x => x[1])))[1] && active[match[0]][0] === declType) ||
      (match = active.find(x => ~findMixfix(name, [x[1]])[1] && x[0] === declType)))) error.mixfix_overlap(name, active[match[0]][1]);
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

  class Data {
    constructor (nameString, ddef, cdefs, builtins = {}) {
      let nameFix = str => str.match(/^(([a-zA-Z][a-zA-Z0-9]*[\']*)\s.*)|(_?(?:[a-zA-Z0-9':!$%&*+.,/<=>\?@\\^|\-~\[\]]+(?:_[a-zA-Z0-9:!$%&*+.,/<=>\?@\\^|\-~\[\]]+)*)_?)(?:\s+((?:l|r)[\d]{1,3}))?$/).slice(1).filter(Boolean);
      let [name, aux] = nameFix(nameString).filter(Boolean);
      name = name || fixName;
      wait('data', name);
      let readyDecl = false, ctorNames = cdefs.map(cdef => typeof cdef === 'string' ? [...nameFix(cdef), {}] :
            Object.entries(cdef)[0].flatMap((x, i) => i ? x : nameFix(x))),
          { fromJS = () => {}, ...dBuiltins } = builtins, fromJSThis = {}, root,
          jsTerm = ctorNames.reduce((a, x) => Object.assign(a, { [x[0].match(/\w+/) ? x[0].toLowerCase() : x[0]]: () => error.unchecked() }),
            { appliedTerms: [], ...dBuiltins });
      // Data(name, tcon, [dcons], {...builtins})
      // Data(name, tcon, [{dcons}], {...builtins})
      sequence(() => cdefs.reduce(
        (p, cdef, i) => p.then(acc => tokenise({sourceString: ctorNames[i][0]})
          .then(lex => parse(lex, 'cdef', {fixity: ctorNames[i][1]}))
          .then(res => (acc[0][2].push(res[0]), acc))),
        tokenise({name, sourceString: ddef}).then(lex => parse(lex, 'ddef', {fixity: aux})))
        .then(decls => typecheck(decls, context))
        .then(res => {
          let [{declName, term, type, params, ctors}] = res;
          root = res[0];
          if (declName === 'data') {
            Object.assign(jsTerm, { term, type });
            if (term) Object.assign(jsTerm, { term, print: print(term) })
          }
          readyDecl = true;
          unwait('data', name)
        }));
      let curry = function (outerTy, typeArgs) {
        if (readyDecl) {
          let { term, type, params } = root, jsTyTerm = { appliedTerms: typeArgs, type };
          if (term) Object.assign(jsTyTerm, { term, print: print(term) });
          ctorNames.forEach(([_, ctorName, cBuiltins]) => {
            let lcname = ctorName.toLowerCase(), ctor;
            jsTyTerm[lcname] = fromJSThis[lcname] = ctor = Object.assign((...termArgs) => {
              // Initialise a term of the given type
              // check if indexed type -> appliedTerm for each param -> if not, throw error
              let term = new Term({dcon: [ new Name({global: [ctorName]}), termArgs.map(tm =>
                    new Arg({arg: [tm.term, false]})) ]}),
                  type = context.lookup(term[0], 'ctor')[0].cdef.items[0][1].quote(),
                  fresh = parser.fresh(), jsCtTerm = { term, type, appliedTerms: [], print: print(term), result: quote(evaluate(term, context)) };
              if (termArgs.length) {
                // Initialise a term, with arguments
                wait('data', fresh);
                jsCtTerm.appliedTerms = termArgs;
                sequence(() => typecheck([
                  new Decl({sig: [ new Name({global: [fresh]}), jsTyTerm.term ]}),
                  new Decl({def: [ new Name({global: [fresh]}), term ]})
                ])).then(res => {
                  let { term, type } = res.find(decl => decl.declName === 'def');
                  Object.assign(jsCtTerm, { term, type, print: print(term) });
                  unwait('data', fresh);
                })
              };
              jsCtTerm = Object.assign(() => jsCtTerm, Object.assign({ toString: () => `<${ctorName}>` }, Object.entries(cBuiltins)
                .reduce((a, [fname, fn]) => Object.assign(a, { [fname]: fn.bind(jsCtTerm.appliedTerms) }), jsCtTerm))); // Naming conflicts?
              Object.defineProperty(jsCtTerm, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))).then(() => jsCtTerm) } });
              return jsCtTerm
            }, cBuiltins)
          });
          // Initialise a type
          if (typeArgs.length) {
            // Initialise a type, with parameters
            params.forEach((param, i) => fromJSThis[(param[0][0][0] + '').toLowerCase()] = jsTyTerm.appliedTerms[i]);
            let fresh = parser.fresh();
            wait('data', fresh);
            sequence(() => typecheck([
              new Decl({sig: [ new Name({global: [fresh]}), type ]}),
              new Decl({def: [
                new Name({global: [fresh]}),
                new Term({tcon: [ new Name({global: [name]}), typeArgs.map(tm => tm.term) ]}) // TODO: if no term, raise error
              ]})
            ], context)).then(res => {
              // TODO: is typeArgs the same length as params?
              let { term, type } = res.find(decl => decl.declName === 'def');
              Object.assign(jsTyTerm, { term, type, print: print(term), result: quote(evaluate(term, context)) });
              unwait('data', fresh)
            })
          }
          jsTyTerm = Object.assign((...typeArgs) => curry(jsTyTerm, typeArgs), { ...jsTyTerm, toString: () => `<${name}>`, fromJS: fromJS.bind(fromJSThis) });
          Object.defineProperty(jsTyTerm, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))).then(() => jsTyTerm) } });
          return jsTyTerm
        } else error.unchecked()
      };
      jsTerm = Object.assign((...typeArgs) => curry(jsTerm, typeArgs), jsTerm);
      Object.defineProperty(jsTerm, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))).then(() => jsTerm) } });
      return jsTerm
    }
  }

  class Sig {
    constructor (nameString, declString) {
      // Sig(name || "name fixity", signature || sigdef)
      let [name, aux] = nameString.match(/^(([a-zA-Z][a-zA-Z0-9]*[\']*)\s.*)|(_?(?:[a-zA-Z0-9':!$%&*+.,/<=>\?@\\^|\-~\[\]]+(?:_[a-zA-Z0-9:!$%&*+.,/<=>\?@\\^|\-~\[\]]+)*)_?)(?:\s+((?:l|r)[\d]{1,3}))?$/).slice(1).filter(Boolean);
      wait('sig', name);
      let ready = false, jsTerm = {}, jsSig = { Def: (...args) => jsTerm = Object.assign(new Def(name, ...args), jsTerm) };
      Object.defineProperty(jsSig, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))).then(() => jsSig) } });
      sequence(() => tokenise({name, sourceString: declString})
        .then(lex => parse(lex, 'sig', {fixity: aux}))
        .then(decls => typecheck(decls, context))
        .then(res => {
          let [{declName, term, type}] = res;
          if (declName === 'sig') Object.assign(jsTerm, {type: term, print: print(term), result: quote(evaluate(term, context)) });
          ready = true;
          unwait('sig', name)
        }));
      return jsSig
    }
  }

  class Def { // TODO: pull builtins from Data definitions somehow
    constructor (nameString, declStrings, builtins = {}) {
      let [name, aux] = nameString.match(/^(([a-zA-Z][a-zA-Z0-9]*[\']*)\s.*)|(_?(?:[a-zA-Z0-9':!$%&*+.,/<=>\?@\\^|\-~\[\]]+(?:_[a-zA-Z0-9:!$%&*+.,/<=>\?@\\^|\-~\[\]]+)*)_?)(?:\s+((?:l|r)[\d]{1,3}))?$/).slice(1).filter(Boolean);
      wait('def', name);
      let ready = false, { toString, ...tBuiltins } = builtins, jsTerm = { ...tBuiltins, appliedTerms: [] };
      if (typeof declStrings === 'string') {
        // Def(name, sigdef, { ...builtins })
        sequence(() => tokenise({name, sourceString: declStrings})
          .then(lex => parse(lex, 'def'))
          .then(decls => typecheck(decls, context))
          .then(ress => {
            ress.forEach(res => {
              let { declName, term, type } = res, appliedTerms = [];
              if (declName === 'sig') Object.assign(jsTerm, {type: term});
              else if (declName === 'def') Object.assign(jsTerm, {term, type, appliedTerms, print: print(term), result: quote(evaluate(term, context)) })
            });
            ready = true;
            unwait('def', name)
          }));
      } else if (Array.prototype.isPrototypeOf(declStrings)) {
        // Def(name, [pats], { ...builtins })
        sequence(() => declStrings.reduce((p, lex) => p
          .then(acc => tokenise({name, sourceString: declString})
            .then(lex => parse(lex, 'pat'))
            .then(res => acc.concat([res]))), Promise.resolve([]))
          .then(decls => typecheck(decls, context))).then(ress => {
              ress.forEach(res => {
                let { declName, term, type } = res, appliedTerms = [];
                if (declName === 'sig') Object.assign(jsTerm, {type: term});
                else if (declName === 'def') Object.assign(jsTerm, {term, type, appliedTerms,
                  print: print(term), result: quote(evaluate(term, context)) })
              });
            jsTerm.pats = ress;
            ready = true;
            unwait('def', name)
          })
      } else {
        // Def(name, { case: [pats] }, { ...builtins })
        let e = Object.entries(declStrings);
        if (e.length !== 1) error.malf('definition');
        let [caseDef, pats] = e[0];
        sequence(() => tokenise({name, sourceString: caseDef})
          .then(lex => parse(lex, 'case'))
          .then(([bvs, toDecl]) => pats.reduce((p, pat) => p.then(acc => tokenise({sourceString: pat})
            .then(pat => parse(pat, 'pat', {casePat: true, bvs}))
            .then(res => acc.concat([res]))), Promise.resolve([]))
            .then(matches => [toDecl(matches.flat())]))
          .then(decls => typecheck(decls, context)).then(ress => {
            ress.forEach(res => {
              let { declName, term, type } = res, appliedTerms = [];
              if (declName === 'sig') Object.assign(jsTerm, {type: term});
              else if (declName === 'def') Object.assign(jsTerm, {term, type, appliedTerms, print: print(term), result: quote(evaluate(term, context)) })
            });
            ready = true;
            unwait('def', name)
          })
        )
      }
      let curry = function (outerFn, fnArgs) {
        if (ready) {
          let jsApTerm = { appliedTerms: outerFn.appliedTerms.concat(fnArgs) };
          if (fnArgs.length) {
            let term = jsApTerm.appliedTerms.reduce((a, arg) => new Term({app: [a, arg.term, false]}), new Term({freevar: [ new Name({global: [name]}) ]})),
                fresh = parser.fresh();
            Object.assign(jsApTerm, { term, print: print(term) });
            wait('data', fresh);
            sequence(() => typecheck([ new Decl({def: [ new Name({global: [fresh]}), term ]}) ])).then(ress => {
              ress.forEach(res => {
                let { declName, term, type } = res, result = quote(evaluate(term, context));
                jsApTerm = Object.assign(jsApTerm, { type, result })
              });
              unwait('data', fresh);
            })
          }
          jsApTerm = Object.assign((...args) => curry(jsApTerm, args), { ...jsApTerm, toString: () => `<${name}>` });
          Object.defineProperty(jsApTerm, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))).then(() => jsApTerm) } });
          return jsApTerm
        } else error.unchecked()
      };
      jsTerm = Object.assign((...args) => curry(jsTerm, args), { ...jsTerm, toString: () => `<${name}>` });
      Object.defineProperty(jsTerm, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))).then(() => jsTerm) } });
      return jsTerm
    }
  }




  // Lexer

  function findMixfix (id, list) {
    let lex = lexMixfix(id), lexop, index = -1;
    return [ list.findIndex(op => typeof op === 'string' &&
      ~(index = (lexop = lexMixfix(op)).findIndex((_, i) => lex.every((token, j) => token === lexop[i + j])))), index ]
  }
  function lexMixfix (str) {
    let result = str.match(/^(_)?([^_]+)?(.*)/);
    return result.slice(1, 3).filter(Boolean).concat(result[3] ? lexMixfix(result[3]) : [])
  }

  function tokenise ({name, sourceString}) {
    let rx_token = /^((\s+)|([a-zA-Z][a-zA-Z0-9]*[\']*|_(?:\s|[(){}"]|$))|(_?(?:[a-zA-Z0-9':!$%&*+.,/<=>\?@\\^|\-~\[\]]+(?:_[a-zA-Z0-9:!$%&*+.,/<=>\?@\\^|\-~\[\]]+)*)_?)|(0|-?[1-9][0-9]*)|([(){}"]))(.*)$/,
        rx_digits = /^([0-9]+)(.*)$/,
        rx_hexs = /^([0-9a-fA-F]+)(.*)$/,
        source = sourceString, tokens = name ? [{id: name, value: 'name'}] : [], index = 0, word, char;

    function alt (fn) {
      let rewind = index;
      return Alt.pure().right((v, err) => fn({
        add: token => tokens.push(token),
        next: match => {
          if (match && match !== char) return char ?
            err(['lexer_unexpected', char, match, index - 1]) :
            err(['lexer_missing', match, index - 1]);
          if (sourceString) {
            word += (char = source[0]);
            source = source.slice(1)
          }
          index++
        },
        back: () => {
          if (word) {
            source = (char = word.slice(-1)) + source;
            word = word.slice(0, -1);
            index--
          } else char = ''
        }
      }, err)).left((e, err) => {
        index = rewind;
        return err(e)
      })
    }

    function lex () {
      return alt((acc, err) => {
        function string () {
          word = '';
          return alt(() => function loop () {
            if (char === '"') {
              word = word.slice(0, -1)
              acc.add({id: char, value: 'string'})
            } else if (char === '') return err(['lexer_uncl_str', index]);
            else if (char === '\\') {
              acc.next('\\');
              if (char === '') return err(['lexer_uncl_str', index]);
              else if (char === '"') acc.next()
            }
            else acc.next();
            return loop()
          })
        }

        function num () {
          return alt((acc, err) => {
            function frack () {
              if (char === '.') {
                somedigits(rx_digits);
                acc.next()
              }
              if (char === 'E' || char === 'e') {
                acc.next();
                if (char !== '+' && char !== '-') acc.back()
                somedigits(rx_digits);
                acc.next()
              }
            }
            function somedigits (rx) {
              let result = source.match(rx);
              if (!result) return err(['lexer_digits', index]);
              char = result[1];
              index += char.length;
              source = result[2];
              word += char
            }
            if (word === '0') {
              acc.next();
              if (char === '.') frack();
              else if (char === 'x') {
                somedigits(rx_hexs);
                acc.next()
              }
            } else {
              acc.next();
              frack()
            }
            if (/[0-9a-zA-Z]/.test(char)) return err(['lexer_unexpected', char, null, index]);
            acc.back();
            return acc.add({id: word, value: 'num'})
          })
        }

        let result;
        if (!source) return acc.add({value: 'final'});
        result = source.match(rx_token);
        if (debug.lexer) log('lex', result);
        if (!result) return err(['lexer_unexpected', source[0], null, index]);
        word = result[1];
        index += word.length;
        source = result[7];

        if (result[3]) acc.add({id: word});
        else if (result[4]) acc.add({id: word, value: 'op'});
        else if (result[5]) return num().right(lex);
        else if (result[6]) {
          if (word === '"') return string().right(lex);
          else acc.add({id: word, value: 'punc'})
        }
        return lex()
      })
    }

    return new Promise(r => lex()
      .right(() => {
        debug.lexer && log('tokens', tokens);
        r(tokens)
      })
      .left(e => error[e.shift()](...e)))
  }




  // Syntax

  function AST (...ctors) {
    return class {
      constructor (arg) {
        let kv = Object.entries(arg);
        if (kv.length !== 1) error.internal_ctor_args();
        if (!~ctors.indexOf(kv[0][0])) error.internal_ctor_invalid(kv[0][0], ctors);
        this.ctor = kv[0][0];
        Object.defineProperties(this, kv[0][1].reduce((a, x, i) =>
          Object.assign(a, {[i]: {
            get () { return kv[0][1][i] },
            set (v) { return kv[0][1][i] = v }
          }}), {}
        ));
        this[Symbol.iterator] = () => kv[0][1].values();
        ['map', 'every'].forEach(prop => this[prop] = (...args) => kv[0][1][prop](...args))
      }
    }
  }

  class Term extends AST('ann', 'star', 'pi', 'lam', 'app', 'boundvar', 'freevar' ,'tcon', 'dcon', 'case') {
    equal (operand) {
      return this.ctor === operand.ctor &&
        this.every((x, i) => x === operand[i] ||
          ('equal' in x && x.equal(operand[i])) ||
          (Array.prototype.isPrototypeOf(x) && x.every((y, j) => y.equal(operand[i][j]))))
    }
    toString () {
      switch (this.ctor) {
        case 'ann': return `(${this[0].toString()} : ${this[1].toString()})`
        case 'star': return 'Type'
        case 'pi': return `${this[2] ? 'Erased ' : ''}Pi(${this[0].toString()}, ${this[1].toString()})`
        case 'lam': return `${this[1] ? 'Erased ' : ''}Lam(${this[0].toString()})`
        case 'app': return `${this[0].toString()} :@: ${this[1].toString()}` // Erased App?
        case 'boundvar': return `Bound ${this[0]}`
        case 'freevar': return `Free ${this[0]}`
        case 'tcon': return `TC:${this[0].toString()}${this[1].map(x => ` (${x.toString()})`).join('')}`
        case 'dcon': return `DC:${this[0].toString()}${this[1].map(x => ` (${x.toString()})`).join('')}`
        case 'case': return `Case ${this[0].toString()} |${this[1].map(x => `\n  ${x.toString()}`).join('')}`
      }
    }
    eval () { return evaluate(this) }
    print () { return print(this) }
  }

  class Name extends AST('global', 'local', 'quote') {
    equal (operand) {
      return this.ctor === operand.ctor && this[0] === operand[0]
    }
    toString () {
      switch(this.ctor) {
        case 'global': return typeof this[0] === 'number' ? '_' + this[0] : `Global <${this[0]}>`
        case 'local': return `Local ${this[0]}`
      } }
  }

  class Item extends AST('term', 'erased', 'constraint') { // TODO combine term and erased - (name, term, ep)
    equal (operand) { return this.ctor === operand.ctor && this.every((x, i) => x.equal(operand[i]))}
    toString () {
      switch(this.ctor) {
        case 'term': return `(${this[0].toString() + ':' + ('quote' in this[1] ? this[1].quote() : this[1]).toString()})`
        case 'erased': return `{${this[0].toString() + ':' + ('quote' in this[1] ? this[1].quote() : this[1]).toString()}}`
        case 'constraint': return `{${this.map(x => x.toString()).join('=')}}`
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

  class Decl extends AST('sig', 'def', 'data', 'datasig') { // is recdef being fully handled by eval case?
    toString () {
      switch (this.ctor) {
        case 'sig': return `SIG: ${this[0].toString()} : ${('quote' in this[1] ? this[1].quote() : this[1]).toString()}`
        case 'def': return `DEF: ${this[0].toString()} := ${('quote' in this[1] ? this[1].quote() : this[1]).toString()}`
        case 'data': return `DATA: ${this[0].toString()}${
          this[1].items.length - 1 ? ' ' + this[1].tail().toString() : ''} : ${this[1].items.slice(-1)[0].toString()}` +
          this[2].map(ctor => `\n  ${ctor.toString()}`).join('')
        case 'datasig': return `DATASIG: ${this[0].toString()} ${this[1].tail().toString()} : ${this[1].items.slice(-1)[0].toString()}`
      }
    }
  }
  class Ctor extends AST('ctor') {
    toString () { return `CTOR: ${this[0].toString()}${this[1].items.length - 1 ? ' ' + this[1].tail().toString() : ''} : ${this[1].items.slice(-1)[0].toString()}` }
  }

  class Value extends AST('vlam', 'vstar', 'vpi', 'vfree', 'vtcon', 'vdcon', 'vapp', 'vcase') {
    quote () { return quote(this) }
    print () { return print(quote(this)) }
    toString () { return 'VAL ' + quote(this).toString() }
  }

  class Arg extends AST('arg') { // Only dcons and patdcons have Args. TODO: ('runtime', 'erased')
    equal (operand) { return this[0].equal(operand[0]) && this[1] === operand[1] }
    toString () { return (this[1] ? 'Erased ' : '') + this[0].toString() }
  }

  class Pat extends AST('patdcon', 'patvar', 'patbvar') {
    toString () {
      switch (this.ctor) {
        case 'patdcon': return `${this[2] ? 'Inac ' : ''}PatDC:${this[0].toString()}${this[1].map(x => ` (${x.toString()})`).join('')}`
        case 'patvar': return `${this[1] ? 'Inac ' : ''}PatVar ${this[0].toString()}`
        case 'patbvar': return 'PatBVar ' + this[0]
      }
    }
  }
  class Match extends AST('clause', 'absurd') {
    toString () {
      switch (this.ctor) {
        case 'clause': return `PatMatch @ ${this[0].toString()} := ${this[1].toString()}`
        case 'absurd': return `Absurd @ ${this[0].toString()}`
      }
    }
  }




  // Parser

  let parser = new (class Parser {
    tnames = []
    dnames = []
    mixfixes = []
    fresh = (i => () => i++)(0)
    parse (tokens, sourceName, parseOptions = {}) {
      // log('@' + sourceName);
      // log('tokens', ...tokens);
      // log('fixity', parseOptions.fixity)

      function parserDebug (msg, res) {
        if (!debug.parser) return;
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
        msg && parserDebug(msg);
        if (match && (('id' in match && tokens[index].id !== match.id) || ('value' in match && tokens[index].value !== match.value)))
        error.parser_mismatch(token, index, match.id, match.value);
        token = next();
      }
      function assertId () { if (!('id' in token) || 'value' in token) error.parser_notid(token, index) }
      function assertOp () { if (!('id' in token && 'value' in token && token.value === 'op')) error.parser_mismatch(token, index) }

      function alt (fn) { // TODO: move the environment state into alt
        let rewind = index;
        return new Promise(r => r(fn())).catch(err => {
          index = rewind;
          throw err
        })
      }
      function altNames (fn) {
        let rewind = index, arg;
        return new Promise(r => r(fn(arg = {tnames: [], dnames: [], mixfixes: []}))).then(res => {
          parser.tnames = parser.tnames.concat(arg.tnames);
          parser.dnames = parser.dnames.concat(arg.dnames.filter(c => !~parser.dnames.indexOf(c)));
          parser.mixfixes = parser.mixfixes.concat(arg.mixfixes.filter(c => !~parser.mixfixes.findIndex(n => n[0] === c[0])));
          return res
        }).catch(err => {
          index = rewind;
          throw err
        })
      }
      function altMsg (msg, fn) {
        return alt(!debug.parser ? fn : () => {
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
            case 'sig': return altNames(arg => {
              // term
              advance('Signature?', {value: 'name'});
              let name = token.id;
              if (name.match(/_/)) arg.mixfixes.push([name, parseOptions.fixity]);
              return parseTerm([], 'pi')
                .then(result => endTest([new Decl({sig: [ new Name({global: [name]}), result ]})]))
                .catch(() => error.parser_notvalid('signature'))
            })

            case 'def': return altNames(arg => {
              // term : type
              advance('Signature with definition?', {value: 'name'});
              let name = token.id;
              if (name.match(/_/)) arg.mixfixes.push([name, parseOptions.fixity]);
              return parseTerm([], 'ann')
                .then(result => {
                  if (result.ctor !== 'ann') throw 'skip';
                  return endTest([ new Decl({sig: [ new Name({global: [name]}), result[1] ]}),
                    new Decl({def: [ new Name({global: [name]}), result[0] ]})])
                })
            }).catch(() => altNames(arg => {
              // term
              advance('Definition?', {value: 'name'})
              let name = token.id;
              if (name.match(/_/)) arg.mixfixes.push([name, parseOptions.fixity]);
              return parseTerm([], 'pi')
                .then(result => endTest([new Decl({def: [ new Name({global: [name]}), result ]})]))
            })).catch(() => error.parser_notvalid('definition'))

            case 'ddef': return altNames(arg => {
              // name bindings : type
              advance('Type/record definition?', {value: 'name'});
              let name = token.id;
              if (name.match(/_/)) arg.mixfixes.push([name, parseOptions.fixity]);
              arg.tnames.push(name);
              return dataDef([], 'ddef')
                .then(result => endTest([new Decl({data: [ new Name({global: [name]}), result, [] ] })]))
                .catch(() => error.parser_notvalid('type definition'))
            })

            case 'cdef': return altNames(arg => {
              // name : bindings type (?)
              advance('Constructor definition?');
              assertId();
              let name = token.id;
              if (name.match(/_/)) arg.mixfixes.push([name, parseOptions.fixity]);
              arg.dnames.push(name);
              advance('Type constructor separator?', {value: 'op', id: ':'});
              return dataDef([], 'cdef')
                .then(result => endTest([new Ctor({ctor: [ new Name({global: [name]}), result ]})]))
                .catch(() => error.parser_notvalid('constructor definition'))
            })

            case 'case': return altNames(arg => {
              // args | term
              advance('Case statement?');
              let name = token.id;
              if (name.match(/_/)) arg.mixfixes.push([name, parseOptions.fixity]);
              return caseOf([])
                .then(([bvs, fn]) => endTest([bvs, x => new Decl({def: [ new Name({global: [name]}), fn(x) ]})]))
                .catch(() => error.parser_notvalid('case statement'))
            })

            case 'pat': return alt(() => {
              // @ args := term
              let name;
              if (parseOptions.casePat) parserDebug('Pattern?');
              else {
                advance('Pattern?');
                name = token.id;
                advance('Pattern marker?', {value: 'op', id: '@'});
              }
              return pattern(parseOptions.bvs || [])
                .then(([pat, env]) => {
                  advance('Pattern equation separator?', {value: 'op', id: ':='});
                  return parseTerm(env, 'ann')
                    .then(term => endTest([new Match({clause: [pat, term]})])) // This should be a binder
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
        // TODO: enforce left erasure
        function bindvars () {
          // '{a} b c'
          advance('Binding variable?');
          assertId();
          let bvs = [[token, false]]
          return (function loop () { return alt(() => {
            advance('Binding next variable?');
            assertId();
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
              bindvars().then(bvs => parseTerm(isPi ? e : [], 'bind').then(type => [bvs, type])))
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
              parseTerm(env, 'bind').then(tm =>
                ({boundvars: bvs.map(x => x[0]), types: boundvars.map(() => tm), epsilons: bvs.map(x => x[1])})
              )
            ))
        })
      }

      function parseTerm (env, clause) { // TODO: split into separate functions
        function arrow (env, term) {
          advance('Function arrow?', {value: 'op', id: '->'});
          return parseTerm([''].concat(env), 'pi')
            .then(piBound => new Term({pi: [ term, piBound, false ]}))
        }
        function annot (term) {
          return alt(() => {
            advance('Annotated term?', {value: 'op', id: ':'});
            return parseTerm(env, 'bind')
              .then(ty => new Term({ann: [term, ty]}))
          }).catch(() => term)
        }

        switch (clause) {
          // lam *or* pi
          case 'bind': return altMsg('Try binding term', () => lambda(env))
            .catch(() => parseTerm(env, 'pi'))

          // {bnd} (bnd)...
          case 'pi': return altMsg('Try Pi', () =>
            bindings(env, true).then(({boundvars, types, epsilons}) => {
              // {bnd} (bnd)... -> term -> term...
              advance('Function arrow? (leftmost)', {value: 'op', id: '->'});
              return parseTerm(boundvars.concat(env), 'bind').then(piBound =>
                types.reduce((acc, ty, i) => acc = new Term({pi: [ty, acc, epsilons[i]]}), piBound)
              )
            })
          ) // lam
            .catch(() => alt(() => lambda(env)))
            // (ann)->...
            .catch(() => alt(() => parseTerm(env, 'ann').then(tm =>
              alt(() => arrow(env, tm)).catch(() => tm))
            ))

          // f a b... : term
          case 'ann': return altMsg('Try Annotation', () => parseTerm(env, 'ctor'))
            .catch(() => alt(() => parseTerm(env, 'app')).then(annot))
            // (a * b) : term
            .catch(() => enclosure(['parens'], () => mixfix(env)).then(annot))
            // (lam) : term
            .catch(() => enclosure(['parens'], () => lambda(env)).then(annot))

          // c a b... *or* t a b...
          case 'ctor': return altMsg('Try Constructor', () => {
            advance('Constructor term?');
            assertId();
            let ts = [], eps = [], name = token.id, ctor;
            if (~parser.tnames.indexOf(name)) ctor = 'tcon';
            else if (~parser.dnames.indexOf(name)) ctor = 'dcon';
            else throw new Error('');
            return (function loop () { return (ctor === 'tcon' ?
              parseTerm(env, 'var').then(term => [term, false]) :
              enclosure(['braces'], () => parseTerm(env, 'var').then(term => [term, true]))
                .catch(() => parseTerm(env, 'var').then(term => [term, false])))
                .then(([term, ep]) => {
                  ts.push(term);
                  eps.push(ep);
                  return loop()
                })
            })()
              .catch(() => new Term({[ctor]: [ new Name({global: [name]}),
                ts.map((x, i) => ctor === 'tcon' ? x : new Arg({arg: [ x, eps[i] ]})) ]}))
              .then(tm => mixfix(env, tm).catch(() => tm))
          })

          case 'app': return enclosure(['parens'], () => lambda(env))
            // *_ x...
            .catch(() => alt(() => mixfix(env)))
            // f a b...
            .catch(() => parseTerm(env, 'var'))
            // x _*_ y...
            .then(tm => alt(() => mixfix(env, tm)).catch(() => tm))
            .then(tm => altMsg('Try apply', () => {
              let ts = [], eps = [];
              parserDebug('Application?');
              return (function loop () { return enclosure(['braces'], () => parseTerm(env, 'var').then(term => [term, true]))
                .catch(() => parseTerm(env, 'var').then(term => [term, false]))
                .then(([term, ep]) => {
                  ts.push(term);
                  eps.push(ep);
                  return loop()
                })
              })().catch(() => ts.reduce((acc, term, i) => acc = new Term({app: [acc, term, eps[i]]}), tm))
            }))

          case 'var': return alt(() => {
            // Type
            advance('Star?', {id: 'Type'});
            return new Term({star: []})
          }) // a *or* [x=>][(x:X)->] x
            .catch(() => alt(() => {
              advance('Variable term?');
              assertId();
              let name = token.id;
              if (~parser.tnames.indexOf(name)) return new Term({tcon: [ new Name({global: [name]}), [] ]});
              else if (~parser.dnames.indexOf(name)) return new Term({dcon: [ new Name({global: [name]}), [] ]});
              let i = env.findIndex(bv => bv.id === name);
              return ~i ? new Term({boundvar: [i]}) : new Term({freevar: [ new Name({global: [name]}) ]})
            })) // x _*...
            .then(tm => mixfix(env, tm).catch(() => tm))
             // c... *or* t...
            .catch(() => alt(() => parseTerm(env, 'ctor')))
             // (pi)
            .catch(() => enclosure(['parens'], () => parseTerm(env, 'pi')))
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
              // x , {y} , ...
              return enclosure(['braces'], nextVar(true))
              // x , y , ...
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
            // x , y , .. => term
            return parseTerm(bvs.concat(env), 'bind')
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
            .then(({boundvars, types, epsilons}) => parseTerm(env, 'pi').then(typeFam =>
              types.reduceRight((acc, ty, i) => acc[epsilons[i] ? 'erased' : 'term'](new Name({global: [boundvars[i].id]}), ty), new Tele())
                .term(new Name({global: [parser.fresh()]}), typeFam)
            ))
        )
      }

      function pattern (env, name) { // TODO: inaccessible patterns
        function atomic () {
          // (pat)
          return enclosure(['parens'], () => pattern(env, name).then(([res, env]) => res))
            // _
            .catch(() => alt(() => {
              advance('Wildcard?', {id: '_'});
              return new Pat({patvar: [ new Name({global: [parser.fresh()]}), false ]})
            }))
            // t *or* x
            .catch(() => {
              advance('Variable or constructor term?');
              assertId();
              let nestedName = token.id;
              if (~parser.tnames.indexOf(nestedName)) error.tc_mismatch_con('type');
              else if (~parser.dnames.indexOf(nestedName)) return new Pat({patdcon: [new Name({global: [nestedName]}), [], false]})
              else {
                let i = env.findIndex(bv => bv.id === nestedName);
                return ~i ? new Pat({patbvar: [i]}) : new Pat({patvar: [ new Name({global: [nestedName]}), false ]})
              }
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
          })().catch(() => new Pat({patdcon: [ new Name({global: [name]}), ts, false ]}));
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
            .then(() => parseTerm(bvs.concat(env), 'ann').then(tm =>
              [bvs, x => bvs.reduce((acc, _, i) => new Term({lam: [acc, eps[i]]}), new Term({case: [tm, x]}))]
            ))
        })
      }

      function mixfix (env, mbTerm, pos = 0) { // TODO: mixfix erasure {A} x = x
        // x a_b...[...] *or* _a_b...[...]
        return altMsg('Try Mixfix Expression', () => {
          advance(`Mixfix operator in ${!!mbTerm ? 'second' : 'first' } position?`);
          assertOp();
          let ts = [], name = token.id, [mi, pi] = findMixfix(name, parser.mixfixes.map(x => x[0]));
          if (!~pi) {
            if (!mbTerm) return parseTerm(env, 'app').then(tm => mixfix(env, tm));
            throw new Error('');
          }
          let [mfName, fixity] = parser.mixfixes[mi], lexAp = lexMixfix(name), lexOp = lexMixfix(mfName);
          if (mbTerm) {
            if (lexAp[0] === '_') throw new Error('');
            ts.push(mbTerm)
          }
          if (pi > 1) error.parser_mixfix_miss_id(mfName, lexOp.slice(!!mbTerm, pi).join(''));
          ts = ts.concat(lexAp.filter(x => x === '_').fill(false));
          lexOp.splice(0, lexAp.length + pi);
          return (function loop () {
            if (lexOp.length === 1 && lexOp[0] === '_') return parseTerm(env, 'app').then(tm => {
              // ..._a x
              ts.push(tm);
              lexOp.shift();
              return loop()
            });
            return alt(() => parseTerm(env, 'app').then(tm => {
              // ..._a x b_...[...]
              advance('Next mixfix operator?');
              assertOp();
              name = token.id;
              lexOp.shift(); // the '_' for the current term
              lexAp = lexMixfix(name);
              if (lexAp.some((token, i) => token !== lexOp[i])) error.parser_mixfix_bad(name, mfName);
              (ts = ts.concat(lexAp.filter(x => x === '_').fill(false))).push(tm);
              lexOp.splice(0, lexAp.length);
              return loop()
            }))
          })()
            .catch(err => {
              if (!err.message) error.parser_mismatch(token, index);
              let falses = ts.filter(x => !x), holes = falses.length, mfTerm;
              if (~parser.tnames.indexOf(mfName)) mfTerm = new Term({tcon: [ new Name({global: [mfName]}),
                ts.map(t => t || new Term({boundvar: [--holes + env.length]})), [] ]});
              else if (~parser.dnames.indexOf(mfName)) mfTerm = new Term({dcon: [ new Name({global: [mfName]}),
                ts.map(t => new Arg({arg: [ t || new Term({boundvar: [--holes + env.length]}), false ]})), [] ]})
              else mfTerm = ts.reduce((a, t, i) =>
                new Term({app: [ a, t || new Term({boundvar: [--holes + env.length]}), false ]}), new Term({freevar: [ new Name({global: [mfName]}) ]}));
              return falses.reduce(a => new Term({lam: [a, false]}), mfTerm)
            })
        })
      }

      let token = tokens[0], index = 0, level = 0;
      return parseStatement([], [])
        // .then(r => (log('parsed expr', ...r.map(d => ~['sig', 'def'].indexOf(d.ctor) ? d[1].print() : d)),r))
        .then(result => (parserDebug('Expression:', result), result))
    }
  }), { parse } = parser;




  // Pretty printer

  function print (o) { // TODO: annotation pass, then print pass
    function vars (i) { return 'xyzwvutsrqponmlkjihgfedcba'.split('')[i % 26].repeat(Math.ceil(++i / 26)) }
    let anns = [], preString = (function recPrint (obj, int1 = 0, int2 = 0) {
      function step (v) {
        anns[v - 1] = 0;
        return v
      }
      function testObj (klass) { return klass.prototype.isPrototypeOf(obj) }
      function parensIf (bool, string) { return bool ? `(${string})` : string }
      function bracesIf (bool, string) { return bool ? `{${string}}` : string }
      function enclosureIf (bBool, pBool, string) { return bBool ? bracesIf(true, string) : parensIf(pBool, string) }
      function nestedLambda (body, eps, index) { return body.ctor === 'lam' ?
        nestedLambda(body[0], eps.concat([body[1]]), index + 1) :
        Array.from(Array(index), (_, i) => bracesIf(eps[i], vars(i))).join(', ') + ' => ' + recPrint(body, 0, index) }
      function nestedPi (range, domain, eps, index) { return domain.ctor === 'pi' ?
        nestedPi([[domain[0], index]].concat(range), domain[1], eps.concat([domain[2]]), step(index + 1)) :
        range.reverse().map(([tm, i], j) => enclosureIf(eps[j], true, `[${i}]` + recPrint(tm, 1, i)) + ' -> ').join('') + recPrint(domain, 0, index) }
      if (testObj(Term)) {
        switch (obj.ctor) {
          case 'star': return 'Type'
          case 'ann': return parensIf(int1 > 1, recPrint(obj[0], 2, int2) + ' : ' + recPrint(obj[1], 0, int2))
          case 'pi': return obj[1].ctor === 'pi' ?
            parensIf(int1 > 1, nestedPi([[obj[1][0], step(int2 + 1)], [obj[0], int2]], obj[1][1], [obj[2], obj[1][2]], step(int2 + 2))) :
            parensIf(true, bracesIf(obj[2], `[${int2}]` + recPrint(obj[0], obj[2], int2)) + ' -> ' + recPrint(obj[1], 0, step(int2 + 1)))
          case 'lam': return parensIf(int1 > 0, obj[0].ctor === 'lam' ?
            nestedLambda(obj[0][0], [obj[1], obj[0][1]], int2 + 2) :
            bracesIf(obj[1], vars(int2)) + ' => ' + recPrint(obj[0], 0, int2 + 1))
          case 'app': return parensIf(int1 > 1, recPrint(obj[0], 2 - (obj[0].ctor === 'app'), int2) + ' ' + bracesIf(obj[2], recPrint(obj[1], 2 + obj[2], int2)))
          case 'boundvar': anns[int2 - obj[0] - 1] = 1; return vars(int2 - obj[0] - 1)
          case 'freevar': return recPrint(obj[0], 0, int2)
          case 'tcon': return parensIf(int1 > 2 + !obj[1].length, recPrint(obj[0], 0, int2) + obj[1].map(tm => ' ' + recPrint(tm, 2, int2)).join(''))
          case 'dcon': return parensIf(int1 > 1 + !obj[1].length, recPrint(obj[0], 0, int2) +
            obj[1].map(arg => ' ' + (arg[1] ? `{${recPrint(arg[0], 3, int2)}}` : recPrint(arg[0], 2, int2))).join(''))
          case 'case': return recPrint(obj[0], 0, int2) + ' |' +
            obj[1].map(match => '\n  ' + recPrint(match[0], 0, int2) + ' := ' + recPrint(match[1], 0, int2))
        }
      } else if (testObj(Name)) {
        switch (obj.ctor) {
          case 'global': return typeof obj[0] === 'number' ? '_' + obj[0] : parensIf(~parser.mixfixes.findIndex(x => x[0] === obj[0]), obj[0])
          case 'local': return typeof obj[0] === 'number' ? vars(obj[0]) : obj[0]
        }
      } else if (testObj(Pat)) {
        switch (obj.ctor) {
          case 'patvar': return (obj[1] ? '.' : '') + recPrint(obj[0], 0, int2)
          case 'patbvar': anns[int2 - obj[0] - 1] = 1; return vars(obj[0])
          case 'patdcon': return (obj[2] ? '.' : '') + parensIf(int1 > 1, recPrint(obj[0], 0, int2) +
          obj[1].map(arg => ' ' + (arg[1] ? `{${recPrint(arg[0], 1, int2)}}` : recPrint(arg[0], 1, int2))).join(''))
        }
      } else if (testObj(Tele)) {
        return (obj.items.length - 1 ? ' ' : '') + obj.items.slice(0, -1).map(item => {
          switch (item.ctor) {
            case 'term': return `(${recPrint(item[0], 0, int2) + ' : ' + recPrint(item[1], 0, int2)})`
            case 'erased': return `{${recPrint(item[0], 0, int2) + ' : ' + recPrint(item[1], 0, int2)}}`
            case 'constraint': return `{${recPrint(item[0], 0, int2) + ' = ' + recPrint(item[1], 0, int2)}}`
          }
        }).join('') + ' : ' + recPrint(obj.items.slice(-1)[0][1], 1, int2)
      } else if (testObj(Ctor)) return recPrint(obj[0]) + recPrint(obj[1]);
      else if (testObj(Value)) error.print_value(print(quote(obj)));
      else if (typeof obj === 'string') return obj;
      else error.print_bad(obj)
    })(o);
    return preString.replace(/\[(\d{1,3})\]/g, (_, m) => (anns[m] ? vars(anns.slice(0, m + 1).reduce((a, b) => a + b) - 1) + ' : ' : ''))
  }




  // Typechecking

  class Context {
    decls = []
    constructor (obj) { if (obj) this.decls = obj.decls.slice() }
    lookup (name, ctor, annot) {
      if (ctor === 'ctor') {
        let mbCdef;
        if (typeof annot === 'undefined') return this.decls.reduce((a, decl) => {
          if (decl.ctor === 'data' && (mbCdef = decl[2].find(cdef => cdef[0].equal(name))))
            a.push({tname: decl[0], ddef: decl[1], cdef: mbCdef[1]});
          return a
        }, []);
        else {
          let mbDdef = this.decls.find(decl => decl.ctor === 'data' && decl[0].equal(annot) &&
            (mbCdef = decl[2].find(cdef => cdef[0].equal(name))));
          return { ddef: mbDdef ? mbDdef[1] : null, cdef: mbCdef ? mbCdef[1] : null }
        }
      }
      let result = this.decls.find(decl => (decl.ctor === ctor || (ctor === 'data' && decl.ctor === 'datasig')) && decl[0].equal(name));
      if (result) return ctor === 'data' ? { ddef: result[1], cdef: result.ctor === 'datasig' ? null : result[2] } : result[1]
    }
    cons (decl) { return this.push(decl, true) }
    extend (decl) { return this.push(decl, false) }
    push (decl, n) {
      let ret = n ? new Context(this) : this;
      if (!Array.prototype.isPrototypeOf(decl)) decl = [decl];
      else if (!decl.length) return ret;
      let d = decl.shift(),
          i = (d[0][0] === '') ? -1 : ret.decls.findIndex(x => x[0][0] === '');
      ret.decls.splice(i === -1 ? ret.decls.length : i, 0, d);
      return decl.length ? ret.push(decl, false) : ret
    }
    localVal (i) { return this.decls[this.decls.length - i - 1][1] }
    concatTele (tele) {
      return tele.items.reduce((acc, item) => { switch (item.ctor) {
        case 'term': case 'erased': return acc.cons(new Decl({sig: [item[0][0], item[1]]}))
        case 'constraint': return acc.cons({def: [...item]})
      } }, new Context(this))
    }
  }
  const context = new Context();

  // Values
  function evaluate (term, ctx = context) {
    // console.log('eval', term.toString())
    let mbVal, vscrut, local = x => new Decl({sig: [ new Name({global: ['']}), x ]});
    switch (term.ctor) {
      case 'star': return new Value({vstar: []})
      case 'ann': return evaluate(term[0], ctx)
      case 'pi': return new Value({vpi: [ evaluate(term[0], ctx), x => evaluate(term[1], ctx.cons(local(x))), term[2] ]})
      case 'lam': return new Value({vlam: [ x => evaluate(term[0], ctx.cons(local(x))), term[1] ]})
      case 'app': return vapply(evaluate(term[0], ctx), evaluate(term[1], ctx), term[2])
      case 'boundvar': return ctx.localVal(term[0])
      case 'freevar': return (mbVal = ctx.lookup(term[0], 'def')) ? mbVal : new Value({vfree: [term[0]]})
      case 'tcon': return new Value({vtcon: [ term[0], term[1].map(tm => evaluate(tm, ctx)) ]})
      case 'dcon': return new Value({vdcon: [ term[0], term[1]
        .map(arg => new Arg({arg: [ evaluate(arg[0], ctx), arg[1] ]})) ].concat([term[2]].filter(Boolean))})

      case 'case': switch ((vscrut = evaluate(term[0], ctx)).ctor) {
        case 'vfree': return new Value({vcase: [ vscrut, term[1] ]});
        case 'vdcon':
        let match = term[1].find(match => match[0].ctor !== 'patdcon' || vscrut[0].equal(match[0][0]));
        switch (match[0].ctor) {
          case 'patvar': return evaluate(match[1], ctx.cons(new Decl({def: [ match[0][0], vscrut ]})));
          case 'patbvar': return evaluate(match[1], ctx.cons(new Decl({def: [ new Term({boundvar: [ match[0][0] ]}), vscrut ]})));
          case 'patdcon':
          let decls = match[0][1].filter(x => !x[1]).map((x, i) => {
                if (x[0].ctor === 'patdcon') error.tc_internal('eval case trying to match on a patdcon');
                return new Decl({def: [x[0][0], vscrut[1][i][0]]})
              });
          return evaluate(match[1], ctx.cons(decls))
        }
      }
    }
  }

  function vapply (value1, value2, epsilon) {
    switch (value1.ctor) {
      case 'vlam': return value1[0](value2)
      case 'vapp': case 'vtcon': case 'vdcon': case 'vfree': return new Value({vapp: [ value1, value2, epsilon ]})
      default: error.tc_bad_app()
    }
  }

  function quote (value, index = 0) {
    let name, qname = new Name({quote: [index]});
    switch (value.ctor) {
      case 'vstar': return new Term({star: []})
      case 'vpi': return new Term({pi: [ quote(value[0], index), quote(value[1](new Value({vfree: [qname]})), index + 1), value[2]]})
      case 'vlam': return new Term({lam: [ quote(value[0](new Value({vfree: [qname]})), index + 1), value[1] ]})
      case 'vfree': return (name = value[0]).ctor === 'quote' ? new Term({boundvar: [index - name[0] - 1]}) : new Term({freevar: [name]})
      case 'vtcon': return new Term({tcon: [ value[0], value[1].map(v => quote(v, index)) ]})
      case 'vdcon': return new Term({dcon: [ value[0], value[1]
        .map(arg => new Arg({arg: [ quote(arg[0], index), arg[1] ]})) ].concat([value[2]].filter(Boolean))})
      case 'vapp': return new Term({app: [ quote(value[0], index), quote(value[1], index), value[2] ]})
      case 'vcase': return new Term({case: [ quote(value[0]), value[1] ]})
    }
  }

  function typecheck (decls) {
    // Infer/check
    function infer (args) { //context, term, number -> value
      let { ctx, term, index = 0 } = args, innerArgs;
      return Promise.resolve().then(() => {
        let result, vstar = new Value({vstar: []}), local = new Name({local: [index]});
        switch (term.ctor) {
          case 'star': return vstar

          case 'ann':
          let annTerm = term[0];
          return check(ctx, term[1], vstar, index)
            .catch(e => error.append(e.message, 'tc_ann_mismatch', '?'))
            .then(({term}) => check(ctx, annTerm, evaluate(term, ctx), index))
            .then(({type})=> type)

          case 'pi': return infer(innerArgs = {ctx, term: term[0], index})
            .then(type1 => {
              term[0] = innerArgs.term;
              if (type1.ctor !== 'vstar') error.tc_pi_mismatch('domain', quote(type1));
              return infer(innerArgs = {
                ctx: ctx.cons(new Decl({sig: [ local, evaluate(term[0], ctx) ]})),
                term: subst(new Term({freevar: [ local ]}), term[1], false), index: index + 1})
                .then(type2 => {
                  args.term = new Term({pi: [term[0], unsubst(new Term({boundvar: [ index ]}), innerArgs.term), term[2]]});
                  if (type2.ctor !== 'vstar') error.tc_pi_mismatch('range', quote(type2));
                  return vstar
                })
            })

          case 'app': return infer(innerArgs = {ctx, term: term[0], index})
            .then(type => {
              term[0] = innerArgs.term;
              if (type.ctor !== 'vpi') error.tc_app_mismatch(quote(type));
              let [dom, func] = type;
              return check(ctx, term[1], dom, index)
                .then(({term}) => func(evaluate(term, ctx)))
            })

          case 'freevar':
          if (result = ctx.lookup(term[0], 'sig')) return result
          error.tc_unknown_id(term[0])

          case 'tcon':
          if (term.length === 1) term.push([]) //?
          result = ctx.lookup(term[0], 'data');
          if (result.ddef === null) error.tc_term_not_found(term[0][0]);
          result = result.ddef;
          let runtimeItems = result.items.filter(x => x.ctor === 'term');
          if (runtimeItems.length - 1 > term[1].length) error.tc_dcon_arg_len(term[1].length, runtimeItems.length - 1);
          else if (runtimeItems.length - 1 < term[1].length)
            return infer({ctx, term: args.term = term[1].slice(runtimeItems.length - 1).reduce((acc, tm) => new Term({app: [acc, tm, false]}),
              new Term({tcon: [term[0], term[1].slice(0, runtimeItems.length - 1)]})), index});
          return tcArgTele(ctx, term[1].map(x => new Arg({arg: [x, false]})), result.items.slice(0, -1)).then(() => result.items.slice(-1)[0][1])

          case 'dcon':
          if (typeof term[2] !== 'undefined') return check(ctx, term, term[2], index);
          if (term.length === 1) term.push([]) //?
          let matches = ctx.lookup(term[0], 'ctor');
          if (matches.length !== 1) error.tc_dcon_ambiguity();
          let match = matches[0];
          if (match.ddef.length !== 1) error.tc_dcon_cannot_infer_params();
          if (match.cdef.length - 1 > term[1].length) error.tc_dcon_arg_len(term[1].length, match.cdef.length - 1);
          else if (match.cdef.length - 1 < term[1].length)
            return infer({ctx, term: args.term = term[1].slice(match.cdef.length - 1).reduce((acc, tm) => new Term({app: [acc, ...tm]}),
              new Term({dcon: [term[0], term[1].slice(0, match.cdef.length - 1)].concat([term[2]].filter(Boolean))})), index});
          return tcArgTele(ctx, term[1], match.cdef.items.slice(0, -1)).then(() => evaluate(new Term({tcon: [ match.tname, [] ]}), ctx))

          case 'lam': error.tc_cannot_infer('lambda')
          case 'case': error.tc_cannot_infer('case')
        }
      })
    }

    function check (ctx, term, typeVal, index = 0) { //context, term, term, number -> term:term, type:value
      if (debug.typechecker) log('check', term.toString(), term, typeVal.toString(), typeVal);
      // log('ctx', ...ctx.decls.map(x => x.toString()))
      let innerArgs;
      return Promise.resolve().then(() => {
        switch (term.ctor) {
          case 'lam':
          if (typeVal.ctor !== 'vpi') error.tc_lam_mismatch(typeVal.ctor);
          if (term[1] !== typeVal[2]) error.tc_erasure_mismatch();
          else {
            let local = new Name({local: [index]});
            return check(
              ctx.cons(new Decl({sig: [ local, typeVal[0] ]})),
              subst(new Term({freevar: [ local ]}), term[0], false),
              typeVal[1](new Value({vfree: [local]})), index + 1)
              .then(({term}) => ({term: new Term({lam: [unsubst(new Term({boundvar: [ index ]}), term), typeVal[2]]}), type: typeVal}))
          }

          case 'dcon':
          let type = quote(typeVal);
          if (typeof term[2] !== 'undefined' && 'equal' in term[2] && !term[2].equal(type)) error.tc_mismatch(term[2], type, term);
          if (term.length === 1) term.push([]) //?
          let [typei, itemsi] = unapplyType(type), match = ctx.lookup(term[0], 'ctor', typei[0]);
          if (match.cdef === null || match.ddef === null) error.tc_term_not_found(term[0][0], typei[0][0]);
          if (match.cdef.length - 1 > term[1].filter(x => !x[1]).length) error.tc_dcon_arg_len(term[1].length, match.cdef.length - 1); // BUG: erased/runtime
          if (match.cdef.length - 1 < term[1].filter(x => !x[1]).length)
            return check(ctx, term[1].slice(match.cdef.length - 1).reduce((acc, tm) => new Term({app: [acc, ...tm]}),
              new Term({dcon: [term[0], term[1].slice(0, match.cdef.length - 1)].concat([term[2]].filter(Boolean))})), typeVal, index);
          let items = substTele(ctx, match.ddef.tail(), itemsi, match.cdef);
          return tcArgTele(ctx, term[1], items.slice(0, -1)).then(args => ({ term: new Term({dcon: [ term[0], args, typeVal ]}), type: typeVal }))

          case 'case':
          return infer(innerArgs = {ctx, term: term[0], index})
            .then(type => {
              term[0] = innerArgs.term;
              let typeTerm = quote(type);
              if (typeTerm.ctor !== 'tcon' && typeTerm.ctor !== 'app') error.tc_mismatch(typeTerm, 'Type Constructor', term[0]);
              return term[1].reduce((p, match) => p.then(acc => {
                let [decls1, evars] = declarePat(ctx, match[0], false, typeTerm), // TODO: check erased vars aren't used
                    decls2 = equateWithPat(ctx, term[0], match[0], typeTerm);
                return check(ctx.cons(decls1.concat(decls2)), match[1], typeVal, index)
                  .then(({term}) => acc.concat([new Match({clause: [match[0], term]})]))
              }), Promise.resolve([]))
                .then(matches => exhaustivityCheck(ctx, term[0], typeTerm, term[1].map(x => x[0]))
                  .then(() => ({term: new Term({case: [term[0], matches, typeVal]}), type: typeVal})))
            })

          default: return infer(innerArgs = {ctx, term, index})
            .then(type => {
              let res = quote(type), ty = quote(typeVal);
              if (!res.equal(ty)) error.tc_mismatch(res, ty, innerArgs.term);
              else return {term: innerArgs.term, type: typeVal}
            })
        }
      })
    }

    // Terms
    function subst (term1, term2, ep, index = 0) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ subst(term1, term2[0], ep, index), subst(term1, term2[1], ep, index) ]})
        case 'pi': return new Term({pi: [ subst(term1, term2[0], ep, index), subst(term1, term2[1], ep, index + 1), term2[2] ]})
        case 'lam': return new Term({lam: [ subst(term1, term2[0], ep, index + 1), term2[1] ]})
        case 'app': return new Term({app: [ subst(term1, term2[0], ep, index), subst(term1, term2[1], ep, index), term2[2] ]})
        case 'boundvar': return index !== term2[0] ? term2 : !ep ? term1 : error.tc_erased_var_subst()
        case 'tcon': return new Term({tcon: [ term2[0], term2[1].map(tm => subst(term1, tm, ep, index)) ]})
        case 'dcon': return new Term({dcon: [ term2[0],
          term2[1].map(arg => new Arg({arg: [ subst(term1, arg[0], ep, index), arg[1]]})) ].concat([term2[2]].filter(Boolean))})
        case 'case': return new Term({case: [ subst(term1, term2[0], ep, index),
          term2[1].map(match => new Match({clause: [ substPat(term1, match[0], ep, index), subst(term1, match[1], ep, index) ]})) ].concat([term2[2]].filter(Boolean))})
        case 'star': case 'freevar': return term2
      }
    }
    function substPat (term, pat, ep, index) {
      switch (pat.ctor) {
        case 'patvar': return pat
        case 'patbvar': return index !== pat[0] ? pat : !ep ? new Pat({patvar: [term[0], false]}) : error.tc_erased_var_subst()
        case 'patdcon': return new Pat({patdcon: [ pat[0], pat[1].map(arg => new Arg({arg: [ substPat(term, arg[0], ep, index), arg[1] ]})), pat[2] ]})
      }
    }
    function unsubst (term1, term2, index = 0) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ unsubst(term1, term2[0], index), unsubst(term1, term2[1], index) ]})
        case 'pi': return new Term({pi: [ unsubst(term1, term2[0], index), unsubst(term1, term2[1], index + 1), term2[2] ]})
        case 'lam': return new Term({lam: [ unsubst(term1, term2[0], index + 1), term2[1] ]})
        case 'app': return new Term({app: [ unsubst(term1, term2[0], index), unsubst(term1, term2[1], index), term2[2] ]})
        case 'freevar': return term2[0].ctor === 'local' && index === term2[0][0] ? term1 : term2
        case 'tcon': return new Term({tcon: [ term2[0], term2[1].map(tm => unsubst(term1, tm, index)) ]})
        case 'dcon': return new Term({dcon: [ term2[0],
          term2[1].map(arg => new Arg({arg: [ unsubst(term1, arg[0], index), arg[1]]})) ].concat([term2[2]].filter(Boolean))})
        case 'case': return new Term({case: [ unsubst(term1, term2[0], index),
          term2[1].map(match => new Match({clause: [ unsubstPat(term1, match[0], index), unsubst(term1, match[1], index) ]})) ].concat([term2[2]].filter(Boolean))})
        case 'star': case 'boundvar': return term2
      }
    }
    function unsubstPat (term, pat, index) {
      switch (pat.ctor) {
        case 'patbvar': case 'patvar': return pat[0].ctor === 'local' && index === pat[0][0] ? new Pat({patbvar: [term[0]]}) : pat
        case 'patdcon': return new Pat({patdcon: [ pat[0], pat[1].map(arg => new Arg({arg: [ unsubstPat(term, arg[0], index), arg[1] ]})), pat[2] ]})
      }
    }

    function substFV (term1, term2, name) {
      switch (term2.ctor) {
        case 'ann': return new Term({ann: [ substFV(term1, term2[0], name), substFV(term1, term2[1], name) ]})
        case 'pi': return new Term({pi: [ substFV(term1, term2[0], name), substFV(term1, term2[1], name), term2[2] ]})
        case 'lam': return new Term({lam: [ substFV(term1, term2[0], name), term2[1] ]})
        case 'app': return new Term({app: [ substFV(term1, term2[0], name), substFV(term1, term2[1], name), term2[2] ]})
        case 'freevar': return name.equal(term2) ? term1 : term2
        case 'tcon': return new Term({tcon: [ term2[0], term2[1].map(tm => substFV(term1, tm, name)) ]})
        case 'dcon': return new Term({dcon: [ term2[0],
          term2[1].map(arg => new Arg({arg: [ substFV(term1, arg[0], name), arg[1] ]})) ].concat([term2[2]].filter(Boolean))})
        case 'case': return new Term({case: [ substFV(term1, term2[0], name),
          term2[1].map(match => new Match({clause: [ match[0], substFV(term1, match[1], name) ]})) ]})
        case 'star': case 'boundvar': return term2
      }
    }

    function unapplyType (term) {
      let items = [], type = term;
      while (type.ctor === 'app') {
        items = [type[1]].concat(items);
        type = type[0]
      }
      return [type, type[1].concat(items)]
    }

    // Telescopes
    function tcTele (ctx, tele) {
      return tele.items.reduce((p, item) => p.then(acc => {
        switch (item.ctor) {
          case 'term': case 'erased':
          let [name, type] = item;
          return check(ctx, type, new Value({vstar: []}))
            .then(({term}) => ctx.extend(new Decl({sig: [ name, type = evaluate(term, ctx) ]})))
            .then(() => acc.concat([new Item({[item.ctor]: [ new Term({freevar: [name]}), type ]})]))

          case 'constraint':
          return infer({ctx, term: item[0]})
            .then(type => check(ctx, item[1]), type)
            .then(({term}) => constraintToDecls(ctx, item[0], item[1] = term))
            .then(decls => decls.forEach(decl => ctx.extend(decl)))
            .then(() => acc.concat([item]))
        }
      }), Promise.resolve([])).then(items => new Tele(...items))
    }

    function constraintToDecls (ctx, term1, term2) {
      let decls = [];
      if (term1.equal(term2)) return decls;
      if (term1.ctor === 'app' && term2.ctor === 'app') decls = decls
        .concat(constraintToDecls(ctx, term1[0], term2[0]))
        .concat(constraintToDecls(ctx, term1[1], term2[1]));
      else if (term1.ctor === 'freevar') return [ new Decl({def: [term1[0], term2]}) ];
      else if (term2.ctor === 'freevar') return [ new Decl({def: [term2[0], term1]}) ];
      else error.tc_constraint_cannot_eq()
    }

    function tcArgTele (ctx, args, items) {
      // log('tcArgTele', args.map(x => x.toString()), items.map(x => x.toString()))
      let rightItems = items.slice(), runtimeArgs = [], item,
          loop = i => {
            if (rightItems.length === 0) return Promise.resolve();
            if ((item = rightItems[0]).ctor === 'erased' && args.length === 0) {
              rightItems.shift();
              return loop(i)
            }
            let arg = args[i];
            function doCheck () {
              return check(ctx, arg[0], item[1]).then(({term}) => {
                arg[0] = term;
                rightItems = doSubst(ctx, [[rightItems.shift()[0], arg[0]]], new Tele(...rightItems));
                runtimeArgs.push(arg)
                return loop(i + 1)
              })
            }
            switch (item.ctor) {
              case 'term':
              if (arg[1]) throw error.tc_erasure_mismatch();
              else return doCheck()

              case 'erased':
              if (!arg[1]) {
                rightItems.shift();
                return loop(i);
              } else return doCheck()

              case 'constraint':
              if (item[0].equal(item[1])) return loop(i + 1);
              error.tc_mismatch(...item)
            }
          };
      return loop(0).then(() => runtimeArgs)
    }

    function doSubst (ctx, nameTerms, tele) {
      return tele.items.map(item => {
        switch (item.ctor) {
          case 'term': case 'erased':
          let type = nameTerms.reduce((acc, [name, term]) => substFV(term, acc, name), quote(item[1]));
          return new Item({[item.ctor]: [item[0], evaluate(type, ctx)]})

          case 'constraint':
          let substItems = item.map(side => nameTerms.reduce((acc, [name, term]) => substFV(term, acc, name), side));
          constraintToDecls(ctx, ...substItem).forEach(decl => ctx.extend(decl));
          return new Item({constraint: substItems})
        }
      })
    }

    function substTele (ctx, tele1, terms, tele2) {
      return doSubst(ctx, tele1.items.map((item, i) => {
        switch (item.ctor) {
          case 'term': return [item[0], terms[i]];
          default: error.internal_arg('substTele')
        }
      }), tele2)
    }

    // Pattern matching
    // TODO: case splitting
    function declarePat (ctx, pat, ep, type) { // adds bindings to the ctx recursively for each patvar in the pattern
      switch (pat.ctor) {
        case 'patvar':
        let name = pat[0];
        return [[new Decl({sig: [name, type]})], ep ? [name] : []]

        case 'patbvar':
        return [[new Decl({sig: [new Term({boundvar: [pat[0]]}), type]})], []]

        case 'patdcon':
        if (ep) error.tc_erased_pat();
        let [typei, itemsi] = unapplyType(type), result = ctx.lookup(pat[0], 'ctor', typei[0]),
            items = substTele(ctx, result.ddef.tail(), itemsi, result.cdef);
        return declarePats(ctx, pat[0], pat[1], items.slice(0, -1))
      }
    }
    function declarePats (ctx, name, patArgs, items) {
      let rightItems = items, decls = [], decls1, names = [], names1, i = 0;
      while (
        (i !== patArgs.length && !rightItems.length && error.tc_pat_dcon_len(false)) ||
        (i === patArgs.length && rightItems.length && error.tc_pat_dcon_len(true)) ||
        i !== patArgs.length || rightItems.length
      ) {
        let ep = true, pat = patArgs[i][0];
        switch (rightItems[0].ctor) {
          case 'term': ep = false; case 'erased':
          [decls1, names1] = declarePat(ctx, pat, ep, rightItems[0][1]);
          let term = quotePat(ctx, pat, quote(rightItems[0][1]));
          rightItems = doSubst(ctx, [[rightItems.shift()[0], term]], new Tele(...rightItems));
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
      if (pat.ctor === 'patvar') return new Term({freevar: [pat[0]]});
      else if (pat.ctor === 'patbvar') return new Term({boundvar: [pat[0]]});
      else if (pat.ctor === 'patdcon' && type.ctor !== 'tcon' && type.ctor !== 'app') error.internal_arg('quotePat');
      let [typei, itemsi] = unapplyType(type), result = ctx.lookup(pat[0], 'ctor', typei[0]),
          items = substTele(ctx, result.ddef.tail(), itemsi, result.cdef),
          rightItems = items.slice(0, -1), args = [], i = 0;
      while (
        (!(rightItems.length ^ (i === pat[1].length)) && error.tc_pat_len(pat[0])) ||
        rightItems.length
      ) {
        let ep = true;
        switch (rightItems[0].ctor) {
          case 'term': ep = false; case 'erased':
          let t = quotePat(ctx, pat[1][i][0], quote(rightItems.shift()[1]));
          args.push(new Arg({arg: [t, ep]}));
          i++; break;

          case 'constraint':
          rightItems.splice(0, 1);
          ctx.extend(constraintToDecls(ctx, ...type)) //???
        }
      }
      return new Term({dcon: [pat[0], args, type]})
    }

    function equateWithPat (ctx, term, pat, type) {
      switch (term.ctor) {
        case 'freevar': return [new Decl({def: [ term[0], evaluate(quotePat(ctx, pat, type), ctx) ]})]

        case 'dcon':
        if (!term[0].equal(pat[0])) return [];//error.tc_pat_cannot_omit(pat[0]);
        let [typei, itemsi] = unapplyType(type), result = ctx.lookup(term[0], 'ctor', typei[0]),
            items = substTele(ctx, result.ddef.tail(), itemsi, result.cdef),
            rightItems = items.slice(0, -1), decls = [], i = 0;
        for (; rightItems.length; i++) {
          let thisItem = rightItems.shift();
          switch (thisItem.ctor) {
            case 'term': case 'erased':
            decls = decls.concat(equateWithPat(ctx, term[1][i][0], pat[1][i][0], quote(thisItem[1])));
            rightItems.forEach(item => item[0] = substFV(thisItem[0], item[0], term[1][i][0]));
            break;

            case 'contraint':
            ctx.extend(constraintToDecls(ctx, ...items[i]));
          }
        }
        return decls

        default: return []
      }
    }

    function exhaustivityCheck (ctx, term, type, pats) {
      function checkImpossible (cdefs) {
        return cdefs.reduce((p, cdef) => p.then(acc =>
          tcTele(ctx, new Tele(...substTele(ctx, result.ddef.tail(), type[1], cdef[1])))
            .then(() => [cdef[0]])
            .catch(() => [])
            .then(res => acc.concat(res))
        ), Promise.resolve([]))
      }
      function removeDcon (name, cdefs) {
        for (let i = 0; i < cdefs.length; i++) if (name.equal(cdefs[i][0])) return [cdefs.splice(i, 1)[0], cdefs];
        error.internal_cant_find(name)
      }
      function relatedPats (name, pats) {
        let argss = [], pats1 = []
        for (let i = 0; i < pats.length; i++) switch (pats[i].ctor) {
          case 'patdcon':
          if (name === pats[i][0]) args.push(pats[i][1]);
          else pats1.push(pats[i]);
          break;

          case 'patvar': case 'patbvar':
          argss = [];
          pats1.push(pats[i])
        }
        return [argss, pats1]
      }
      function checkSubPats (name, items, patss) { // All subpatterns must be PatVars
        items.forEach((item, i) => {
          switch (item.ctor) {
            case 'term': case 'erased':
            if (patss.length !== 0 && patss.every(pats => pats.length !== 0)) {
              let {hds, tls} = patss.reduce((acc, pats) => {
                    acc.hds.push(pats[0][0]);
                    acc.tls.push(pats.slice(1));
                    return acc
                  }, {hds: [], tls: []});
              if (hds.length === 1 && hds[0].ctor !== 'patdcon') patss = tls;
              else error.tc_subpat_cannot_dcon()
            } else error.internal('checkSubPats')
          }
        })
      }
      if (pats.length > 0 && pats[0].ctor !== 'patdcon') return;
      let [typei, itemsi] = unapplyType(type);
      if (typei.ctor !== 'tcon' ) error.tc_mismatch(type, 'Type Constructor');
      let result = ctx.lookup(typei[0], 'data');
      if (result.cdef === null) error.tc_dcon_cannot_infer();
      (function branch (ps, dcons) {
        if (ps.length === 0) {
          if (dcons.length === 0) return;
          else return checkImpossible(dcons)
            .then(l => l.length === 0 || error.tc_missing_cases(l))
        } else ps.forEach((pat, i) => {
          if (pat.ctor === 'patdcon') {
            let [cd, dcons1] = removeDcon(pat[0], dcons.slice());
            let items = substTele(ctx, result.ddef.tail(), itemsi, cd[1]),
                [argss, pats1] = relatedPats(pat[0], ps.slice(i + 1));
            checkSubPats(pat[0], items.slice(0, -1), [pat[1], ...argss]);
            return branch(pats1, dcons1)
          }
        })
      })(pats, result.cdef);
      return Promise.resolve()
    }

    // Main typecheck
    return decls.reduce((p, decl) => p.then(acc => {
      if (debug.typechecker || debug.parsedDecl) log('typechecking...', decl.toString(), ...(decl.ctor === 'data' ? [] : [decl[1].print()]));
      let [name, info, ctors] = decl, mbValue, value, args;
      switch (decl.ctor) {
        case 'sig':
        mbValue = context.lookup(name, 'sig');
        if (typeof mbValue !== 'undefined') {
          if (info.equal(quote(mbValue))) return acc.concat([{declName: 'sig', type: mbValue[1].quote(), term: info}]);
          else error.duplicate(name);
        } else return infer(args = {ctx: context, term: info}).then(type => {
          if (typeof name[0] !== 'number') console.log(print(name), ':', print(args.term));
          context.extend(new Decl({sig: [ name, evaluate(args.term) ]}));
          return acc.concat([{declName: 'sig', type: quote(type), term: args.term}])
        })

        case 'def':
        mbValue = context.lookup(name, 'def');
        if (typeof mbValue !== 'undefined') {
          if (info.equal(quote(mbValue))) return acc.concat([{declName: 'def', type: context.lookup(name, 'sig'), term: info}]);
          else error.duplicate(name)
        } else {
          let mbType = context.lookup(name, 'sig');
          return (typeof mbType === 'undefined') ?
            infer(args = {ctx: context, term: info}).then(type => {
              let typeTerm = quote(type);
              if (typeof name[0] !== 'number') {
                console.log(print(name), ':', print(typeTerm));
                console.log(print(name), ':=', print(args.term));
              }
              context.extend([new Decl(({sig: [name, type]})), new Decl({def: [name, evaluate(args.term)]})]);
              return acc.concat([{declName: 'def', type: typeTerm, term: args.term}])
            }) :
            check(context, info, mbType).then(({term, type}) => {
              if (typeof name[0] !== 'number') console.log(print(name), ':=', print(term));
              context.extend(new Decl({def: [name, evaluate(term)]}));
              return acc.concat([{declName: 'def', type: quote(type), term}])
            })
        }

        case 'data':
        return tcTele(new Context(context), info).then(tele =>
          ctors.reduce((p, ctor) => p.then(acc =>
            tcTele(context.cons(new Decl({datasig: [name, tele]})).concatTele(tele), ctor[1])
              .then(ctorTele => acc.concat([new Ctor({ctor: [ctor[0], ctorTele]})]))
          ), Promise.resolve([])).then(ctors => {
            let quoteTele = tl => new Tele(...tl.items.map(item =>
              new Item({[item.ctor]: [ item.ctor === 'constraint' ? quote(item[0]) : item[0], quote(item[1]) ]})));
            console.log(print(name) + print(quoteTele(tele)) +
              ctors.map(ctor => '\n  ' + print(new Ctor({ctor: [ ctor[0], quoteTele(ctor[1]) ]}))).join(''));
            let decl = new Decl({data: [name, tele, ctors]});
            context.extend(decl);
            return [{ declName: 'data', params: tele.items.slice(0, -1), type: quote(tele.items.slice(-1)[0][1]), ctors,
              ...(tele.items.length === 1 && tele.items[0][1].ctor === 'vstar' ? {term: new Term({tcon: [name, []]})} : {})
            }]
          })
        )

        case 'datasig': error.tc_internal()
      }
    }), Promise.resolve([])).catch(e => {console.log(e);throw e})
  }




  // API

  const R = { Data, Sig, Def, context, parser },
        sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  Object.defineProperty(R, 'ready', { get () { return sequence(() => new Promise(r => queueMicrotask(r))) } }); // TODO: make all props read-only

  return R
}
