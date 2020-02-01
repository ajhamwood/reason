var R = (() => {

  // Utilities

  const error = {
    unchecked: () => { throw new Error('Type error: unchecked') },
    lexer: (err, col, info) => { throw new Error(`Lexer error: ${err}\nat ${col}\n${info}`) }
  };

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
      if (!sourceString) return tokens;
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

  // Parser

  function parse (lex) {
    return Promise.resolve()
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
  let test2 = new R.Def('id', '(t, x => x)(T : Type) -> T -> T');
  let test3 = new R.Data('Unit : Type', ['tt : Unit'], { fromJS: () => Unit().tt() });
  passFail({ test1, test2, test3 })
  await R.ready;

  passFail({ test1: () => test1, test2, test3 });
  let test4 = test1.Def('t, x => x');
  passFail({ test4 });
  await R.ready;

  passFail({ test4 })
})()
