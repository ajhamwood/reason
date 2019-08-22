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


class Sigma {
  constructor (type, fun) {
    if (!testCtor(type, Function) || !testCtor(fun, Function)) throw new Error('Type mismatch')
    this.fstType = type
    this.sndFun = fun
    let pair
    return class {
      constructor (first, second) {
        if (!test(first, type) || !test(second, fun(first))) throw new Error('Type mismatch')
        pair = [first, second]
        return this
      }
      first () { return pair[0] }
      second () { return pair[1] }
    }
  }
}

class Pair extends Sigma {
  constructor (type1, type2) {
    super(type1, () => type2)
    this.fstType = type1
    this.sndType = type2
  }
}


class List {
  constructor (type) {
    if (!test(type, Function)) throw new Error('Type mismatch');
    this.elemType = type
    return this
  }
  get Nil () {
    let { elemType } = this
    return class Nil extends List {
      _typecon = this.Nil
      _values = []
      constructor () {
        super(elemType)
        return this
      }
    }
  }
  get Cons () {
    let { elemType, _values } = this
    return class Cons extends List {
      _typecon = this.Cons
      _values = _values.slice()
      constructor (value) {
        super(elemType)
        this._values.unshift(value)
        return this
      }
    }
  }
  nil () {
    return new this.Nil()
  }
  cons (value) {
    if (!test(value, this.elemType)) throw new Error('Type mismatch')
    return new this.Cons(value)
  }
  concat (list) {
    if (this.elemType !== list.elemType) throw new Error('Type mismatch')
    switch (this._typecon) {
      case this.Nil: return list
      case this.Cons:
        this._values = this._values.concat(list._values)
        return this
      default: throw new Error('Cannot form term')
    }
  }
  '!!' (index) {
    if (!testInteger(index)) throw new Error('Type mismatch')
    switch (this._typecon) {
      case this.Nil: return null
      case this.Cons: return index >= this._values.length ? null : this._values[index]
      default: throw new Error('Cannot form term')
    }
  }
}


class Type {
  _typedef = { params: [], indexes: [] }
  _init (...args) {
    let { params, indexes } = this._typedef,
        a = params.findIndex(x => test(x, String)), b = !!indexes.length - 1
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
  }
}


class Vector extends Type {
  _typedef = { params: ['Function'], indexes: ['Number'] }
  constructor (...args) {
    super()
    this._init(...args)
    return this
  }
  get Nil () {
    let elemType = this._typedef.params[0].Function
    return class Nil extends Vector {
      _typecon = this.Nil
      _type = [Vector]
      _values = []
      constructor () {
        super(elemType, 0)
        return this
      }
    }
  }
  get Cons () {
    let { _values } = this,
        elemType = this._typedef.params[0].Function,
        length = this._typedef.indexes[0].Number
    return class Cons extends Vector {
      _typecon = this.Cons
      _type = [elemType, Vector, Vector]
      _values = _values.slice()
      constructor (value) {
        super(elemType, length + 1)
        this._values.unshift(value) // "Builtin"
        return this
      }
    }
  }
  nil () {
    return new this.Nil()
  }
  cons (value) {
    return new this.Cons(value)
  }
  concat (vector) {
    if (!test(vector, Vector) || this._typedef.params[0].Function !== vector._typedef.params[0].Function) throw new Error('Type mismatch')
    let _type = (a, i, j) => [[Vector, a, i], [Vector, a, j], [Vector, a, i + j]]
    switch (this._typecon) {
      case this.Nil: return list
      case this.Cons:
        this._typedef.indexes[0].Number += vector._typedef.indexes[0].Number
        this._values = this._values.concat(vector._values)
        return this
      default: throw new Error('Cannot form term')
    }
  }
  '!!' (index) {
    let elemType = this._typedef.params[0].Function,
        length = this._typedef.indexes[0].Number,
        _type = [[Vector, elemType, length], Number, elemType]
    if (!testInteger(index)) throw new Error('Type mismatch')
    switch (this._typecon) {
      case this.Nil: return null
      case this.Cons: return index >= this._typedef.indexes[0].Number ? null : this._values[index]
      default: throw new Error('Cannot form term')
    }
  }
  uncons () {
    switch (this._typecon) {
      case this.Cons: return
    }
  }
}

var Reason = {
  Vector: {
    concat (vector1, vector2) {
      if (!test(vector1, Vector) || !test(vector2, Vector) ||
        vector1._typedef.params[0].Function !== vector1._typedef.params[0].Function) throw new Error('Type mismatch')
      let elemType = vector1._typedef.params[0].Function,
          len1 = vector1._typedef.indexes[0].Number,
          len2 = vector2._typedef.indexes[0].Number,
          _type = [[Vector, elemType, len1], [Vector, elemType, len2], [Vector, elemType, len1 + len2]]
      switch (this._typecon) {
        case this.Nil: return list
        case this.Cons:
          this._typedef.indexes[0].Number += len2
          this._values = this._values.concat(vector._values)
          return this
        default: throw new Error('Cannot form term')
      }
    }
  }
}


class Nat extends Type {
  zero () { return new this.Zero() }
  get Zero () {
    return class Zero extends Nat {
      _typecon = this.Zero
      _type = [Nat]
      _value = 0
    }
  }
  succ () { return new this.Succ() }
  get Succ () {
    let { _value } = this
    return class Succ extends Nat {
      _typecon = this.Succ
      _type = [Nat, Nat]
      _value = _value + 1
    }
  }
  valueOf () { return this._value }
}
