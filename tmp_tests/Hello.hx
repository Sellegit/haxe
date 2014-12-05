package ;

interface IHello {
  function sayHi(name: String): String;
}

interface IHelloT<T> extends IHello {
  function identity(t: T): T;
}

class Hello implements IHello {
  public function sayHi(name: String): String {
    return 'hi $name';
  }
	public static function allSayHi(names: Array<String>): String {
		return 'hi ${names[0]}';
	}
  public static function main() {

  }
  public static function identityStaticAnyways<T>(t: T): T {
    return t;
  }
  public function identityAnyways<T>(t: T): T {
    return t;
  }
}

class SubHello extends Hello implements IHello {
  override public function sayHi(name: String): String {
    return 'subhi $name';
  }
}

class SubHelloT<T> extends SubHello implements IHelloT<T> {
  public function identity(t: T): T {
    return t;
  }
  public static function subIdentityStaticAnyways<T>(t: T): T {
    return t;
  }
}

class Guid
{
  public static function generate():String
  {
    var result = "";
    for (j in 0...32) {
      if ( j == 8 || j == 12|| j == 16|| j == 20) {
        result += "-";
      }
      result += std.StringTools.hex(Math.floor(Math.random()*16));
    }
    return result.toUpperCase();
  }
}
