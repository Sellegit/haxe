package ;

class Hello {
  function sayHi(name: String): String {
    return 'hi $name';
  }
	static function allSayHi(names: Array<String>): String {
		return 'hi ${names.join(" and ")}';
	}
  static function main() {

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
