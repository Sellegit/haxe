package haxe.ds;

@:category("NSMutableDictionary") @:coreApi class ObjectMap< K: { }, V > implements Map.IMap<K,V> {
	
	public function new() : Void {
		
	}

	public function get( key : K ) : Null<V> {
		//return untyped this.objectForKey ( key );
		return untyped __swift__("[self objectForKey:[NSString stringWithFormat:@\"%@\",key]]");
	}

	public function set( key : K, value : V ) : Void {
		//untyped this.setObject (value, key);
		untyped __swift__("[self setObject:value forKey:[NSString stringWithFormat:@\"%@\",key]]");
	}

	public function exists( key : K ) : Bool {
		//return untyped this.objectForKey ( key ) != null;
		return untyped __swift__("[self objectForKey:[NSString stringWithFormat:@\"%@\",key]] != nil");
	}

	public function remove( key : K ) : Bool {
		//return untyped this.removeObjectForKey ( key );
		if (exists(key)) {
			untyped __swift__("[self removeObjectForKey:[NSString stringWithFormat:@\"%@\",key]]");
			return true;
		}
		return false;
	}

	public function keys() : Iterator<K> {
		var a:Array<K> = untyped this.allKeys();
		return a.iterator();
	}

	public function iterator() : Iterator<V> {
		var a:Array<Dynamic> = untyped this.allValues();
		return a.iterator();
	}

	public function toString() : String {
		var s = "";
		var it = keys();
		for( i in it ) {
			s += (s == "" ? "" : ",") + Std.string(i);
			s += " => ";
			s += Std.string(get(i));
		}
		return s + "}";
/*		return untyped this.description();*/
	}

}
