/**
 *  An abstract type that represents a Selector.
 *  
 *  Used to generate a native selector in swift
 *  new SEL ( func )  -> @selector(func_signature)
 *  If the function has the @:sel metadata it will be used instead the function signature
 *  
 *  SEL is not generated or referenced in swift sources
 **/
extern class SEL {
	public function new (sel:Dynamic) :Void;
}