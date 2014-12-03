@:framework("Foundation")
extern class Concurrency {

	@:c public static function dispatch_get_global_queue (a:Int, b:Int) :Void;
	@:c public static function dispatch_get_main_queue () :Void;
	@:c public static function dispatch_queue_create () :Void;
	@:c public static function dispatch_get_current_queue () :Void;
	@:c public static function dispatch_queue_get_label () :Void;
	@:c public static function dispatch_set_target_queue () :Void;
	@:c public static function dispatch_main () :Void;
	
	@:c public static function dispatch_async (queue:Void, func:Void->Void) :Void;
}
