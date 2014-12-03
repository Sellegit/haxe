/*
 * Copyright (c) 2005, The haXe Project Contributors
 * All rights reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   - Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   - Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE HAXE PROJECT CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE HAXE PROJECT CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
 * DAMAGE.
 */
package sys;

import swift.foundation.NSError;
import swift.foundation.NSFileManager;
import swift.foundation.NSFileHandle;


private enum FileKind {
	kdir;
	kfile;
	//kother( k : String );
}

@:coreApi
class FileSystem {
	
	public static function exists( path : String ) : Bool {
		return NSFileManager.defaultManager().fileExistsAtPath(path);
	}
	
	public static function rename( path : String, newPath : String ) : Void {
		var error :NSError = null;
		var success = NSFileManager.defaultManager().moveItemAtPath (path, newPath, error);
		if (!success)
			throw "Could not rename:" + path + " to " + newPath;
	}
	
	public static function stat( path : String ) : FileStat {
		var s : FileStat = null;
		if (s==null)
			return { gid:0, uid:0, atime:Date.fromTime(0), mtime:Date.fromTime(0), ctime:Date.fromTime(0), dev:0, ino:0, nlink:0, rdev:0, size:0, mode:0 };
		s.atime = Date.fromTime(1000.0*(untyped s.atime));
		s.mtime = Date.fromTime(1000.0*(untyped s.mtime));
		s.ctime = Date.fromTime(1000.0*(untyped s.ctime));
		return s;
	}
	
	public static function fullPath( relPath : String ) : String {
		return null;
	}
	
	static function kind( path : String ) : FileKind {
		var isDir :Bool = false;
		NSFileManager.defaultManager().fileExistsAtPath (path, isDir);
		return switch (isDir) {
			case false: kfile;
			case true: kdir;
			//default: kother(k);
		}
	}
	
	public static function isDirectory( path : String ) : Bool {
		var isDir :Bool = false;
		NSFileManager.defaultManager().fileExistsAtPath (path, isDir);
		return isDir;
	}
	
	public static function createDirectory( path : String ) : Void {
		var error :NSError = null;
		var attributes :Dynamic = { NSFilePosixPermissions : 493 };
		var success = NSFileManager.defaultManager().createDirectoryAtPath (path, true, attributes, error);
		if (!success)
			throw "Could not create directory:" + path;
	}
	
	public static function deleteFile( path : String ) : Void {
		var error :NSError = null;
		var success = NSFileManager.defaultManager().removeItemAtPath (path, error);
		if (!success)
			throw "Could not delete file:" + path;
	}
	
	public static function deleteDirectory( path : String ) : Void {
		var error :NSError = null;
		var success = NSFileManager.defaultManager().removeItemAtPath (path, error);
		if (!success)
			throw "Could not delete directory:" + path;
	}
	
	public static function readDirectory( path : String ) : Array<String> {
		//var dir = NSHomeDirectory();
		var de :NSDirectoryEnumerator = NSFileManager.defaultManager().enumeratorAtPath ( path );
		var files :Array<String> = [];
		var file :String = null;
		while ((file = de.nextObject()) != null) files.push ( file );
		return files;
	}
}
