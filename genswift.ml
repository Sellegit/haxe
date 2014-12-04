open Ast
open Type
open Common
open Gencommon
open Gencommon.SourceWriter

exception SwiftEx of string

let module_type_path t =
		match t with
		| TClassDecl cl ->
			let (ns, n) = cl.cl_path in
			(String.concat "." (ns @ [n]))
		| TEnumDecl e ->
			let (ns, n) = e.e_path in
			(String.concat "." (ns @ [n]))
		| TTypeDecl d ->
			let (ns, n) = d.t_path in
			(String.concat "." (ns @ [n]))
		| TAbstractDecl a ->
			let (ns, n) = a.a_path in
			(String.concat "." (ns @ [n]))

let module_type_type t =
	match t with
		| TClassDecl _ -> "TClassDecl"
		| TEnumDecl _ -> "TEnumDecl"
		| TTypeDecl _ -> "TTypeDecl"
		| TAbstractDecl _ -> "TAbstractDecl"

let module_type_s t =
	(module_type_type t) ^ " " ^ (module_type_path t)
	
let to_real_path s =
	match s with
		| "Void" -> "()"
		| _ -> s
	
let rec module_type_ps_s md_t ps =
	(match ps with
		| [] -> to_real_path (module_type_path md_t)
		| _ ->
			let s = String.concat ", " (List.map type_s ps) in
			(to_real_path (module_type_path md_t)) ^ "<" ^ s ^ ">")

and type_s t =
	match t with
		| TMono t ->
			(match !t with
				| Some mt -> type_s mt
				| None -> "$TMono")
		| TEnum(e, ps) ->
			module_type_ps_s (TEnumDecl e) ps
		| TInst(cl, ps) ->
			module_type_ps_s (TClassDecl cl) ps
		| TType(d, ps) ->
			module_type_ps_s (TTypeDecl d) ps
		| TFun(args, ret) ->
			"$TFun"
		| TAnon a ->
			"$TAnon"
		| TDynamic t ->
			"$TDynamic"
		| TLazy t -> 
			"$TLazy"
		| TAbstract(a, ps) ->
			module_type_ps_s (TAbstractDecl a) ps
			
let unwrap_paren e =
	match e.eexpr with
		| TParenthesis e' -> e'
		| _ -> e
		
let configure gen =

	let begin_block w = write w "{"; push_indent w; newline w; in
	let end_block w = pop_indent w; (if w.sw_has_content then newline w); write w "}"; newline w; in
	
	let write_id w name = write w name in
	let write_field w name = write w name in

	let escape ichar b =
		match ichar with
			| 92 (* \ *) -> Buffer.add_string b "\\\\"
			| 39 (* ' *) -> Buffer.add_string b "\\\'"
			| 34 -> Buffer.add_string b "\\\""
			| 13 (* \r *) -> Buffer.add_string b "\\r"
			| 10 (* \n *) -> Buffer.add_string b "\\n"
			| 9 (* \t *) -> Buffer.add_string b "\\t"
			| c when c < 32 || (c >= 127 && c <= 0xFFFF) -> Buffer.add_string b (Printf.sprintf "\\u%.4x" c)
			| c when c > 0xFFFF -> Buffer.add_string b (Printf.sprintf "\\U%.8x" c)
			| c -> Buffer.add_char b (Char.chr c)
	in

	let escape s =
		let b = Buffer.create 0 in
		(try
			UTF8.validate s;
			UTF8.iter (fun c -> escape (UChar.code c) b) s
		with
			UTF8.Malformed_code ->
				String.iter (fun c -> escape (Char.code c) b) s
		);
		Buffer.contents b
	in

	let in_value = ref false in
	
	let in_function_decl = ref false in

	let expr_s w e =
		in_value := false;
		let rec expr_s w e =
			let was_in_value = !in_value in
			let was_in_function_decl = !in_function_decl in
			in_function_decl := false;
			in_value := true;
			(match e.eexpr with
				| TConst c ->
					(match c with
						| TInt i32 ->
							write w (Int32.to_string i32);
						| TFloat s ->
							write w s;
							(if String.get s (String.length s - 1) = '.' then write w "0");
						| TString s ->
							write w "\"";
							write w (escape s);
							write w "\""
						| TBool b -> write w (if b then "true" else "false")
						| TNull -> write w "nil"
						| TThis -> write w "self"
						| TSuper -> write w "super")
				| TLocal v -> write_id w v.v_name
				| TArray(e1, e2) ->
					(* array access e1[e2] *)
					write w "TArray"
				| TBinop(op, e1, e2) ->
					expr_s w e1;
					write w (" " ^ (Ast.s_binop op) ^ " ");
					expr_s w e2
				| TField(e, fa) ->
					expr_s w e;
					write w ".";
					write_field w (field_name fa)
				| TTypeExpr(md_t) ->
					(match md_t with
						| TClassDecl cl -> write w (type_s (TInst(cl, List.map (fun _ -> t_dynamic) cl.cl_params)))
						| TEnumDecl en -> write w (type_s (TEnum(en, List.map (fun _ -> t_dynamic) en.e_params)))
						| TTypeDecl td -> write w (type_s (gen.gfollow#run_f (TType(td, List.map (fun _ -> t_dynamic) td.t_params))))
						| TAbstractDecl a -> write w (type_s (TAbstract(a, List.map (fun _ -> t_dynamic) a.a_params)))
					)
				| TParenthesis e ->
					write w "("; expr_s w e; write w ")"
				| TObjectDecl ses -> 
					write w "TObjectDecl"
				| TArrayDecl es ->
					write w "TArrayDecl"
				| TCall(e, es) ->
					expr_s w e;
					write w "(";
					List.iteri (fun idx e ->
						expr_s w e;
						if idx < List.length es - 1 then write w ", ") es;
					write w ")"
				| TNew(cl, ps, es) ->
					write w "TNew"
				| TUnop(op, flag, e) ->
					(match flag with
						| Ast.Prefix -> write w ( " " ^ (Ast.s_unop op) ^ " (" ); expr_s w e; write w ") "
						| Ast.Postfix -> write w "("; expr_s w e; write w (") " ^ Ast.s_unop op))
				| TFunction f ->
					write w "TFunction"
				| TVar (v, e_op) ->
					write w "var ";
					write_id w v.v_name;
					print w ": %s" (type_s v.v_type);
					(match e_op with
						| None ->
							write w " = ";
							expr_s w (null v.v_type e.epos)
						| Some e ->
							write w " = ";
							expr_s w e
					);
					newline w
				| TBlock(es) ->
					if not was_in_function_decl then write w "locally ";
					begin_block w;
					List.iter (expr_s w) es;
					end_block w
				| TFor(v, e1, e2) ->
					write w "TFor"
				| TIf(econd, ethen, eelse_op) ->
					write w "if ";
					expr_s w (unwrap_paren econd);
					write w " ";
					in_value := false;
					in_function_decl := true;
					expr_s w (mk_block ethen);
					(match eelse_op with
						| None -> ()
						| Some e ->
							write w "else ";
							in_value := false;
							in_function_decl := true;
							let e = match e.eexpr with
								| TIf _ -> e
								| TBlock [{eexpr = TIf _} as e] -> e
								| _ -> mk_block e
							in
							expr_s w e
					)
				| TWhile(econd, eblock, flag) ->
					(match flag with
						| Ast.NormalWhile ->
							write w "while ";
							expr_s w (unwrap_paren econd);
							write w " ";
							in_value := false;
							in_function_decl := true;
							expr_s w (mk_block eblock)
						| Ast.DoWhile ->
							write w "do ";
							in_value := false;
							in_function_decl := true;
							expr_s w (mk_block eblock);
							write w "while ";
							in_value := true;
							expr_s w (unwrap_paren econd);
					)
				| TSwitch(e, cases, default_op) ->
					write w "TSwitch"
				| TTry(etry, catches) ->
					write w "TTry"
				| TReturn(e_op) ->
					(match e_op with
						| Some e ->
							write w "return ";
							expr_s w e;
							newline w
						| None ->
							write w "return";
							newline w)
				| TBreak ->
					write w "TBreak"
				| TContinue ->
					write w "TContinue"
				| TThrow(e) ->
					write w "TThrow"
				| TCast(e, md_t_op) ->
					write w "TCast"
				| TMeta(meta, e) ->
					write w "TMeta"
				| TEnumParameter(e, ef, i) ->
					write w "TEnumParameter");
			in_value := was_in_value;
			in_function_decl := was_in_function_decl;
		in
		expr_s w e
	in

	let rec gen_class_field w is_static cl cf =
		let static_s = if is_static then "class " else "" in
		let public_s = "" in
		let name_s = cf.cf_name in
		(*Printf.printf "%s\n" (Std.dump cf)*)
		match cf.cf_kind with
			| Method MethNormal ->
				(match cf.cf_type with
					| TFun(args, ret) ->
						let func_s = "func " in
						let args_s = String.concat ", " (List.map (fun (argname, argopt, argt) ->
							argname ^ ": " ^ (type_s argt)
						) args) in
						let ret_s = type_s ret in
						write w (static_s ^ func_s ^ public_s ^ name_s ^ "(" ^ args_s ^ ")" ^ " -> " ^ ret_s ^ " ");
						(*begin_block w;*)
						(match cf.cf_expr with
							| Some e ->
								(match e.eexpr with
									| TFunction f ->
										in_function_decl := true;
										expr_s w f.tf_expr
									| _ -> raise (SwiftEx "why u no TFunction"))
							| None -> ());
						(*end_block w*)
					| _ -> raise (SwiftEx "why u no TFun"))
			| _ -> ()
	in
		
	let gen_class w cl =
    write w ("class " ^ (module_type_path (TClassDecl cl)) ^ " ");
    begin_block w;
  	List.iter (gen_class_field w true cl) cl.cl_ordered_statics;
  	List.iter (gen_class_field w false cl) cl.cl_ordered_fields;
    end_block w
	in

  let gen_enum w e =
  	write w ("enum " ^ (module_type_path (TEnumDecl e)))
	in

	let module_type_gen w md_tp =
		if module_type_path md_tp = "Hello" || module_type_path md_tp = "Guid" then begin
			match md_tp with
				| TClassDecl cl ->
					if not cl.cl_extern then begin
						gen_class w cl;	
						newline w;
						newline w
					end;
					(not cl.cl_extern)
				| TEnumDecl e ->
					if not e.e_extern then begin
						gen_enum w e;
						newline w;
						newline w
					end;
					(not e.e_extern)
				| TAbstractDecl _
				| TTypeDecl _ ->
					false
		end else false
	in
	let module_gen w md_def =
		List.fold_left (fun should md -> module_type_gen w md || should) false md_def.m_types
	in
	init_ctx gen;
	let out_files = ref [] in
	let t = Common.timer "code generation" in
	let parts = Str.split_delim (Str.regexp "[\\/]+") gen.gcon.file in
	mkdir_recursive "" parts;
	generate_modules gen "swift" "src" module_gen out_files;
	t()

let generate com =
	(try
		let gen = new_ctx com in
		configure gen
	with | Not_found ->
		Printf.printf "something not found");
