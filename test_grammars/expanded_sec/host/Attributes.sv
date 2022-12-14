grammar expanded_sec:host;

synthesized attribute vars::[String];


synthesized attribute ty::Type;
synthesized attribute tys::[Type];
synthesized attribute tyCtx_out::[(String, Type)];
synthesized attribute wellTyped::Boolean;
inherited attribute tyCtx::[(String, Type)];

inherited attribute funTyCtx::[(String, Type, Params)];
synthesized attribute funTyCtx_out::[(String, Type, Params)];


synthesized attribute value::Value;
synthesized attribute vals::[Value];
synthesized attribute evalCtx_out::[(String, Value)];
inherited attribute evalCtx::[(String, Value)];

synthesized attribute printedOutput::[Value];

--arguments passed to the program, going to the main function
inherited attribute mainArgs::[Value];

--[(fun name, ret name, param names, body)]
inherited attribute funEvalCtx::[(String, String, [String], C)];
