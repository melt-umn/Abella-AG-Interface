grammar expanded_sec:host;

synthesized attribute vars::[String];

synthesized attribute ty::Type;
synthesized attribute tyCtx_out::[(String, Type)];
inherited attribute tyCtx::[(String, Type)];

synthesized attribute value::Value;
synthesized attribute evalCtx_out::[(String, Value)];
inherited attribute evalCtx::[(String, Value)];
