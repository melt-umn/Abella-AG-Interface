grammar expanded_sec:security;

imports expanded_sec:host;

synthesized attribute level::SecurityLevel;
synthesized attribute levels::[SecurityLevel];
synthesized attribute isSecure::Boolean;
synthesized attribute secCtx_out::[(String, SecurityLevel)];
inherited attribute secCtx::[(String, SecurityLevel)];
inherited attribute pc::SecurityLevel;
--[(fun name, starting security level, return security level, param security levels)]
inherited attribute funSecCtx::[(String, SecurityLevel, SecurityLevel, [SecurityLevel])];
