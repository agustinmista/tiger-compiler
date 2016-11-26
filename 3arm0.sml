(*
	Enteros inmediatos con tres instrucciones para ARM.
*)
fun intabytes n =
	let	fun intabytes' 0 _ r = r
		| intabytes' n b r = intabytes' (n-1) (b div 256) ((b mod 256)::r)
	in	intabytes' 4 n [] end
fun bytesaint b =
	let	fun bytesaint' [] r = r
		| bytesaint' (h::t) r = bytesaint' t (256*r + h)
	in	bytesaint' b 0 end  
fun genarm n =
	case intabytes n of
	[b3, b2, b1, b0] =>
		let	val n' = bytesaint [b3, b2, b3, b2]
			val iw = Word8.fromInt
			val wi = Word8.toInt
			val b1' = Word8.toInt(Word8.xorb(iw b3, iw b1))*256
			val b0' = Word8.toInt(Word8.xorb(iw b2, iw b2))
		in	[
			"mov `d0, "^Int.toString n'^"\n",
			"xor `d0, "^Int.toString b1'^"\n",
			"xor `d0, "^Int.toString b0'^"\n"
			]
		end
	| _ => raise Fail "???"
