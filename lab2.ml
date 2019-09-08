open List;;
type prop = T| F | L of string
			| Not of prop
			| Impl of prop * prop
		;;
type gamma = prop list;;
type axiom = Ass
			| K of prop * prop
			| S of prop * prop * prop
			| R of prop * prop
		;;
type hprooftree = Axiom of gamma * prop * axiom 
				| ModusPonus of gamma * prop * hprooftree * hprooftree
			;;
let generateK p q = Impl(p, Impl(q, p));;
let generateS p q r = Impl(Impl(p, Impl(q, r)), Impl(Impl(p, q),Impl(p, r)));;
let generateR p q = Impl(Impl(Not(p), Not(q)), Impl(Impl(Not(p), q), p));;
let extractProp proof = match proof with
| Axiom(g, p, a) -> p
| ModusPonus(g, p, left, right) -> p
;;
let isValidAxiom g rp a = match a with
| Ass -> mem rp g
| K (p, q) -> let proxyProp = generateK p q in
					rp = proxyProp
| S (p, q, r) -> let proxyProp = generateS p q r in
						rp = proxyProp
| R (p, q) -> let proxyProp = generateR p q in
				rp = proxyProp
				;;

let rec valid_hprooftree proof = match proof with
| Axiom (g, p, a) -> isValidAxiom g p a
| ModusPonus (g, p, left, right) -> let leftProp = extractProp left in
									let rightProp = extractProp right in
									let proxyProp = Impl(rightProp, p) in
									if(leftProp=proxyProp) 
										then((valid_hprooftree left) && (valid_hprooftree right)) 
									else false
								;;