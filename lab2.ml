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

let rec mergeList g delta = match delta with
| [] -> g
| x::xs -> if(mem x g) then (mergeList g xs) else (mergeList (g@[x]) xs)
;;

let rec pad (proof, delta) = match proof with
| Axiom (g, p, a) -> Axiom((mergeList g delta), p, a)
| ModusPonus (g, p, left, right) -> ModusPonus((mergeList g delta), p, pad(left, delta), pad(right, delta))
;;

let rec minimalGaama proof = match proof with
| Axiom (g, p, a) -> (match a with
					| Ass -> g
					| _ -> [])
| ModusPonus (g, p, left, right) -> mergeList (minimalGaama left) (minimalGaama right)
;;

let rec setGamma minGaama proof = match proof with
| Axiom (g, p, a) -> Axiom(minGaama, p, a)
| ModusPonus (g, p, left, right) -> ModusPonus(minGaama, p, (setGamma minGaama left), (setGamma minGaama right))
;;

let prune proof = let minGaama = minimalGaama proof in
					setGamma minGaama proof
				;;

exception Wronggraft;;

let rec findProp prop prooflist = match prooflist with
| [] -> raise Wronggraft
| x::xs -> (match x with
			| Axiom (g, p, a) -> if(prop=p) then x else (findProp prop xs)
			| ModusPonus (g, p, left, right) -> if(prop=p) then x else (findProp prop xs))
;;

let rec graftAndReplace proof prooflist finGaama = match proof with
| Axiom (g, p, a) -> (match a with
					| Ass -> (findProp p prooflist)
					| _ -> Axiom (finGaama, p, a))
| ModusPonus (g, p, left, right) -> ModusPonus (finGaama, p, 
									(graftAndReplace left prooflist finGaama),
									(graftAndReplace right prooflist finGaama))
;;

let graft proof prooflist = let finGaama = (match (hd prooflist) with
											| Axiom (g, p, a) -> g
											| ModusPonus (g, p, left, right) -> g) in
							graftAndReplace proof prooflist finGaama
							;;
exception NotInList;;
exception ModusPonusViolation;;

let rec removeFromList l a = match l with
| [] -> raise NotInList
| x::xs -> if(x=a) then xs else x::(removeFromList xs a)
;;

let proofPImpliesP gaama p = let q = Impl(p, Impl(L("qfresh"),p)) in
								let r = Impl(p, Impl(Impl(q,p), p)) in
								let kdownpropMP = Impl(q, Impl(p,p)) in
								let kuppropMP = Impl(r, Impl(Impl(p, Impl(q,p)),Impl(p,p))) in
								let sAxiom = Axiom(gaama, kuppropMP, S(p, Impl(q,p), p)) in
								let kupAxiom = Axiom(gaama, r, K(p, Impl(q,p))) in
								let leftSubtree = ModusPonus(gaama,kdownpropMP,sAxiom,kupAxiom) in
								let rightSubTree = Axiom(gaama, q, K(p, L("qfresh"))) in
								ModusPonus(gaama, Impl(p,p), leftSubtree, rightSubTree)
							;;

let rec dedthmreal proof p trimmedGaama = match proof with
| Axiom (g, q, a) ->if (q=p) 
					then (proofPImpliesP trimmedGaama p) 
					else (
						let leftSubtree = Axiom (trimmedGaama, Impl(q, Impl(p, q)), K (q, p)) in
						let rightSubTree = Axiom (trimmedGaama, q, a) in
						ModusPonus(trimmedGaama, Impl(p, q), leftSubtree, rightSubTree)
					)
						
| ModusPonus (g, q, left, right) -> if (q=p) 
									then (proofPImpliesP trimmedGaama p)
									else (
										let leftDerivedProof = (dedthmreal left p trimmedGaama) in
										let rightDerivedProof = (dedthmreal right p trimmedGaama) in
										let r = (match (extractProp left) with
												| Impl(rmatch, qmatch) -> rmatch
												| _ -> raise ModusPonusViolation) in
										let sLeftPartTree = Axiom(trimmedGaama, (generateS p r q), (S(p, r, q))) in
										let finLeft = ModusPonus(trimmedGaama, Impl(Impl(p,r),Impl(p,q)),sLeftPartTree, leftDerivedProof) in
										ModusPonus(trimmedGaama, Impl(p,q), finLeft, rightDerivedProof)
									) 
								;;
let dedthm proof p = match proof with
| Axiom (g, p, a) -> dedthmreal proof p (removeFromList g p)
| ModusPonus (g, p, left, right) -> dedthmreal proof p (removeFromList g p)
;;



