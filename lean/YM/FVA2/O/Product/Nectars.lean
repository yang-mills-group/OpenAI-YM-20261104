import YM.FVA2.O.Product.Glue
/-!
# Integrated second-order bracket and angular offset price symbol
Continuum, B0 true covered. Need for QR contact suppression.
Adapted from Breeze.Wine. No compare unintegrable cuts.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff
open scoped Topology ContDiff
variable {G:Gauge}{x y:Law G}{t:Bool}{a b:QP}{U:Edge G}
local notation "Ψ"=> Lifting.sense G
local infix:70 " ⋄ " => product (field Landau.parity)
abbrev crossF (U:Edge G)(t:Bool): Pair ( Law G ) := tokenL (Heat.orbit U planeF) t (field Landau.parity)
lemma buys (h:Rolled U)(hx:x∈ Wallet G)(he: y∈ Wallet G): SatP planeF U x y a:= by obtain ⟨d,hD,hW⟩:= Job.funds Unit Geo.Coherent; exact priceP h ( Latch.Lease.highp ( show Latch.Lease _ _ _ _ _ from hx ) ) ( Latch.Lease.highp ( show Latch.Lease _ _ _ _ _ from he ) ) hW () a
lemma supplier (h:Rolled U)(hx:x∈ Wallet G)(ht:y∈ Wallet G)(hp:Pure (field Landau.parity) false x)(l: Legs (Lane4 G)) : Integrable (fun p=> link (trc U p) t (field Landau.parity) x y l) planeF ∧ crossF U t x y l= ∫ p, link (trc U p) t (field Landau.parity) x y l∂planeF:= by
    have h1:= (cycle_map planeF _ (buyer y) l (h.pays Geo.Coherent hx)); have h2:=(cycle_map planeF _ (seller x) l ( h.pays Geo.Coherent ht )); obtain h3:= h.pays Geo.Coherent ( Wallet.product hx ht ) l; simp only [crossF,tokenL,LinearMap.coe_mk,AddHom.coe_mk,link,hp.signs,cross_false',one_smul,Pi.sub_apply]; rw [finite_cc planeF (h.pays Geo.Coherent ( Wallet.product hx ht )), finite_cc planeF (h.pays Geo.Coherent hx), finite_cc planeF (h.pays Geo.Coherent ht)]; refine ⟨ (h3.sub h1.1).sub h2.1, ?_⟩; rw [integral_sub (show Integrable (fun p=> trc U p (x ⋄ y) l- (trc U p x ⋄ y) l) planeF from h3.sub h1.1) h2.1,integral_sub h3 h1.1,h1.2,h2.2]
abbrev hail (F H:Law G)(U:Edge G)(i j:BH G)(l r:Legs ( Lane4 G ))(p:QP) : ℂ:= (2:ℂ)⁻¹ * meshZ U i j F H l r p
lemma hail' (h:Reverse U Landau.parity)(i j:BH G)(p:QP)(l r:Legs (Lane4 G)): hail x y U j i l r (-p)= U i j p * ( Koszul.D (j,-p) (Koszul.sign Ψ (Landau.parity i) x) l * Koszul.D (i,p) y r ):= by
    unfold hail meshZ; rw [h]; simp_rw [at_D,at_sign,degree_cons,neg_neg ]; rw [show Lifting.sense G (j,-p)= Landau.parity j from rfl,cross_right (Landau.parity i) (Landau.parity j) (degree Ψ l) (R:=ℂ)]; unfold Lifting.sense; simp only [cross_comm (Landau.parity j) (Landau.parity i)]; ring
abbrev hailS (F H:Law G)(U:Edge G)(i j:BH G)(p:QP)(l r:Legs (Lane4 G)) := hail F H U i j l r p+ hail F H U j i l r (-p)
lemma hail_spec (h:closed U Landau.parity t)(hr:Reverse U Landau.parity)(w:List (Lane4 G))(i j:BH G)(p:QP): U i j p* link (diffPair (i,p) (j,-p)) t (field Landau.parity) x y w = scatter (field Landau.parity) w (hailS x y U i j p):= by
    let V:= Lifting.sense G; let F:= x; let H:= y; have he : hailS F H U i j p=fun l r=> U i j p • (Koszul.sign V (Landau.parity j) (Koszul.D (i,p) F) l* D (j,-p) H r+D (j,-p) (Koszul.sign V (Landau.parity i) F) l * Koszul.D ( i,p ) H r):= funext fun l=> funext fun r=> by rw [ hailS, hail' hr, hail,meshZ ]; simp only [smul_eq_mul,at_sign,at_D]; ring
    rw [he]; let Q:= allocate ( Lifting.sense G ) w ( R:=ℂ ); by_cases hp:U i j p=0; · rw [hp,zero_mul]; simp_rw [zero_smul]; exact (Q.map_zero)|>.symm
    rw [ link_pair (p:=field Landau.parity) (i,p) (j,-p) ( h i j p hp ) x y,Pi.add_apply, scattered, scattered ]; rw [mul_add]; change (U i j p) • Q _+ (U i j p) • Q _=Q _; rw [← map_smul, ← map_smul, ← map_add ]; congr 1; ext1; rename_i u; ext1 v; exact ( mul_add (U i j p) _ _ )|>.symm
lemma haled (h:Rolled U)(hp:x∈ Wallet G)(ht:y∈ Wallet G)(i j:BH G)(l r:Legs ( Lane4 G )): Integrable ( hail x y U i j l r ) planeF:= by obtain he:= buys (a:=0) h hp ht i j l r; simp only [pay0,one_mul] at he; exact he.const_mul _
lemma halo (p:QP)(h:closed U Landau.parity t)(hr:Reverse U Landau.parity)(w:Legs ( Lane4 G )) : link (trc U p) t (field Landau.parity) x y w=scatter (field Landau.parity) w (∑ i:BH G,∑ j:BH G,hailS x y U i j p):= by unfold trc; simp_rw [ link_sum,link_scale, Finset.sum_apply,Pi.smul_apply ]; rw [ show scatter (field Landau.parity) w (∑ i:BH G,_) =_ from map_sum ( allocate Ψ w ( R:=ℂ ) ) _ _ ]; simp_rw [ map_sum ]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> hail_spec h hr w i j p ))
lemma mandate (h:Rolled U)(hr:Reverse U Landau.parity)(hh:closed U Landau.parity t)(hp:x∈ Wallet G)(ht:y∈ Wallet G)(hf:Pure (field Landau.parity) false x): crossF U t x y=Cabin 0 U planeF x y:= by
    funext w; let L(p:QP):=∑ i:BH G,∑ j:BH G,hailS x y U i j p; have hg(a b: Legs (Lane4 G))(i j:BH G): Integrable (fun q=>hailS x y U i j q a b) planeF:= ( haled h hp ht i j a b ).add ((haled h hp ht j i a b).comp_neg )
    have he (l r:Legs (Lane4 G)): Integrable (fun p=> L p l r ) planeF:= by simp_rw [ L,Finset.sum_apply ]; exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> hg l r i j))
    obtain hL:= (scatter_integral planeF (f:=L) Ψ w (fun a b _=> he a b)).2; rw [( supplier h hp ht hf w ).2 ]; simp_rw [halo _ hh hr]; rw [hL]; unfold Cabin; refine scatter_congr _ _ _ _ (fun a b he'=>?_); simp_rw [ pay0,one_mul ]; unfold L; simp_rw [Finset.sum_apply]; rw [ integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=> hg a b i j)) ]; simp_rw [show ∀ i:BH G,(∫ p,∑ j:BH G,hailS x y U i j p a b∂planeF) = _ from fun i=> integral_finsetSum _ (fun j _=> hg a b i j) ]; simp_rw [hailS, show ∀ i j:BH G,(∫ p,hail x y U i j a b p+hail x y U j i a b (-p)∂planeF)= (∫ p,hail x y U i j a b p∂planeF)+(∫ p,hail x y U j i a b p∂planeF) from fun i j=> by rw [integral_add ( haled h hp ht i j a b ) ( (haled h hp ht j i a b).comp_neg ),integral_neg_eq_self],hail, integral_const_mul, Finset.sum_add_distrib, ← Finset.mul_sum ]; nth_rw 2 [ Finset.sum_comm ]; ring
lemma tension (h:Rolled U)(hr:Reverse U Landau.parity)(hh:closed U Landau.parity t)(hp:x∈ Wallet G)(ht:y∈ Wallet G)(hf:Pure (field Landau.parity) false x)(a b:QP): crossF U t ( chair G a x ) ( chair G b y ) = chair G b (Cabin ( a-b ) U planeF x y):= by
    have he(i j:BH G)(l r:Legs (Lane4 G))(p:QP): meshZ U i j (chair G a x) (chair G b y) l r p = Tone.bill a (net l)*Tone.bill b (net r)*(Tone.bill (a-b) p * meshZ U i j x y l r p):= by simp only [ meshZ,seated,net_cons,Tone.rightadd,Tone.inverse,netπ ]; ring
    rw [ mandate h hr hh ( chair_v a hp ) ( chair_v b ht ) (( chair_p a ( hp:= (show x∈ Roof G from ⟨hp,hf⟩) ) ).2) ]; funext w; unfold Cabin; rw [seated]; let Q:= allocate Ψ w ( R:=ℂ ); change Q _= Tone.bill b (net w) • Q _; rw [ ← map_smul ]; apply scatter_congr; intro u v hs; simp_rw [ Tone.pay0,one_mul,he, integral_const_mul, ← Finset.mul_sum ]; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul,← split_net hs,Tone.rightadd, netπ ]; field_simp [ nonz ]
end YM.FVA2.O.Serve
