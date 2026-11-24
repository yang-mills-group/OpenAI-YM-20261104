import YM.MS.Orbit.Join
/-!
# B_s(t) Vs. Finite tree identities. Exact projection at global P. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{P:Latch.Edge G}{F H: Law G}{n:Side}
    {A: Cover}{x y z: Legs ( FixedMode G n )}
local notation "Z"=> field ( parity ( A:=Axis ) ( C:=G.ColorIndex))
lemma recognize (P:Latch.Edge G)(n:Side) : frame ( mat n P)=slab ( EdgeV n P) univ:= StraightFocus (P:=P) ( fun i j=> diffPair i j (R:=ℂ) ) 
lemma passB (h: Twig P)(X: Than G n): conn Z ( mat n P ) ( Bulk G n F ) X = tree parity ( EdgeV n P ) (Bulk G n F) X:= by
   unfold conn; rw [ recognize ]; exact localize ( edge_cl h.close ) _ (fun _ v=>False.elim ( v ( Finset.mem_univ _ ))) (Gps F n) X
lemma θ_minus (x:Legs (FixedMode G n)): congrQ ( - net ( stage x ) ) (Coord (-net x)):= congrQ.trans ( θ_net x |>.opp ) (ξ_neg ..)
lemma sizeL (i:BH G)(h:Speaks F) : Bulk G n F ((i,-net x)::x)= brightness n * F ((i,-net (stage x))::stage x):= by rw [ bulkZ, if_pos (by simp), point ]; exact congr_arg _ (h _ _ ( .cons ⟨rfl,(θ_minus x).sym⟩ (asc _)))
lemma meet0 (x:Legs (FixedMode G n)) (w:Legs (FixedMode G n))(j:BH G)(h:Speaks H): Vμ H n ((j,net x)::w)=H ((j,net (stage x))::stage w):= by rw [point]; exact h _ _ (.cons ⟨rfl,(θ_net x).sym⟩ (asc _))
lemma source (i j:BH G)(H': Than G n)(c:ℂ)(h: Twig P)(hp:Speaks F)(ht: H' ((j,net x)::y)=c * H ((j,net (stage x))::stage y)): radius parity ( EdgeV n P) i j ( Bulk G n F ) H' x y = c*radius parity P i j F H (stage x) (stage y):= by
   unfold radius; dsimp only; rw [ sizeL i hp, neg_neg,neg_neg,ht ]; unfold EdgeV; rw [ ← h.pin i j (θ_minus x), Λ_d ]; linear_combination (norm:=ring_nf) c*2*P i j (-net (stage x)) *cross (parity j) (degree Z x)* F ((i,-net (stage x))::stage x)* H ((j,net (stage x))::stage y) *(lightW n)
lemma grantS (h:Twig P)(hp:Speaks F)(he:Speaks H)(U:Than G n)(c:ℂ)(hf:∀ l r,Split l r z→∀ j:BH G,U ((j,net l)::r)=c* Vμ H n ((j,net l)::r)): tree parity ( EdgeV n P ) ( Bulk G n F ) U z=c * Vμ ( tree parity P F H ) n z:= by
   unfold tree; rw [ point, scat_δ ]; let T:= allocate Z z ( R:=ℂ ); change T _ = c • T _; rw [ ← map_smul ]; refine scatter_congr _ _ _ _ (fun l r hl=>?_); simp only [Pi.smul_apply,smul_eq_mul,convertR h.t, convertR (edge_rev h.pin h.t),Finset.mul_sum]; exact Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun j _=> source i j _ c h hp ( by rw [hf _ _ hl,meet0 _ _ j he])))
lemma BB (h: Twig P)(hp:Speaks F)(he:Speaks H): conn Z ( mat n P ) ( Bulk G n F ) ( Bulk G n H )= Bulk G n ( tree parity P F H ):= by
   rw [ passB h ]; funext w; rw [ bulkZ ]; by_cases hx:net w=0; swap; · rw [ if_neg hx ]; exact conserved_tree _ _ ( Gps H n ) ( Bulk G n F ) _ hx
   rw [ if_pos hx ]; exact grantS h hp he _ _ (fun l r hr i=> by rw [bulkZ]; simp only [net_cons,split_net hr,hx,if_true]) -- if_true syntax
lemma BM (h:Twig P)(hp:Speaks F)(he:Speaks H): conn Z ( mat n P ) ( Bulk G n F ) ( anchor G n A H ) = anchor G n A ( tree parity P F H ):= by rw [ passB h ]; funext w; rw [ chase_now ]; exact grantS h hp he _ _ (fun l r hr j=> by rw [chase_now]; simp only [net_cons,split_net hr])
end YM.MS.Orbit
