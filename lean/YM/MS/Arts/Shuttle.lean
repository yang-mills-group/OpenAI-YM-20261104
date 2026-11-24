import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Pilot
/-!
# Pilot: finite-point operators, project orth covariance and color

Mass-compatible (comm tree/trc), use Silo. No volume equality needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts.Pilot
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open scoped Topology ContDiff InnerProductSpace
variable {A B R P:Type}[Fintype A][CommRing R][AddCommGroup P]{p: Koszul.Sector A}{b c:Bool}
variable {K:Pilot R P p}{K' L':Flux A P R}{F H: Row A P R} {s: Finset P}{i:P}
def Transport (K:Pilot R P p)(X Y:Flux A P R): Prop:=∀ i a b, Y a b (K.volp i)= ∑ c,∑ d,X c d i*K.fieldC c a*K.fieldC d b
namespace Transport
variable (h:Transport K K' L')
include h
lemma trimX (s:Finset P): Transport K (trim s K') (trim (s.map K.volp.toEquiv.toEmbedding) L'):= by
    intro i a b; by_cases hp:i∈s; · simp [trim,h .., hp]
    simp [trim,hp]
omit h in
private lemma ride_pair (F) (i j:A)(q:P): diffPair (i,q) (j,-q) (beam K F)=∑ a,∑ b, (K.fieldC i a*K.fieldC j b) • beam K (diffPair (a,K.volp q) (b,-K.volp q) F):= by
    simp_rw [diffPair_apply,served,map_sum,map_smul,served,Finset.smul_sum,smul_smul,map_neg]
-- #goal names
lemma shuttle0 (q:P)(F): beam K (trc L' (K.volp q) F)=trc K' q (beam K F):= by
    simp_rw [trc,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,h q, Finset.sum_smul,ride_pair (K:=K) F, Finset.smul_sum, smul_smul,mul_assoc]; rw [summ_sum]
lemma shuttleS (q:Finset P)(F): beam K (slab L' (q.map K.volp.toEquiv.toEmbedding) F)=slab K' q (beam K F):= by simp [slab,LinearMap.sum_apply,Finset.sum_map,shuttle0 h]
-- commute link trim.
lemma linkR (hF: Conserved F)(i: Finset P)(hx:closed K' p b)(ht:closed L' p b)(H:Row A P R): beam K (tree p (trim (i.map K.volp.toEquiv.toEmbedding) L') F H)= tree p (trim i K') (beam K F) (beam K H):= by
    have he : Conserved (beam K F):= by
       intro l hl; rw [offset K _ 0 (net l) l (fun i hi=> hF i (fun hv=> hl ( K.volp.injective ((hi.symm.trans hv).trans (map_zero _).symm)))) rfl,map_zero]; rfl

    rw [stickT ht _ hF, stickT hx _ he]; unfold link; rw [map_sub, map_sub,circle_prod,← beam_sign, (trimX h i).shuttleS, circle_prod, (trimX h i).shuttleS,circle_prod,(trimX h i).shuttleS] -- maybe circle twice
omit h in
lemma event (K:Pilot R P p){V:B→ Row A P R}{f:Filter B}(h : ∀ i, ∀ᶠ u in f, V u i=F i)(k:Legs (Mode A P)): ∀ᶠ u in f, beam K (V u) k=beam K F k:= by
    induction k generalizing F V with
    | nil=> simpa using h []
    | cons i l ih=> simp_rw [met]; apply finadd; intro j hj; filter_upwards [ih (V:=fun i'=> D (j,K.volp i.2) (V i')) (F:= D (j,K.volp i.2) F) (fun k=> h _)] with t ht; rw [ht]
set_option maxHeartbeats 600000 in
lemma gatherR (F H)(hx:closed K' p b)(hv:closed L' p b): beam K (tree p L' F H)=tree p K' (beam K F) (beam K H):= by
    have hs : ∀ i: Finset P, beam K (tree p (trim (i.map K.volp.toEquiv.toEmbedding) L') F H)=tree p (trim i K') (beam K F) (beam K H):= fun i=> by simpa only [net_beam,tree_trans] using linkR h (trans_off F) i hx hv H
    ext l
    have HT: Tendsto (fun i:Finset P=> i.map K.volp.toEquiv.toEmbedding) atTop atTop := by
        classical
        refine tendsto_atTop.mpr fun w=>?_ ; filter_upwards [eventually_ge_atTop (w.map K.volp.symm.toEquiv.toEmbedding)] with i hi y hy; exact Finset.mem_map.mpr ⟨K.volp.symm y, hi (Finset.mem_map_of_mem K.volp.symm.toEquiv.toEmbedding hy), K.volp.apply_symm_apply y⟩
    obtain ⟨i,ht,hU⟩:= ((roll_tree p (beam K F) (beam K H) K' l).and (event K (F:=tree p L' F H) (V:=fun i:Finset P=>tree p (trim (i.map K.volp.toEquiv.toEmbedding) L') F H) (fun w=>HT.eventually (roll_tree p F H L' w)) l)).exists; rw [← ht,← hU, hs] -- rw hs all i?
end Transport
end YM.MS.Arts.Pilot
