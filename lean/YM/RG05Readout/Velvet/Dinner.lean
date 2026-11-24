import YM.RG05Readout.Pulse.Excursion
import YM.MSbar.UV.Compact
/-!
Commuting smooth center payments with true field read costs. Use only
 abstract parameter integral lemma MSbar.High on real/complex smooth functions,
 no importing scheme assumptions from that library. Preserve normalization as
 ACTUAL full test function with centered child profiles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Analysis Function MeasureTheory Set Filter Topology Pulse Native
open scoped Topology ContDiff BigOperators Classical
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
set_option quotPrecheck false
local notation "Z"=>Complexion X
abbrev Savors (w:E4→ Complexion X) := ContDiff ℝ ∞ (fun z:X×E4=> (w z.2).val z.1)
section
variable {w:E4→ Complexion X}(h:Savors w) {I: Set E4}(hp:IsCompact I)
include h
noncomputable def dine (h:Savors w)(hp:IsCompact I): Complexion X :=⟨_, MSbar.High.section_smooth (μ:=volume) h hp⟩
lemma diner (x): (dine h hp).val x=∫ y in I,(w y).val x:=rfl
-- under repeated directional partial smooth fees
omit [FiniteDimensional ℝ X] in
lemma smoothT (u:X) (n:ℕ): Savors (fun x=> tires u n (w x)):=by
    unfold Savors; simp_rw [rim_flat]; let F(z:X×E4):= (w z.2).val z.1; let L:= ContinuousMultilinearMap.apply ℝ (fun _ : Fin n=>X) ℂ (fun _=>u)
    exact L.contDiff.comp (MSbar.High.leaf_cont (f:=F) h)
lemma rimT (u:X) (n:ℕ): tires u n (dine h hp)= dine (smoothT h u n) hp:=by
    apply Subtype.ext; funext x
    let F(z:X×E4):=(w z.2).val z.1; have ht:ContDiff ℝ ∞ F:=h
    have hv := MSbar.High.under_leaf (U:=I) (μ:=volume) (n:=n) (x:=x) ht hp
    rw [rim_flat]; change (iteratedFDeriv ℝ n (MSbar.High.sectionL F I volume) x) (fun _=>u)= (∫ y in I, (tires u n (w y)).val x); rw [hv,ContinuousMultilinearMap.integral_apply]; rotate_left
    · apply ContinuousOn.integrableOn_compact hp; exact ((MSbar.High.leaf_cont (n:=n) ht).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    simp_rw [rim_flat]; rfl
omit h
omit [FiniteDimensional ℝ X] in
lemma Smoothsum {ι:Type*} (s: Finset ι) (Q:ι→E4→ Complexion X)(hS:∀ i∈s,Savors (Q i)) : Savors (fun x=>∑ i∈s, Q i x):=by
   unfold Savors; simp_rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]; exact ContDiff.sum (f:=fun i (z:X×E4)=>(Q i z.2).val z.1) hS -- name check
include h
omit [FiniteDimensional ℝ X] in
lemma Smoothsmul (c:ℂ): Savors (fun x=> c • w x):= h.const_smul c
lemma Dinesmul (c:ℂ) : c • dine h hp = dine (Smoothsmul h c) hp:=Subtype.ext (funext fun x=> (integral_smul c (fun y=> (w y).val x)).symm)
include hp in
omit [FiniteDimensional ℝ X] in
lemma livesX (x:X) : IntegrableOn (fun y:E4=>(w y).val x) I := (h.continuous.comp ((continuous_const (y:=x)).prodMk continuous_id)).continuousOn.integrableOn_compact hp
omit h
lemma Dinesum {ι:Type*} (s: Finset ι)(Q:ι→E4→ Complexion X)(p:ι→ Complexion X)(hS:∀ i∈s,Savors (Q i))(hP:∀ i:ι,∀ hi:i∈s, p i = dine (hS i hi) hp) : ∑ i∈s,p i = dine (Smoothsum s Q hS) hp:=by
   apply Subtype.ext; funext x; simp_rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,diner,AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]; rw [integral_finsetSum s (fun i hi=> livesX (hS i hi) hp x)] ; exact Finset.sum_congr rfl (fun i hi=>by rw [hP i hi,diner])
variable {d:ℕ}
include h
omit [FiniteDimensional ℝ X] in
lemma Smoothlat (k:Letter d)(i:E4→X): Savors (fun y=> lat k i (w y)):=by
   unfold lat; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]; exact Smoothsum (paint k) (fun j x=>ink k j • tires (i j) _ (w x)) (fun j _=>Smoothsmul (smoothT h _ _) _)
lemma Dines (k:Letter d)(i:E4→X): lat k i (dine h hp)= dine (Smoothlat h k i) hp:=by
   generalize_proofs hw; unfold lat at *; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply] at *
   apply Dinesum hp (paint k) (fun j x=> ink k j • tires (i j) _ (w x)) _ (fun j _=>Smoothsmul (smoothT h _ _) _)
   intro j _; rw [rimT]; exact Dinesmul ..
omit [FiniteDimensional ℝ X] in
lemma SmoothFork (x:X)(r:ℝ): Savors (fun y=> fork r x (w y)):= h.comp ((contDiff_const.add (contDiff_fst.const_smul r)).prodMk contDiff_snd)
lemma DineFork (x:X)(r:ℝ): fork r x (dine h hp)= dine (SmoothFork h x r) hp:=rfl
end
section
variable {V:Type}[Fintype V][DecidableEq V]{F:E4→Wave V}{I:Set E4}(hw:Savors F)(hp:IsCompact I)(s:V→ℕ)(k:∀ i:V,Letter (s i))
include hw
lemma moving (L:List V): Savors (fun x=> machine s k L (F x)):=by induction L generalizing F with|nil=>exact hw|cons i L ih=> exact ih (Smoothlat hw (k i) fun u=>Pi.single i u)
lemma meals (L:List V) : machine s k L (dine hw hp)=dine (moving hw s k L) hp:=by induction L generalizing F with| nil=> rfl| cons i L ih=> 
      let h:= Smoothlat hw (k i) fun u=> Pi.single i u
      exact Eq.trans (congr_arg (machine s k L) (Dines hw hp (k i) _)) (ih h)
end
end YM.RG05Readout.Velvet
