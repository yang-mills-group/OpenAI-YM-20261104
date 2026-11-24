import YM.FVA2.Coupling.Real
import YM.XSpace.Nested
import YM.XSpace.Invariance

/-!
# coupling reexpression before position solve

The positive-order equations use power series of ℝ-linear mixtures of observations. The mixing
is implicit at horizon. Now EXACT explicit formula removing both coupling change and any other
unit-leading bare frame. No size assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.WilsonBridge.Coupling
open Function Finset Set Filter MeasureTheory XSpace Normalize PowerSeries Fray
open Maxwell Maxwell.Free Maxwell.Wick
open scoped Topology BigOperators ContDiff Classical
variable {G: Gauge} {d n k:ℕ}
namespace Key
variable (a:Key) (D : Guard G d) (P: Reports G d)

def gate (D : Guard G d): Guard G d := PowerSeries.mk (a.mix (fun i=> coeff i D))
lemma coeffGate : coeff n (a.gate D) = a.mix (fun i=> coeff i D) n:= coeff_mk ..
lemma taxGate (j: Dime G d)(p:Sec G d) : tax (a.gate D) p j=a.applyPS (tax D p j):= by
   apply PowerSeries.ext; intro n; unfold tax; rw [complexes,coeff_mk, coeffGate]; simp_rw [mix,coeff_mk ]; rw [LinearMap.sum_apply,map_sum,Finsupp.finsetSum_apply]; refine Finset.sum_congr rfl fun i _=> ?_; rw [LinearMap.smul_apply, show (dime G d).repr (_ • (coeff i D p))= _ from (map_smul ((dime G d).repr.restrictScalars ℝ) (a.Γ n i) ( coeff i D p )) ]; rfl
lemma reports_mix (u:Test n)(p:Fin n→ Sec G d) : said (a.mix P) u p=a.applyPS (said P u p):= by
   apply PowerSeries.ext; intro i; unfold said; rw [a.complexes]; simp_rw [coeff_mk,mix]; simp only [ Finset.sum_apply, LinearMap.sum_apply, _root_.sum_apply, Pi.smul_apply,LinearMap.smul_apply, _root_.smul_apply ]
lemma compatiblePS : realm (a.gate D) (a.mix P) = a.mix (realm D P):= by
   ext1 k; ext1 n; ext1 t; ext1 p; have ht (P:Reports G d) : coeff k (said P t p)= P k n t p:=coeff_mk ..; rw [ ← ht, ← ht (a.mix _), reports_mix, talks,talks,map_sum a.applyPS]; apply congr_arg; exact Finset.sum_congr rfl (fun i _=> by simp only [reports_mix,taxGate,map_mul,map_prod]) -- `ht` rewritesp

lemma Chgs (A:Pick G d) : gate a (deck A)= deck (a.mix A):= by
   refine PowerSeries.ext fun n=>?_ ; rw [coeffGate,decked]; let U:ℕ→FieldEnd G d:= fun i=> if i=0 then 1 else 0; let V:ℕ→ FieldEnd G d:=fun i=>(A i).val;
   have hp (A:Pick G d) (i): pulling A i= U i+(A i).val:= by unfold pulling U; split; rfl; rw [zero_add];
   rw [ show (fun i=> coeff i ( deck A ))= U+V from funext (fun i=> by exact (decked A i).trans (hp A i)), combined, hp ]; congr 1; exact a.Γ_combine _; exact (a.across A (Change G d).subtype n).symm
lemma formal_gate (H: Formal D): Formal (a.gate D):= by
    obtain ⟨p,hp⟩:= H.actions; refine ⟨⟨a.mix p, by rw [hp, Chgs ] ⟩, (PowerSeries.isUnit_iff_constantCoeff (φ:=a.gate D) (R:=FieldEnd G d)).mpr ?_ ⟩; rw [← coeff_zero_eq_constantCoeff_apply, coeffGate, begins,coeff_zero_eq_constantCoeff_apply ]; exact (PowerSeries.isUnit_iff_constantCoeff (φ:=D) (R:=FieldEnd G d)).mp H.seed
lemma solvedGate {K:Pick G d}{W:Screen G d} (h:W.Solved K P): W.Solved (a.mix K) (a.mix P):=by
    intro i; rw [← Chgs,compatiblePS, a.across _ W.D i]; exact ( show W.D ∘ (realm ( deck K ) P)=(fun i=> if i=0 then W.D (reference G d) else 0) from funext h ).symm ▸ (a.Γ_combine _)

-- stronger invariance.Exact layout factors.
variable {A:Screen G d} (H:Fray A)(he:A.Prepared)
lemma layouts (hx:H.Executed he P): H.Lays he (a.mix P)= a.mix (H.Lays he P) := by
    have h:( a.mix P ) 0=P 0:= a.begins _; have ht:= no_reset H he ( Q:=a.mix P ) hx h.symm; apply A.shift_unique _ _ _ ?_ ht.2.1 ( solvedGate a P hx.2.1 ) ht.2.2.1
    rw [ begins, leads,leads,h]
lemma stand_inj : Injective (stand (G:=G) (d:=d)):=by intro x y h; apply Subtype.ext; ext1 p; exact add_left_cancel (DFunLike.congr_fun h p:p+x.val p=p+y.val p)
lemma equalLayout (hx:H.Executed he P) (h:Formal D)(hh:constantCoeff D=1) : D* ( deck (H.Lays he (realm D P)) )= (deck (H.Lays he P)):= by
    let Q:= realm D P; let t:= H.Lays he P; let w:= H.Lays he Q; have ht: Q 0=P 0:= by unfold Q; rw [rest,coeff_zero_eq_constantCoeff_apply, hh ]; rfl
    have hφ:= no_reset H he ( Q:=Q ) hx ht.symm; obtain ⟨k,hk⟩:= (h.product hφ.1).actions; change D*deck w=_; change D*deck w=_ at hk
    have h₁: A.Solved k P:= fun i=> by rw [← hk,← parlance ]; exact hφ.2.1 i
    rw [hk]; refine congr_arg deck ?_; symm; apply A.shift_unique _ _ _ _ hx.2.1 h₁ hx.2.2.1; apply stand_inj; rw [← const_deck,← const_deck,←hk,map_mul,hh,one_mul,const_deck,const_deck]; unfold w; rw [leads,leads,ht]; -- ok
end Key
end YM.MS.WilsonBridge.Coupling
