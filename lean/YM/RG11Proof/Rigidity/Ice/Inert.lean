import Mathlib.Analysis.SpecialFunctions.Exponential
import YM.RG11Proof.Rigidity.Ice.Holder

/-!
# Inert frame flows on the finite physical stage, off contacts only. Physical
real trait and quantification across cutoffs remains separately accounted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Pert.Position Pert Maxwell Function Extra.FD NormedSpace Filter
open scoped Classical BigOperators Topology ContDiff Real

variable {G : Gauge} {F : Frames G} {d:ℕ}

section evolve
variable {Y : Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y][FiniteDimensional ℝ Y]

def drive (b:Y→L[ℝ] Y)(v:Y)(t:ℝ):= exp (t • b) v
omit [CompleteSpace Y] [FiniteDimensional ℝ Y] in
lemma starts (b:Y→L[ℝ] Y)(v:Y) :drive b v 0=v:=by rw [drive,zero_smul,exp_zero]; rfl
omit [FiniteDimensional ℝ Y] in
lemma march (b:Y→L[ℝ] Y)(v:Y)(t:ℝ) : HasDerivAt (drive b v) (b (drive b v t)) t :=
  (ContinuousLinearMap.apply ℝ Y v).hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_exp_smul_const' b t)

omit [FiniteDimensional ℝ Y] in
lemma drive_parts (b:Y→L[ℝ] Y)(t:ℝ)(v:Y) : drive b v t = ∑' n : ℕ, (↑n.factorial : ℝ)⁻¹ • ((t • b)^n) v := by
  unfold drive; rw [exp_eq_tsum ℝ]
  exact Eq.trans ((ContinuousLinearMap.apply ℝ Y v).map_tsum (expSeries_summable' (𝕂:=ℝ) (t • b))) rfl

lemma drive_protect (V : Submodule ℝ Y)(b:Y→L[ℝ] Y)(h : ∀ v∈V,b v∈V)(v:Y)(hv:v∈V)(t:ℝ): drive b v t∈V := by
  rw [drive_parts]; apply tsum_mem V.closed_of_finiteDimensional; intro n; apply V.smul_mem
  induction n with
  | zero=>exact hv
  | succ n ih=> rw [pow_succ']; exact V.smul_mem _ (h _ ih)

omit [FiniteDimensional ℝ Y] in
lemma drive_anchor (b:Y→L[ℝ] Y)(v:Y)(h:b v=0)(t:ℝ): drive b v t=v := by
  rw [drive_parts,tsum_eq_single 0]; simp
  intro i hi; obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [pow_succ]; change _ • ((t • b)^i) (t • b v)=0; rw [h,smul_zero,map_zero, smul_zero]
end evolve

section framed
variable (b : Buffer F d)

lemma directs (t:ℝ)(v:E F d){e}(he:e≤ d)(h:v∈lower F e d): drive b.val v t∈lower F e d:= by
  obtain rfl|hx:=eq_or_lt_of_le he
  · exact top_step ..
  exact drive_protect ((lower F e d).restrictScalars ℝ) b.val (b.property.2.1 _ hx) _ h t

lemma drive_real (t:ℝ)(v:E F d)(h:Basis.overReals v): Basis.overReals (drive b.val v t):= by
  let B:=(tower F d).toBasis
  let V : Submodule ℝ (E F d) :=
    { carrier := {i|Basis.overReals i}
      zero_mem' := map_zero _
      add_mem' := fun a h=> by unfold Basis.overReals at *; exact (_root_.map_add _ _ _).trans (congr_arg₂ (·+·) a h)
      smul_mem' := fun t i h=> by
        unfold Basis.overReals at *; change (freeTable F).conj _ _ (_ • i)=t • i
        rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,h]; simp }
  change drive b.val v t∈ V
  exact drive_protect V _ (fun i h=> (b.property.2.2.1 i).trans (congr_arg b.val h)) _ h _

end framed
end YM.RG11.Rigidity.Ice
