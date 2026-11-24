import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogReserve

/-! A joint finite physical test pays the product of the separate filed readers on every submode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogWeights
open Finset Marker
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

def weight (reader:V→ℂ) (v:V):ℝ:=(max 1 ‖reader v‖)⁻¹
omit [DecidableEq V] [Fintype V] in
theorem positive (reader:V→ℂ) (v:V):0<weight reader v:=by
  apply inv_pos.mpr
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

omit [Fintype V] in
theorem paid {I:Type} [Fintype I] (reader:V→ℂ) (s:Γ.Mode) (e:I≃s.val):
    Poly.toll (weight reader) s * (∏i:I,‖reader (e i).val‖)≤1:=by
  have eq:(∏i:I,‖reader (e i).val‖)=∏i∈s.val,‖reader i‖:=
    (e.prod_comp (fun z:s.val=>‖reader z.val‖)).trans (Finset.prod_coe_sort s.val (fun i:V=>‖reader i‖))
  rw [eq,Poly.toll,←Finset.prod_mul_distrib]
  apply Finset.prod_le_one (fun i _=>mul_nonneg (positive reader i).le (norm_nonneg _))
  intro i _
  exact (inv_mul_le_one₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).2 (le_max_right _ _)

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogWeights
