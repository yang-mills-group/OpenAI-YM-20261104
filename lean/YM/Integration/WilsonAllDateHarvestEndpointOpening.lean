import YM.Integration.WilsonAllDateHarvestAffine
import YM.RG05Readout.Many.Release

/-! Reopen both comparison inputs at the original dormant sites before the
ordinary full-census trajectory. All active signed coefficients are preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestEndpointOpening

open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker MergeProof MergeProof.Accent
open RG05Readout RG05Readout.Address RG05Readout.Many Extra.Histories Push
open WilsonAllDateHarvestAffine
open scoped BigOperators Classical

variable {V:Type} [DecidableEq V] {B C:Census V} {G:Gauge} {n:Side}

private def extension (inc:B.choices⊆C.choices) : Poly B →ₗ[ℂ] Poly C where
  toFun := wrap B C
  map_add' x y := by
    ext i
    by_cases hi:i.val∈B.choices
    · let j:B.Mode:=⟨i.val,hi⟩
      rw [show i=route inc j from rfl,Poly.part_plus,wrap_right,wrap_right,wrap_right,Poly.part_plus]
    rw [Poly.part_plus,wrap_off _ _ hi,wrap_off _ _ hi,wrap_off _ _ hi,zero_add]
  map_smul' z x := by
    ext i
    by_cases hi:i.val∈B.choices
    · let j:B.Mode:=⟨i.val,hi⟩
      rw [show i=route inc j from rfl,Poly.part_smul,wrap_right,wrap_right,Poly.part_smul]
      rfl
    rw [Poly.part_smul,wrap_off _ _ hi,wrap_off _ _ hi,mul_zero]

def opening (inc:B.choices⊆C.choices) (D:Set V) : Poly B →ₗ[ℂ] Poly C :=
  (extension inc).comp (feed (fun i:V=>if i∈D then 0 else 1) (id_licenses B)).toLinearMap

theorem genuine (inc:B.choices⊆C.choices) (D:Set V)
    (gate:∀i:C.Mode,i.val∉B.choices→¬Disjoint D (i.val:Set V))
    (x:Poly C) (dark:∀i:C.Mode,¬Disjoint D (i.val:Set V)→x.part i=0) :
    opening inc D (narrow inc x)=x := by
  ext i
  change (wrap B C (temperV B D (narrow inc x))).part i=x.part i
  by_cases hi:i.val∈B.choices
  · let j:B.Mode:=⟨i.val,hi⟩
    rw [show i=route inc j from rfl,wrap_right,temper_part,narrow_right]
    split_ifs with h
    · rfl
    exact (dark _ h).symm
  rw [wrap_off _ _ hi,dark _ (gate _ hi)]

variable [Fintype V] {P:Rep G n} {rows:V→Address.Three G n} {o:V→Site n} {w:V→ℝ} {α ρ:ℝ}
variable {X Y:Config G n→Poly B}

theorem paid (inc:B.choices⊆C.choices) (D:Set V)
    (gate:∀i:C.Mode,i.val∉B.choices→¬Disjoint D (i.val:Set V))
    (dormant:∀i∈D,(rows i).2.1=0 ∧ profile P.activities (rows i).2.2=0)
    (weight:∀i,0<w i) (board:MenuBoard P rows X o w α ρ) :
    MenuBoard P rows (fun U=>opening inc D (X U)) o w α ρ := by
  refine ⟨((opening inc D).toContinuousLinearMap.restrictScalars ℝ).integrable_comp board.cleared,
    board.fettled,?_⟩
  apply open_served inc D dormant weight (temper_served D dormant weight board.grants) _ gate
  intro U i crossed
  rw [temper_part,if_neg crossed]

omit [Fintype V] in
theorem intermediate (inc:B.choices⊆C.choices) (D:Set V)
    (gate:∀i:C.Mode,i.val∉B.choices→¬Disjoint D (i.val:Set V))
    (full:Config G n→Poly C) (dark:∀U i,¬Disjoint D (i.val:Set V)→(full U).part i=0)
    (z:ℂ) (eq:∀U,narrow inc (full U)=blend (X U) (Y U) z) :
    full=fun U=>blend (opening inc D (X U)) (opening inc D (Y U)) z := by
  funext U
  calc
    full U=opening inc D (narrow inc (full U)) := (genuine inc D gate _ (dark U)).symm
    _ = _ := by rw [eq]; simp only [blend,map_add,map_smul,map_sub]

end YM.Integration.WilsonAllDateHarvestEndpointOpening
