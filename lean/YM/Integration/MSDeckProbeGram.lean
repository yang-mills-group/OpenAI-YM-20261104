import YM.Integration.OPEProjectedMSRows
import YM.OPE.Levy.Panel
import YM.RG11Proof.Neighborhood.Feelers

/-! The native, unrelabelled two-point receiver in every independently
booked MS physical deck. Both slots can have any engineering grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSDeckProbeGram

open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open scoped Classical BigOperators

variable {G : Gauge} (V : Warehouse G) {B : Deck G} {Q : Booked B}
variable (M : MS_Data G Q) {d n : ℕ}

def basis (B : Deck G) (d : ℕ) : Module.Basis (Glyph B d) ℂ (E V.F d) :=
  (Daylight B d).map (exactField V.F d).symm

theorem letters (a : Glyph B d) :
    writes V.F d (basis V B d a) = Letters B a := by
  change (exactField V.F d (basis V B d a)).val = _
  rw [basis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, readHeight]

def raw (a : Fin n → Glyph B d) (x : Points n) (μ : ℝ) (k : ℕ) : ℂ :=
  Dial.tour M (FVA2.ColorCode.labelAt B ∘ a) μ (Fountain.metric x) Finset.univ k

theorem free (a : Fin n → Glyph B d) (x : Points n) (hx : x ∈ conf n) (μ : ℝ) :
    raw M a x μ 0 = visible V.F d x (basis V B d ∘ a) := by
  unfold raw Fountain.metric
  rw [Dial.highest_zero M μ x (FVA2.ColorCode.labelAt B ∘ a) hx, PositionX.visible_eq]
  congr 1
  funext i
  change Letters B (a i) = Maxwell.Free.address V.F d (basis V B d (a i))
  exact (letters V (a i)).symm.trans (Fountain.common_L V d _)

def matrix (d : ℕ) (p q : E4) (μ : ℝ) (k : ℕ) : Matrix (Glyph B d) (Glyph B d) ℂ :=
  fun a b => raw M ![a,b] (couple p q) μ k

theorem free_entry (μ : ℝ) {p q : E4} (hp : p ≠ q) (a b : Glyph B d) :
    matrix M d p q μ 0 a b =
      visible V.F d (couple p q) ![basis V B d a, basis V B d b] := by
  rw [matrix, free V M _ _ (couple_ok hp)]
  congr 1
  funext i
  fin_cases i <;> rfl

include V in
theorem invertible (μ : ℝ) {p q : E4} (hp : p ≠ q) (d : ℕ) :
    IsUnit (matrix M d p q μ 0) := by
  let e := basis V B d
  let L := linear₂ (visible V.F d (couple p q))
  have read (u : Glyph B d → ℂ) (a : Glyph B d) :
      ((matrix M d p q μ 0).vecMul u) a = L (e.equivFun.symm u) (e a) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply]
    change ∑ j, u j * matrix M d p q μ 0 j a = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, free_entry V M μ hp j a]
    rfl
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro u v h
  have equal : L (e.equivFun.symm u) = L (e.equivFun.symm v) :=
    e.ext fun j => (read u j).symm.trans ((congrFun h j).trans (read v j))
  apply e.equivFun.symm.injective
  apply sub_eq_zero.mp
  by_contra hn
  obtain ⟨t, ht⟩ := Pert.Scale.fullness V.F hp _ hn
  apply ht
  change L (e.equivFun.symm u - e.equivFun.symm v) t = 0
  rw [map_sub, equal, sub_self, LinearMap.zero_apply]

end YM.Integration.MSDeckProbeGram
