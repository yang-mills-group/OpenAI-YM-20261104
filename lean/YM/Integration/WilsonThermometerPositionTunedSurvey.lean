import YM.Integration.WilsonThermometerPositionTunedSlope
import YM.Integration.WilsonEpochCalibratedInsertion

/-! On each original complete Wilson frame, the public survey has an actual
finite cylinder for every basis letter. Keep the basis changes of its Wick
subtraction, including the unit, before multiplying any three sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedSurvey
open Function Lattice Wilson Source Source.Drops Labels XSpace PhysicalNext.Repeat.Legato
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G) (W:Initialize G) (d:ℕ)
local notation "F" => R.family.labels.level d

def prepared : SectionData F := ((W.surveys d).prepares F).choose

theorem represents : (W.surveys d).Represents F (prepared R W d) :=
  ((W.surveys d).prepares F).choose_spec

theorem sound : (prepared R W d).Sound R.family.params := by
  rw [← WilsonEpochPositionCoefficients.holonomy W.hol R.family.params]
  exact (represents R W d).1

theorem invisible : ∃ b:ℕ, ∀ n:Side, b ≤ n.val → ∀ o:Site n, ∀ c:(F).Coeff,
    R.family.params.PiVanish d o
      (fun U => (R.family.localSection d).places c o U - (prepared R W d).places c o U) := by
  let A:=R.family.localSection d
  let T:=prepared R W d
  obtain ⟨b,hab⟩:=WardBin.large_fits A.stencil
  obtain ⟨e,hte⟩:=WardBin.large_fits T.stencil
  refine ⟨max b e,?_⟩
  intro n hn o c J
  let Z:=fun h:ℝ=>R.family.params.links d J h
  have left (h:ℝ) : A.places c o (R.family.params.testLinks d o J h)=A.evaluate c (Z h) :=
    WardBin.fromAbove (A.cylinder_local c) (hab n ((le_max_left _ _).trans hn)) o (Z h)
  have right (h:ℝ) : T.places c o (R.family.params.testLinks d o J h)=T.evaluate c (Z h) :=
    WardBin.fromAbove (T.cylinder_local c) (hte n ((le_max_right _ _).trans hn)) o (Z h)
  let u:=fun h:ℝ=>A.places c o (R.family.params.testLinks d o J h) -
    T.places c o (R.family.params.testLinks d o J h)
  let v:=fun h:ℝ=>A.evaluate c (Z h)-T.evaluate c (Z h)
  have eq : u=v := funext fun h=>congrArg₂ (·-·) (left h) (right h)
  change ContDiffAt ℝ _ u 0 ∧ ∀ k ≤ d, iteratedDeriv k u 0 = 0
  rw [eq]
  have ah:=(R.makes.sections d).projects c J
  have th:=(sound R W d).projects c J
  refine ⟨ah.1.sub th.1,fun k hk=>?_⟩
  exact (iteratedDeriv_fun_sub (ah.1.of_le (Nat.cast_le.mpr hk))
    (th.1.of_le (Nat.cast_le.mpr hk))).trans (sub_eq_zero.mpr
      ((ah.2.2 k hk).trans (th.2.2 k hk).symm))

variable (P:XSpace.Period) (tree:P.Tree) (x:P.Sites)
def row (b:(F).Index) : Bare.Series tree G := Bare.raw tree (W.surveys d) x ((F).basis b).val

theorem shifted (b:(F).Index) :
    PowerSeries.X ^ ((F).grades b).2 * row R W d P tree x b =
    Taylor.expandTaylor (tree.basis G) (fun u => (prepared R W d).places (Pi.single b 1) x (tree.links u)) := by
  have h:=Bare.raw_calculation tree (W.surveys d) x F (prepared R W d) (represents R W d)
    ((F).grades b).1 ((F).grades b).2 ((F).pure b)
  simpa only [row, Frame.coords_basis] using h

/-- Coordinates of the survey's genuine local Wick correction on the actual
Wilson basis, at the original position and on the common finite pad. -/
def rates (v:Labels.Label G d) : (F).Coeff := (F).coords ((W.surveys d).insertW (-1) v)

theorem corrected (v:Labels.Label G d) :
    Bare.column tree (W.surveys d) x v =
      ∑ b:(F).Index, rates R W d v b • row R W d P tree x b := by
  let L:Labels.Label G d →ₗ[ℂ] Bare.Series tree G :=
    (MvPolynomial.aeval (Bare.factor tree (W.surveys d) x)).toLinearMap.comp (localFields G d).subtype
  let y:=(W.surveys d).insertW (-1) v
  have h:=congrArg L ((F).basis.sum_repr y)
  rw [map_sum] at h
  simp only [map_smul] at h
  exact h.symm

end YM.Integration.WilsonThermometerPositionTunedSurvey
end
