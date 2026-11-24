import YM.Integration.WilsonSurveyedColorVacuumBasis
import YM.Integration.WilsonSurveyedColorVacuumKnight
import YM.XSpace.PairGlyph

/-! The independent MS matrix and the original recorded color action on the same
on-shell fields, including fields in every lower grade of the cumulative space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorAxis
open Function Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab XSpace.Stab.OJoint
open Labels MS MS.Arts MS.Theater MS.Land FVA2 FVA2.Dframe FVA2.O.Score
open WilsonSurveyedColorOpenIndex WilsonSurveyedColorCurvature WilsonSurveyedColorNormalizers
open WilsonSurveyedColorHomeDeck WilsonSurveyedColorNamedBasis
open scoped Classical BigOperators
variable {G : Gauge}
local notation "B" => Press.portDeck G

def reduced (G : Gauge) (h : ℕ) : WilsonSurveyedColorHomeDeck.Board G h →ₗ[ℝ] WickPol G :=
  ∑ r : Fin (h+1), (reduceEq.toLinearMap.restrictScalars ℝ) ∘ₗ (Film0 G h r.val).subtype ∘ₗ
    Resume (Press.portDeck G) h r.val ∘ₗ LinearMap.proj r

theorem atRank {h : ℕ} (r : Fin (h+1)) (v : (Press.portDeck G).carries (h:ℤ) r.val) :
    reduced G h (Pi.single r v) = reduceEq (Resume B h r.val v).val := by
  unfold reduced
  rw [LinearMap.sum_apply,Finset.sum_eq_single r]
  · simp
  · intro z _ hz
    simp [Pi.single_eq_of_ne hz]
  · simp

theorem filed {h d : ℕ} (i : Grade G h) (hi : h ≤ d) :
    reduced G h (WilsonSurveyedColorHomeDeck.basis G h i) = (cap (own i) hi).val := by
  rw [WilsonSurveyedColorHomeDeck.basis,Pi.basis_apply,atRank]
  rfl

variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (N : Normalizes U)

theorem placed {h : ℕ} (i : Grade G h) (X : TaylorTower G) :
    probe X (reduced G h (WilsonSurveyedColorHomeDeck.wheel U N h (WilsonSurveyedColorHomeDeck.basis G h i))) =
    probe (fun j => faceMap j U.toContinuousLinearEquiv.toContinuousLinearMap (X j))
      (reduced G h (WilsonSurveyedColorHomeDeck.basis G h i)) := by
  rw [WilsonSurveyedColorHomeDeck.basis,Pi.basis_apply,oneAxis,atRank,atRank,print]
  change probe X (reduceEq (changed (WilsonSurveyedColorPlot.color U) _)) =
    probe _ (reduceEq _)
  rw [jet_value,jet_value,eval_changed]
  apply congrArg (fun A => Labels.read A _)
  funext j
  exact (WilsonSurveyedColorHomeLift.shell U (X j)).symm

theorem column {h d : ℕ} (i : Grade G h) (hi : h ≤ d) :
    (WilsonSurveyedColorVacuumBasis.axis U N d (cap (own i) hi)).val =
    reduced G h (WilsonSurveyedColorHomeDeck.wheel U N h (WilsonSurveyedColorHomeDeck.basis G h i)) := by
  change (shellSector G d).subtype (_) = _
  rw [WilsonSurveyedColorVacuumBasis.label,map_sum]
  conv_rhs => rw [← (WilsonSurveyedColorHomeDeck.basis G h).sum_repr (WilsonSurveyedColorHomeDeck.wheel U N h (WilsonSurveyedColorHomeDeck.basis G h i)),map_sum]
  simp only [map_smul,Complex.coe_smul,
    WilsonSurveyedColorNamedBasis.entry,filed (d:=d) _ hi]
  rfl

theorem evaluated {d : ℕ} (p : Sec G d) (X : TaylorTower G) :
    probe X (WilsonSurveyedColorVacuumBasis.axis U N d p).val =
    probe (fun j => faceMap j U.toContinuousLinearEquiv.toContinuousLinearMap (X j)) p.val := by
  let A : Sec G d →ₗ[ℂ] ℂ := (probe X).toLinearMap ∘ₗ (shellSector G d).subtype ∘ₗ
    WilsonSurveyedColorVacuumBasis.axis U N d
  let C : Sec G d →ₗ[ℂ] ℂ :=
    (probe (fun j => faceMap j U.toContinuousLinearEquiv.toContinuousLinearMap (X j))).toLinearMap ∘ₗ
      (shellSector G d).subtype
  have maps : A = C := by
    apply (Daylight (Press.portDeck G) d).ext
    intro i
    have hi := size_le i
    change probe X (WilsonSurveyedColorVacuumBasis.axis U N d
      (Daylight (Press.portDeck G) d i)).val = _
    rw [theory_sig]
    change probe X (WilsonSurveyedColorVacuumBasis.axis U N d (cap (own (panel i)) hi)).val =
      probe _ (cap (own (panel i)) hi).val
    rw [column, ← filed (panel i) hi]
    exact placed U N (panel i) X
  exact DFunLike.congr_fun maps p

theorem oriented (c : Knight G) (sign : conn c 1) :
    Preserves (WilsonSurveyedColorVacuumKnight.isometry c) := by
  intro x y z
  change inner ℝ (Spin c x) (G.ad (Spin c y) (Spin c z)) = inner ℝ x (G.ad y z)
  calc _ = CH G (Spin c y) (Spin c z) (Spin c x) := real_inner_comm _ _
    _ = CH G y z x := (sign y z x).trans (one_mul _)
    _ = _ := real_inner_comm _ _

theorem original (c : Knight G) (N' : Normalizes (WilsonSurveyedColorVacuumKnight.isometry c))
    {d : ℕ} (p : Sec G d) :
    (WilsonSurveyedColorVacuumBasis.axis (WilsonSurveyedColorVacuumKnight.isometry c) N' d p).val =
    appears G d (changing c (records G d p)) := by
  apply Maxwell.equalPol
  intro X
  rw [evaluated, WilsonSurveyedColorVacuumKnight.recorded]
  rfl

end YM.Integration.WilsonPositionScaleLawColorAxis
end
