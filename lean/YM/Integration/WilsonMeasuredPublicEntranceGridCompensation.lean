import YM.Integration.WilsonMeasuredPublicEntranceGridDebit
import YM.Integration.WilsonMeasuredPublicEntranceCheapField

/-! Reconstruct the signed cut-to-trial source from the earned ultraviolet
matrix and the two true single-field readings, and charge its ordinary term
against the physical fees of the other fields. The ultraviolet and guarded
gases keep their own compulsory addresses. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceGridCompensation
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open PhysicalNext PhysicalNext.Repeat Legato Work.G08
open WilsonPositionProgramBlockedPublicExperiment WilsonOriginalMicroscopicGuardedNomination
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonMeasuredCoefficientTransport WilsonThermometerUnitFilingFieldRange WilsonOriginalAlternativeHearing
open WilsonMeasuredPublicEntranceGridDebit WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredPublicEntranceCheapField
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V : Type} {N p f n b : ℕ} (d j : V → ℕ)
variable (W : Rep G (R.family.side f p)) (o : V → Site (R.family.side f p))
    (X Y Z : (v : V) → Coefficient (R.family.labels.level (d v)) (R.family.side f p))
    (A : (v : V) → R.family.label (d v) ≃ₗ[ℂ] R.family.label (d v))
    (names : (v : V) → R.family.label (d v)) (c : V → ℂ)
local notation "P" => R.family.path.rep N p f
local notation "xy" => fun v => (A v).symm (fitted R (d v) (j v) N p (names v))
local notation "fee" => fun v => bill R (d v) (f+n) f (xy v)
local notation "sigma" => fun v => -(c v)/(R.family.S.a f:ℂ)^(d v)

def earned : Prop :=
  ∀ v, WilsonAddressedRestartedFiled.Filed R (d v) N p f (o v)
    (track R (d v) N p (f+n) (numerator R (d v) N p (f+n) 0 (xy v)) f-
      calValues (C:=R.family) (d v) N p f ((R.family.factory (d v) N p).terminal.symm (names v))) (fee v) (Z v)

theorem filed (live : f+n ≤ N)
    (debit : ∀v, settled R (d v) (j v) f n N p live (A v) (names v) (o v))
    (physical : ∀ v U, (X v).density (o v) (R.family.localSection (d v)) P U =
      ((P).eval U:ℂ)* (c v*actualTransport R.family (N:=N)
        (named R (d v) f N p (by omega) (o v) (names v)) (by omega) U))
    (independent : ∀ v U, (Y v).density (o v) (R.family.localSection (d v)) W U =
      ((P).eval U:ℂ)* (c v*actualTransport R.family (N:=N)
        (trial R (d v) f n N p (o v) (xy v)) (Nat.le_add_right f n) U)) :
    ∃ Z, earned R (n:=n) (N:=N) d j o Z A names ∧
      ∀ v U, (X v).density (o v) (R.family.localSection (d v)) P U -
        (Y v).density (o v) (R.family.localSection (d v)) W U =
        (sigma v)*(Z v).density (o v) (R.family.localSection (d v)) P U := by
  classical
  choose Z cash equation using debit
  refine ⟨Z,cash,?_⟩
  intro v U
  rw [physical,independent,← mul_sub,← mul_sub,equation]
  have nz : ((P).eval U:ℂ) ≠ 0 := by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (by omega : f≤N) U).ne'
  have af : (R.family.S.a f:ℂ) ≠ 0 := by exact_mod_cast (R.family.S.a_pos f).ne'
  field_simp

theorem original (same : W.eval = (P).eval)
    (sheet : ∀v U, (X v).density (o v) (R.family.localSection (d v)) P U -
        (Y v).density (o v) (R.family.localSection (d v)) W U =
        (sigma v)*(Z v).density (o v) (R.family.localSection (d v)) P U)
    (vs : List V) (U : Config G (R.family.side f p)) :
    let x := fun v => regular R d P o X v U
    let y := fun v => regular R d W o Y v U
    let e := fun v => sigma v * regular R d P o Z v U
    let hard := fun v => charge R d P X v U-charge R d W Y v U-sigma v*charge R d P Z v U
    ((P).eval U:ℂ)*((vs.map x).prod-(vs.map y).prod) =
      ((P).eval U:ℂ)*route x (fun v => x v-e v) e vs-route y (fun v => x v-e v) hard vs := by
  apply WilsonMeasuredPublicEntranceCheapOrder.original
  intro v
  have h := sheet v U
  change _ * (_ - (_ - (_ * _))) = _ - _ - _ * _
  unfold regular charge
  simp only [Coefficient.density,account,same] at h ⊢
  linear_combination -h

theorem heard (live : f+n≤N) (lower : b≤f) (fund : earned R (n:=n) (N:=N) d j o Z A names)
    (κ₀ M : V → ℝ) (px : ∀v, (X v).remBound (o v) P (κ₀ v) (M v))
    (vs : List V) (T : Config G (R.family.side b p)) :
    let x := fun U v => regular R d P o X v U
    let e := fun U v => sigma v*regular R d P o Z v U
    let a := fun v => fare R d P X v (M v)
    let δ := fun v => ‖sigma v‖*(|cost G (d v) (P).p.threshold| *
      ((invoice (C:=R.family) (d v) f p+4)*(fee v))+(1+4*stock R.family f)*(fee v))
    ‖held R.family N p (fun U => ((P).eval U:ℂ)*route (x U) (fun v => x U v-e U v) (e U) vs) lower T‖ ≤
      route a (fun v => a v+δ v) δ vs := by
  dsimp only
  have le : f≤N := by omega
  rw [normalized R.family N p R.makes le _ lower]
  apply actualTransport_norm_le R.family R.makes le _ lower
  intro U
  have nz : ((P).eval U:ℂ) ≠ 0 := by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson le U).ne'
  simp only [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ nz, one_mul]
  apply WilsonMeasuredPublicEntranceCheapOrder.price
  · intro v
    exact point R (d v) P (X v) (o v) (px v) U
  · intro v
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine (point R (d v) P (Z v) (o v) (fund v).paid U).trans ?_
    apply add_le_add _ le_rfl
    have pn : 0 ≤ (R.family.labels.level (d v)).coeffSize (Z v).x := size_nonneg _ _
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) pn).trans
      (by simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left (fund v).primary (abs_nonneg (cost G (d v) (P).p.threshold)) )

end YM.Integration.WilsonMeasuredPublicEntranceGridCompensation
end
