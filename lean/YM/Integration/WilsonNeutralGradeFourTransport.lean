import YM.Integration.WilsonOriginalThermometerPalette
import YM.TraceExtension.Terrace.Knell
import YM.TraceExtension.Terrace.Insert

/-! The finite measured transfer of the two intrinsic fourth-horizon legs of
the oriented Wilson coupling assay. The numerical reference column and both
its representatives use one original cutoff, period and source factory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralGradeFourTransport
open Function Source RG Lattice Wilson Cells Table Climb Trace.Terrace Next.Rank
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {N p : ℕ}
local notation "C" => R.family
local notation "V" => R.family.label 4
local notation "oneField" => (R.family.labels.level 4).e0

/-- Reference to the physical coordinate after removing the engineering scale. -/
def atDate (j : ℕ) (ref : R.family.ref 4 ≤ j) (top : j ≤ N) : V ≃ₗ[ℂ] V :=
  (LinearEquiv.ofBijective ((nib_linear C R.makes (p:=p) ref top).mk' _)
      (nib_faithful C R.makes ref top)).trans
    (LinearEquiv.smulOfNeZero ℂ V ((R.family.S.a j : ℂ)^4)⁻¹
      (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos j).ne'))))

theorem atDate_apply (j : ℕ) (ref : R.family.ref 4 ≤ j) (top : j ≤ N) (v : V) :
    atDate R (p:=p) j ref top v = Price.awake C 4 j N p v := rfl

theorem atDate_unit (j : ℕ) (ref : R.family.ref 4 ≤ j) (top : j ≤ N) :
    atDate R (p:=p) j ref top (R.family.refUnit 4) = oneField := by
  rw [atDate_apply, Price.awake, ← Cturn, nib_unit C R.makes ref top, unitVec, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos j).ne')), one_smul]

/-- Space on which a connected hearing eliminates a scalar deposit. -/
def scalars := Submodule.span ℂ ({oneField} : Set V)

def transfer {m j : ℕ} (ref : R.family.ref 4 ≤ m) (mj : m ≤ j) (top : j ≤ N) : V ≃ₗ[ℂ] V :=
  (atDate R (p:=p) j (ref.trans mj) top).symm.trans (atDate R (p:=p) m ref (mj.trans top))

theorem transfer_unit {m j : ℕ} (ref : R.family.ref 4 ≤ m) (mj : m ≤ j) (top : j ≤ N) :
    transfer R (p:=p) ref mj top oneField = oneField := by
  change atDate R (p:=p) m ref (mj.trans top) ((atDate R (p:=p) j (ref.trans mj) top).symm _) = _
  rw [show (atDate R (p:=p) j (ref.trans mj) top).symm oneField = R.family.refUnit 4 from
    (atDate R (p:=p) j (ref.trans mj) top).symm_apply_eq.mpr (atDate_unit R j (ref.trans mj) top).symm, atDate_unit]

theorem map_scalars {m j : ℕ} (ref : R.family.ref 4 ≤ m) (mj : m ≤ j) (top : j ≤ N) :
    (scalars R).map (transfer R (p:=p) ref mj top).toLinearMap = scalars R := by
  rw [scalars, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun x : V => Submodule.span ℂ ({x} : Set V)) (transfer_unit R (p:=p) ref mj top)

def onQuotient {m j : ℕ} (ref : R.family.ref 4 ≤ m) (mj : m ≤ j) (top : j ≤ N) :
    (V ⧸ scalars R) ≃ₗ[ℂ] (V ⧸ scalars R) :=
  Submodule.Quotient.equiv _ _ _ (map_scalars R (p:=p) ref mj top)

theorem original {m j : ℕ} (ref : R.family.ref 4 ≤ m) (mj : m ≤ j) (top : j ≤ N)
    (A : Group C 6) (leg : Fin 2) :
    let x := fun k => coordinates R A k N p leg.succ
    transfer R (p:=p) ref mj top (x j) = x m ∧
    onQuotient R (p:=p) ref mj top ((scalars R).mkQ (x j)) = (scalars R).mkQ (x m) := by
  let i := leg.succ
  let v : V := A.station.wheel.atCut (N,p) (index A (grade i)) (vector A Finset.univ i)
  change transfer R (p:=p) ref mj top (atDate R (p:=p) j (ref.trans mj) top v) =
      atDate R (p:=p) m ref (mj.trans top) v ∧ _
  have same : transfer R (p:=p) ref mj top (atDate R (p:=p) j (ref.trans mj) top v) =
      atDate R (p:=p) m ref (mj.trans top) v := by simp [transfer]
  exact ⟨same, congrArg (scalars R).mkQ same⟩

/-- At horizon four the physical field projection has trivial kernel. This
also retains the unit whenever the full moment, rather than its connected
part, is required. -/
theorem at_horizon (h : G.Simple) {S : Table R.family.book} (X : Climb.Scaling S) :
    Function.Bijective (S.project 4) := actual4 h X

end YM.Integration.WilsonNeutralGradeFourTransport
