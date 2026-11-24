import YM.RG11Proof.Formal.Calibrate

/-!
# Fix the pencil's coupling component with a separate scalar detector

Deliver a solver extracting the same tangent as this predeclared detector on
the other scheme (so in particular prove leading invertibility from a single
slope test at first order, no preferred scheme parameter convention silently
assumed, usable before proving any full scheme match). At higher orders a
connected convention or previously rotated fields can change the price too;
the solver there continues to use simultaneous calibration in all slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped Classical BigOperators

variable {R J P : Type*} [Field R] [Fintype J]
variable {shape : P→ℕ} {A : ArrayAt J R shape} {L : Constraints R J}

namespace RulerTest

def priceAt (T : RulerTest L A) (B : ArrayAt J R shape) (n : ℕ) :=
  T.meter (fun i => coeff n (B (T.tests i)))

/-- Replace only the left-inverse choice to GUARANTEE the coupling recovered
from a diagnostic with nonzero derivative in the scheme inserted. For arrays
lying in the conversion orbit any choice would agree; initial tangent as solved
on the detector alone need not. -/
def pin (T : RulerTest L A) (Q : Detector L A) : Detector L A where
  m := Q.m + T.m
  test := Fin.append Q.test T.tests
  restore :=
    ((LinearMap.fst R (↥L.vary) R).comp (Q.restore.comp (LinearMap.pi fun i=> LinearMap.proj (R:=R) (φ:=fun _:Fin (Q.m+T.m)=>R)
      (Fin.castAdd T.m i))))
     |>.prod (T.meter.comp (LinearMap.pi fun i=> LinearMap.proj (Fin.natAdd Q.m i)))
  works x := by
    apply Prod.ext
    · change (Q.restore (fun i=> fullRead L A x (Fin.append Q.test T.tests (Fin.castAdd T.m i)))).1=_
      simp_rw [Fin.append_left]; rw [Q.works]
    change T.meter (fun i=> fullRead L A x (Fin.append Q.test T.tests (Fin.natAdd Q.m i))) = _
    simp_rw [Fin.append_right]; rw [T.reads]

@[simp] theorem pin_recoupling (T : RulerTest L A) (Q : Detector L A) (B : ArrayAt J R shape) (n:ℕ) :
    ((T.pin Q).restore (fun i=> coeff n (B ((T.pin Q).test i)))).2=T.priceAt B n := by
  change T.meter (fun i=> coeff n (B (Fin.append Q.test T.tests (Fin.natAdd Q.m i))))=_
  simp_rw [Fin.append_right]; rfl

variable [DecidableEq J]

def calibrate (T : RulerTest L A) (h : Free L A) (B : ArrayAt J R shape) : Change R J :=
  RG11.Formal.solution (pin T (Detector.ofSees (Sees.of_parts h T))) B

theorem calibrate_law (T : RulerTest L A) (h : Free L A) (B : ArrayAt J R shape) :
    RG11.Formal.Law L (T.calibrate h B) := RG11.Formal.solution_law ..

theorem calibrate_tangent (T : RulerTest L A) (h : Free L A) (B : ArrayAt J R shape) :
    tangent (calibrate T h B).g=T.priceAt B 1 := (RG11.Formal.tangent_solution ..).trans (pin_recoupling ..)

theorem calibrate_good (T : RulerTest L A) (h : Free L A) {B : ArrayAt J R shape} (h₁ : T.priceAt B 1 ≠ 0) :
    Change.Good L (T.calibrate h B) :=
  ⟨⟨(calibrate_law ..).1, isUnit_iff_ne_zero.mpr ((T.calibrate_tangent h B).trans_ne h₁)⟩, (calibrate_law ..).2⟩
end RulerTest
end YM.RG11.Jets
