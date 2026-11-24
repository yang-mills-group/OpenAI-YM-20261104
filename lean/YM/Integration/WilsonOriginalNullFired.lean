import YM.Integration.WilsonOriginalNullDate
import YM.Integration.WilsonMeasuredSingletonForce
import YM.MergeProof.Wicket

/-! The scalar projection of the actual one-mark return, with the complete
hard numerator kept on its own original numerical keys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullFired
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Ac MeasureTheory
open Extra.Histories Push.Local Overlay Fusion.Attached Extra.Multi Marker.Poly Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {C : Census Unit} {d : ℕ} {F : Frame G d} {P : Rep G n}
    {o : Unit → Site n} (H : Hard Unit P.p P.activities.forced P.activities.K o C)

theorem output (sec : SectionData F) (U : Config G n) (L : Poly C) (hL : L.part C.quiet = 0)
    (hh : Summable (packet P.activities P.p (H.hard ()) U)) :
    (((Real.exp (P.exponent U) : ℂ) • (Poly.pass L * WilsonCenteredAbsoluteHard.gas H () U)).part
        (C.fire ())) =
      (P.eval U : ℂ) * L.part (C.fire ()) + (WilsonMeasuredSingletonForce.row H () ()).density (o ()) sec P U := by
  rw [WilsonMeasuredSingletonForce.density H () () sec U hh]
  have quiet := Hard.packet_of_quiet H () U hh
  change (WilsonCenteredAbsoluteHard.gas H () U).part C.quiet = (P.activities.gas P.p U : ℂ) at quiet
  have fire : (Poly.pass L).part (C.fire ()) = L.part (C.fire ()) := by
    rw [←lamp () _ (Poly.pass_part L hL), connected_pass hL]
  simp only [Poly.part_smul, Multi.first_mul, fire, Poly.pass_part L hL, quiet, Rep.eval,
    Complex.ofReal_mul]
  ring

/-- The scalar and polynomial inputs are integrable on the actual Haar prior.
The two real functions are original admitted leaves and carry their true
pointwise fees, including the failed-mask values. -/
theorem input (P : Rep G n) (C : Census Unit) {σ A Λ e k : ℝ} (hp : P.Lawful σ A Λ e k)
    (a b : PhysicalNext.Repeat.Lotus.Leaf P) (φ : Config G n → ℂ)
    (re : ∀ U, a.ingredient U = (φ U).re) (im : ∀ U, b.ingredient U = (φ U).im)
    (w : ℝ) :
    Integrable (fun U => (P.eval U : ℂ) * φ U) (prior G n) ∧
    Integrable (fun U => Poly.bead C ((P.eval U : ℝ) : ℂ) +
      Poly.send (C.fire ()) (((w : ℂ) * (P.eval U : ℂ)) * φ U)) (prior G n) := by
  have ink (t : PhysicalNext.Repeat.Lotus.Leaf P) :
      Integrable (fun U => P.eval U * t.ingredient U) (prior G n) :=
    ((P.envelope hp).mul ⟨t.borel,t.weight,t.earn⟩).integrable _
  have val : Integrable (fun U => (P.eval U : ℂ) * φ U) (prior G n) := by
    apply ((ink a).ofReal.add ((ink b).ofReal.mul_const Complex.I)).congr
    filter_upwards [] with U
    change ((P.eval U * a.ingredient U : ℝ) : ℂ) + ((P.eval U * b.ingredient U : ℝ) : ℂ) * Complex.I =
      (P.eval U : ℂ) * φ U
    rw [re, im, Complex.ofReal_mul,Complex.ofReal_mul]
    calc
      _ = (P.eval U : ℂ) * (((φ U).re : ℂ) + ((φ U).im : ℂ) * Complex.I) := by ring
      _ = _ := congrArg ((P.eval U : ℂ) * ·) (Complex.re_add_im (φ U))
  refine ⟨val, ?_⟩
  have pure : Integrable (Complex.ofReal ∘ P.eval) (prior G n) := ((P.envelope hp).integrable _).ofReal
  have folded := (((Multi.sendC C.quiet).restrictScalars ℝ).integrable_comp pure).add
    (((Multi.sendC (C.fire ())).restrictScalars ℝ).integrable_comp (val.const_mul (w:ℂ)))
  apply folded.congr
  filter_upwards [] with U
  change Poly.send C.quiet ((P.eval U : ℝ) : ℂ) + Poly.send (C.fire ()) ((w:ℂ)*((P.eval U : ℂ)*φ U)) =
    Poly.send C.quiet ((P.eval U : ℝ) : ℂ) + Poly.send (C.fire ()) (((w:ℂ)*(P.eval U : ℂ))*φ U)
  rw [mul_assoc]

/-- Scalar projection commutes with the actual Wilson kernel, with the
original single tap undone only after returning to the scalar coefficient. -/
theorem push {l : Side} (step : StepData l n) (P : Rep G n) (C : Census Unit)
    {σ A Λ e k : ℝ} (hp : P.Lawful σ A Λ e k) (hk : step.IsKernel P.beta G)
    (a b : PhysicalNext.Repeat.Lotus.Leaf P) (φ : Config G n → ℂ)
    (re : ∀ U, a.ingredient U = (φ U).re) (im : ∀ U, b.ingredient U = (φ U).im)
    (w : ℝ) (V : Config G l) :
    ((step.push P.beta (fun U => Poly.bead C ((P.eval U : ℝ) : ℂ) +
      Poly.send (C.fire ()) (((w : ℂ) * (P.eval U : ℂ)) * φ U)) V).part (C.fire ())) =
      (w : ℂ) * step.push P.beta (fun U => (P.eval U : ℂ) * φ U) V := by
  obtain ⟨scalar, poly⟩ := input P C hp a b φ re im w
  have eqn := congrFun (MergeProof.Accent.push_get hk poly (C.fire ())) V
  refine eqn.trans ?_
  have equal : (fun U => (Poly.bead C ((P.eval U : ℝ) : ℂ) + Poly.send (C.fire ())
      (((w : ℂ) * (P.eval U : ℂ)) * φ U)).part (C.fire ())) =
      (w : ℂ) • (fun U => (P.eval U : ℂ) * φ U) := by
    funext U
    simp [Poly.bead, Poly.part_send, C.fire_hot (), mul_assoc]
  rw [equal, StepData.push_smul _ _ _ _ scalar]
  rfl

end YM.Integration.WilsonOriginalNullFired
