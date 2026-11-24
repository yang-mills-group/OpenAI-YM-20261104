import YM.Integration.WilsonLongContactForest
import YM.Integration.WilsonMacroscopicRichHeldMarkedScore
import YM.Integration.WilsonMacroscopicRichNormalizedRows
import YM.Integration.ActualTrajectoryTransport

/-! Arbitrarily long physical transport of a bounded merged row. Only the final normalized
transition differentiates the held field, including the established Wilson vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactResponse
open Lattice Wilson RG MeasureTheory PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Lotus
open Push.Local Push.Local.Kernel WilsonLocalHeldDerivatives WilsonMacroscopicRichTransitionIncome
open scoped BigOperators Classical
variable {G : Gauge}

theorem held (R : Run G) (N per j b : ℕ) (hj : j ≤ N) (hb : b ≤ j)
    (L : Leaf (R.family.path.rep N per j)) (W : Config G (R.family.S.side b per)) :
    ‖actualTransport R.family (N:=N) L.ingredient hb W‖ ≤ L.weight :=
  actualTransport_norm_le R.family R.makes hj L.earn hb W

theorem derivative (R : Run G) {N per j b : ℕ} (hj : j ≤ N) (hb : b < j)
    (H : Config G (R.family.S.side j per) → ℂ) (borel : Measurable H) {w : ℝ}
    (paid : ∀ U, ‖H U‖ ≤ w) (l : List (Directions G (R.family.S.side b per)))
    (V : Config G (R.family.S.side b per)) :
    leftDerivs (actualTransport R.family (N:=N) H hb.le) l V =
      ∫ U, measured R N per b V l U • actualTransport R.family (N:=N) H hb U ∂prior G _ := by
  let C := R.family
  let S := C.path.levels.clock.op b per
  let Q := C.path.rep N per (b+1)
  let Q' := C.path.rep N per b
  let T := actualTransport C (N:=N) H hb
  let X := fun U => Q.eval U • T U
  have live : b < N := hb.trans_le hj
  have den : S.push Q.beta Q.eval = Q'.eval := (R.makes.wilson.steps N per b live).1.symm
  have pos (W) : 0 < S.push Q.beta Q.eval W := den ▸ Multi.AxisShift.chosen_positive R.makes.wilson live.le W
  have reg : Integrable Q.eval (prior G (R.family.S.side (b+1) per)) :=
    ((R.family.path.rep N per (b+1)).envelope (R.makes.wilson.represents N per (b+1) live).good).integrable
      (prior G (R.family.S.side (b+1) per))
  have eqn : actualTransport C (N:=N) H hb.le = fun W => (S.push Q.beta Q.eval W)⁻¹ • S.push Q.beta X W := by
    rw [actualTransport_step C R.makes hj H hb]
    funext W
    rw [actualAverage_push,den]
  rw [eqn,WilsonMacroscopicRichNormalizedRows.integral S (C.path.levels.blocks b per).branches
    Q.beta Q.eval reg pos X
    (actualTransport_weighted_integrable C R.makes hj borel.aestronglyMeasurable paid hb)]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [WilsonLocalHeldDerivatives.factor,den]
  change leftDerivs (fun W => S.density Q.beta U W / Q'.eval W) l V • (Q.eval U • T U) =
    (leftDerivs (fun W => S.density Q.beta U W / Q'.eval W) l V * Q.eval U) • T U
  rw [smul_smul]

/-- The bill is fixed at the reporting date, before every finer date, period, or merged
support. It is paid once for the whole previously transported bounded coefficient. -/
theorem original (R : Run G) (b order edges : ℕ) {radius : ℝ} (rad : 0 ≤ radius) :
    let P := WilsonMacroscopicRichHeldProbePrice.price R b order edges radius
    ∀ N per j : ℕ, j ≤ N → ∀ hb : b < j,
      ∀ H : Config G (R.family.S.side j per) → ℂ, Measurable H → ∀ w : ℝ,
      (∀ U, ‖H U‖ ≤ w) → ∀ B : Edges (R.family.side b per), B.card ≤ edges →
      ∀ l : List (Directions G (R.family.S.side b per)), l.length ≤ order →
      (∀ A∈l, Born B radius A) → ∀ V : Config G (R.family.S.side b per),
        ‖leftDerivs (actualTransport R.family (N:=N) H hb.le) l V‖ ≤ P*w := by
  intro P N per j hj hb H borel w paid B hB l hl hA V
  let ρ := actualConditionalDensity R.family N per b V
  let D := measured R N per b V l
  let T := actualTransport R.family (N:=N) H hb
  have live := hb.trans_le hj
  obtain ⟨p0,permitted⟩ := WilsonMacroscopicRichHeldMarkedScore.score R b order edges rad
  have score := (permitted N per live B hB l hl hA V).2
  have w0 : 0 ≤ w := (norm_nonneg _).trans (paid 1)
  have fare (U) : ‖D U • T U‖ ≤ (P*w)*ρ U := by
    rw [norm_smul]
    calc ‖D U‖ * ‖T U‖ ≤ (P*ρ U)*w :=
          mul_le_mul (score U) (actualTransport_norm_le R.family R.makes hj paid hb U)
            (norm_nonneg _) (mul_nonneg p0 (actualConditionalDensity_nonneg R.family R.makes live V U))
      _ = _ := by ring
  rw [derivative R hj hb H borel paid]
  calc
    ‖∫ U, D U • T U ∂prior G _‖ ≤ ∫ U, ‖D U • T U‖ ∂prior G _ := norm_integral_le_integral_norm _
    _ ≤ ∫ U, (P*w)*ρ U ∂prior G _ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        ((actualConditionalDensity_integrable R.family R.makes live V).const_mul _) (Filter.Eventually.of_forall fare)
    _ = P*w := by rw [integral_const_mul,actualConditionalDensity_total R.family R.makes live V,mul_one]

end YM.Integration.WilsonLongContactResponse
