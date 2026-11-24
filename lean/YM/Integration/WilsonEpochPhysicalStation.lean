import YM.Integration.WilsonEpochOriginalFeed
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! Retain the temperature/field conversion and the calibrated continuum
meter on the *same* physical Run. The terminal RG10 source and the booked
epoch are evaluated at their specified common UV and IR regulators; the
finite change from the position meter is displayed before any varying-cutoff
estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochPhysicalStation

open Function Filter Lattice Source Source.Drops Labels XSpace FVA2 FVA2.Arrival FVA2.Register
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonEpochCalibratedInsertion WilsonEpochPositionCoefficients
open WilsonEpochOriginalFeed
open scoped Classical Topology BigOperators

universe u
variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)

/-- On every lower Wick term this actual terminal matrix scales by its own
Laurent slot number, even when it is lower than the declared field size. -/
theorem temperature (Y : Initialize G) (c per : ℕ) (s : Folio G) :
    Dict06.Actual.calibrate R.family c per s.u.size (s.item Y) =
      (R.family.factory s.u.size c per).terminal
        (((R.family.path.levels.clock.threshold c ^ s.slots : ℝ) : ℂ) •
          (R.family.labels.level s.u.size).coords (s.item Y)) := by
  obtain ⟨u,hu⟩ := Press.pure_chip Y s.u s.j
  change (R.family.factory s.u.size c per).terminal
      ((R.family.labels.level s.u.size).scaled _ (_)) = _
  exact congrArg (R.family.factory s.u.size c per).terminal
    ((R.family.labels.level s.u.size).scaled_pure _ (u,s.slots) hu)

theorem common (N : WilsonPrescription G) (c per i B : ℕ)
    (geo : (R.family.S.denominator c).val = N.run.ratio ^ i ∧
      (R.family.S.period per).val = N.run.finalSide.side.val * N.run.ratio^(N.run.reserve*i*i))
    (P : Handoff.Directory N i B) (v : List (Birth G)) (k : ℕ)
    (enough : Handoff.Directory.requested v + k ≤ B) :
    let n := R.family.side c per
    let ev := even_iff_two_dvd.mpr (ActualOriginalFiniteCoefficients.side_admissible R c per).2
    PowerSeries.coeff k (Birth.scan v (row R N.scheme n ev)) -
      Complex.ofReal (PowerSeries.coeff k (P.product v)) =
      Complex.ofReal (PowerSeries.coeff k (Birth.scan v (WilsonEpochPositionCoefficients.residual R N.scheme n))) := by
  obtain ⟨_,he⟩ := (WilsonEpochRegulator.same R N.run c per i).2 geo
  let Q (n : Side) := ∀ ev : Even n.val,
    PowerSeries.coeff k (Birth.scan v (row R N.scheme n ev)) -
      Complex.ofReal (PowerSeries.coeff k (P.product v)) =
      Complex.ofReal (PowerSeries.coeff k (Birth.scan v (WilsonEpochPositionCoefficients.residual R N.scheme n)))
  have target : Q ((N.run.step i).p.side) := fun _ => priced R N i B P v k enough
  exact (he.symm ▸ target : Q (R.family.side c per)) _

def clockCorrection (g w : ℝ → ℝ) (k : ℕ) (v : ℂ) (r : ℝ) :=
  ((((g r/w r)^k-1 : ℝ) : ℂ))*v

private theorem small {g w : ℝ → ℝ}
    (h : Tendsto (fun r => g r/w r) Trace.Pilot.trail (𝓝 1)) (k : ℕ) (v : ℂ) :
    Tendsto (clockCorrection g w k v) Trace.Pilot.trail (𝓝 0) := by
  have hp : Tendsto (fun r => (g r/w r)^k-1) Trace.Pilot.trail (𝓝 0) := by
    simpa using (h.pow k).sub_const 1
  change Tendsto (fun r => Complex.ofReal ((g r/w r)^k-1)*v) _ _
  simpa only [Complex.ofReal_zero,zero_mul,Function.comp_apply] using
    (Complex.continuous_ofReal.tendsto 0 |>.comp hp).mul_const v

/-- One physically selected final station with its actual position test and
field comparison. For every independent historical prescription, the error
after changing this real Wilson clock has two specified summands. The second
tends to zero for each fixed finite coefficient; no uniform rate in growing
epoch, word, or perturbative order is asserted here. -/
theorem funded {hG : G.Simple} {ε : ℝ} {T : Campaign R} (W : Campaign.Pillars R T)
    (fund : FundedOriginalProperties.{u} hG ε W) (base : Extraction.Order) :
    ∃ (next : Extraction.Order) (S : Table R.family.book)
      (F : Spec.Final R.family (base.refine next) S)
      (H : (Climb.Bel R.family.book).Hierarchy) (Z : Trace.Terrace.Arch R.family)
      (l : Ultrafilter (ℕ×ℕ)) (P P' : ℝ → Spin.change S 4) (φ : E4 → ℝ)
      (a d e : ℝ → ℝ), Trace.Pilot.Bliss F l Z H ∧
      Trace.Target.XScheme F hG H l P P' φ ∧ Trace.Target.FieldComparison F H Z P P' a d e ∧
      ∀ (N : WilsonPrescription G) (c per i B : ℕ),
        (R.family.S.denominator c).val = N.run.ratio ^ i →
        (R.family.S.period per).val = N.run.finalSide.side.val * N.run.ratio^(N.run.reserve*i*i) →
        ∀ (P₀ : Handoff.Directory N i B) (v : List (Birth G)) (k : ℕ),
          Handoff.Directory.requested v + k ≤ B →
          let n := R.family.side c per
          let ev := even_iff_two_dvd.mpr (ActualOriginalFiniteCoefficients.side_admissible R c per).2
          let value := PowerSeries.coeff k (Birth.scan v (row R N.scheme n ev))
          let delta := clockCorrection (Trace.Sundial.glo P') (Trace.Pilot.wilson Z) k value
          (∀ r : ℝ, Complex.ofReal ((Trace.Sundial.glo P' r / Trace.Pilot.wilson Z r)^k) * value -
            Complex.ofReal (PowerSeries.coeff k (P₀.product v)) =
            Complex.ofReal (PowerSeries.coeff k
              (Birth.scan v (WilsonEpochPositionCoefficients.residual R N.scheme n))) + delta r) ∧
          Tendsto delta Trace.Pilot.trail (𝓝 0) := by
  rcases fund with ⟨_,_,_,_,_,_,_,_,_,stations,_⟩
  obtain ⟨next,S,F,_,_,_,_,_,_,_,H,Z,l,bliss,P,P',_,φ,a,d,e,_,xs,fc,_,_⟩ := stations base
  refine ⟨next,S,F,H,Z,l,P,P',φ,a,d,e,bliss,xs,fc,?_⟩
  intro N c per i B hn hp P₀ v k hk n ev value delta
  refine ⟨fun r => ?_,small fc.calibrationX k value⟩
  have h := common R N c per i B ⟨hn,hp⟩ P₀ v k hk
  rw [← h]
  dsimp only [delta,clockCorrection]
  push_cast
  ring

end YM.Integration.WilsonEpochPhysicalStation
end

