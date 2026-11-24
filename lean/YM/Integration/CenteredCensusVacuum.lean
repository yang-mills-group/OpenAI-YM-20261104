import YM.Integration.OriginalCensusFusion
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-! Center the retained physical action while recording the scalar and
prescribed quadratic coupling on the canonical signed high-sector carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CenteredCensusVacuum

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open IterationFour IterationFour.Vacuum Extra.Iteration
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction.FundedCensusVacuum Pert.Asymptotics
open scoped Topology

variable {G : Gauge} {n : Side}

def record (Y Z : Rep G n) : Rep G n := { Z with v := Y.v }

theorem record_eval (Y Z : Rep G n) (z : Config G n) :
    (record Y Z).eval z = Z.eval z * Real.exp (Y.scalar - Z.scalar) := by
  have he : (record Y Z).exponent z = Z.exponent z + (Y.scalar - Z.scalar) := by
    unfold Rep.exponent Rep.scalar record
    ring
  rw [Rep.eval,he,Real.exp_add]
  change _ = (Real.exp (Z.exponent z)*Z.activities.gas Z.p z)*_
  change (Real.exp (Z.exponent z)*Real.exp (Y.scalar-Z.scalar))*Z.activities.gas Z.p z = _
  ring

theorem center (Y Z : Rep G n) {σ C Λ δ w σ' C' Λ' δ' w' : ℝ}
    (hy : Y.Lawful σ C Λ δ w) (hz : Z.Lawful σ' C' Λ' δ' w')
    (f : Config G n → ℝ) (he : ∀ z, Y.eval z = Z.eval z * Real.exp (-f z)) :
    Y.scalar = Z.scalar - f 1 ∧ ∀ z, Y.eval z =
      (record Y Z).eval z * Real.exp (-(f z-f 1)) := by
  have hflat := he 1
  rw [SectorNext.Vacuum.flat_density Y hy,SectorNext.Vacuum.flat_density Z hz,
    ← Real.exp_add] at hflat
  have hscalar : Y.scalar = Z.scalar - f 1 := by
    simpa only [sub_eq_add_neg] using Real.exp_injective hflat
  refine ⟨hscalar,fun z => ?_⟩
  rw [he z,record_eval,mul_assoc,← Real.exp_add,hscalar]
  congr 2
  ring

variable {V : Type} {J : Request V}

/-- A carrier with the exact original scalar, prescribed coupling, original
stencil and threshold, on the requested regular norm. The force inventory
and forced allowance come from the actual paid cluster on this torus. -/
theorem atStation (R : Run G) (A : NumericSchedule R.family J) (ε : ℝ)
    (m N per : ℕ) (hN : m < N) (hs : OriginalCensusFusion.AtStation R A ε m N per hN) :
    let S := station R N per m hN
    let L := R.alloy.B.a
    let W := R.alloy.B.kin.path N m
    let Y := R.family.path.rep N per m
    let X := ledger R.kit S.guide
    let D := discarded R.kit S.guide S.guide S.identity J.order
    let q := A.outputNorm m
    let H := (2*gStep (R.family.path.rep N per (m+1)).beta)^(J.order+1)
    let charge := ActualNextInheritedPrice.extractionFactor R A m*H
    let base (k : ℝ) := k-Averaging.delta (X.read D)
    let Z (k : ℝ) := record Y (Reset.after W (L.params m).clip q X D (base k) 0 0)
    let f k := WilsonLimitConstruction.FundedCensusComparison.action S J.order (base k)
    charge ≤ ε*regulatorRun R.family N per m^((J.order:ℝ)+1-J.eta) ∧
      ∀ k, (Z k).v = Y.v ∧ (Z k).beta = k ∧ (Z k).path = Y.path ∧ (Z k).clip = Y.clip ∧
        (Z k).p = q ∧ (Z k).p.threshold = Y.p.threshold ∧
        (Z k).Lawful (L.params m).width (L.params m).paths (L.clock.loopCap m)
          charge (L.clock.forcedAllowance m) ∧
        (NativeRequestedInputNorm.regularPayload (Z k).activities).Invoice q charge ∧
        ∀ (O : Tree.Forest (L.clock.op m per).ratio),
          (Reset.after W (L.params m).clip q X D (base k)
            (Song.weighty S.guide Chi.canonical O) 0).scalar - f k 1 = Y.scalar ∧
          ∀ z, Y.eval z = (Z k).eval z * Real.exp (-(f k z-f k 1)) := by
  intro S L W Y X D q H charge base Z f
  have hy : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN.le
  obtain ⟨_,hcharge,hz,he⟩ := hs
  refine ⟨hcharge,fun k => ?_⟩
  have hzero := hz (base k) 0
  have hbeta : (Z k).beta = k := by
    change (Reset.after W (L.params m).clip q X D (base k) 0 0).beta = k
    rw [hzero.2.2.1]
    exact sub_add_cancel k _
  have hp : (Z k).p.threshold = Y.p.threshold := by
    change q.threshold = (R.family.path.rep N per m).p.threshold
    rw [hy.vac]
    exact (A.output_norm m).threshold
  refine ⟨rfl,hbeta,(CommonConstruction.runAlong_actual_path R N m per hN.le).symm,
    hy.clip.symm,rfl,hp,⟨hzero.1.paths,hzero.1.labels⟩,hzero.2.1,fun O => ?_⟩
  let τ := Song.weighty S.guide Chi.canonical O
  let Zτ := Reset.after W (L.params m).clip q X D (base k) τ 0
  have h := center Y Zτ hy.good (hz (base k) τ).1 (f k) (he O (base k))
  exact ⟨h.1.symm,h.2⟩

end YM.Integration.CenteredCensusVacuum
end
