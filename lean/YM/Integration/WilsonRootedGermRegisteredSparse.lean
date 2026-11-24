import YM.Integration.WilsonRootedGermSparseNumerator
import YM.Integration.WilsonRootedGermReportingTariff
import YM.Integration.WilsonInvariantActionCurvatureGate

/-! Both marked arms are transported by the same original reporting layout before testing the sparse numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermRegisteredSparse
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker MergeProof
open OPE.Therm MS.Local.Physical LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato ActualRunPacketRetuning MergeProof.Accent Pert.Asymptotics RG17
open WilsonInheritedRegisteredField WilsonMatrixTicketLanesReportedPivot Trace.Physical.GermGraph Next.Rank.Price
open WilsonRootedGermSparseNumerator WilsonRootedGermSparseCorrelation WilsonRootedGermFlagMass
open scoped Classical Topology BigOperators
variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple)
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (Q:MS.Land.Prescription B) (σ:ℝ)
variable (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))

def amount (i N p : ℕ) (v : R.family.label 4) : ℝ :=
  (R.family.S.a i^4)⁻¹*Next.UVStress.quota R.family 4 i N p v

private theorem amount_nonneg (i N p : ℕ) (v : R.family.label 4) : 0 ≤ amount R i N p v :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg (R.family.S.a_pos i).le 4)) (Work.G08.size_nonneg _ _)

private theorem allocated (i N p : ℕ) (v : R.family.label 4) :
    Next.UVStress.quota R.family 4 i N p v ≤ R.family.S.a i^4*amount R i N p v := by
  unfold amount
  rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (R.family.S.a_pos i).ne'),one_mul]

def row (v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period))
    (U:Config G (R.family.side (d.level+1) d.period)) : ℂ :=
  R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o U -
    WilsonInvariantActionFineCurvature.masked R simple J A Q σ d v o U

variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
    (V:Ultrafilter (ℕ×ℕ)) (cut:(V:Filter (ℕ×ℕ)) ≤ L.lens)

/-- The unmodified correlated covariate lives exactly on the admitted local rejection, also inside the sparse cut. -/
theorem supported (e:ℕ) (v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period)) (age:R.family.ref 4 ≤ d.level+1) :
    (WilsonInvariantActionCurvatureGate.rejected R simple J A Q σ d o).indicator
      (sparse R e (d.level+1) d.period (row R simple J A Q σ d v o)) =
        sparse R e (d.level+1) d.period (row R simple J A Q σ d v o) := by
  funext U
  by_cases bad : U∈WilsonInvariantActionCurvatureGate.rejected R simple J A Q σ d o
  · exact Set.indicator_of_mem bad _
  rw [Set.indicator_of_notMem bad]
  have equal : row R simple J A Q σ d v o U=0 := sub_eq_zero.mpr (WilsonInvariantActionCurvatureGate.clear R simple J A Q σ d o v age U bad)
  simp [sparse,slice,equal]

include Φ L V cut
/-- Fix the normalized reporting order, then admit every cutoff, period, pair of filed labels and occupied roots. -/
theorem purchased (stoves : Poetry R.family.path.levels) (e q:ℕ) {η:ℝ} (hη:0<η) :
    ∀ᶠ m:ℕ in atTop, ∀ d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)), d.level=m →
      ∀ (r:ℝ) (w v:R.family.label 4) (x y:Site (R.family.side (d.level+1) d.period)),
      let i := d.level+1
      let z := (d.cutoff,d.period)
      let a := atRef L 4 r z w
      let b := atRef L 4 r z v
      let D := row R simple J A Q σ d b y
      let Y := numerator R i d.cutoff d.period a x
        ((WilsonInvariantActionCurvatureGate.rejected R simple J A Q σ d y).indicator (sparse R e i d.period D))
      let Z := forced R.makes (Nat.succ_le_of_lt d.below) a x
      let μ := scene R.family.path d.cutoff d.period i
      Integrable (fun U=>Z U*D U) μ ∧ Integrable Y (prior G (R.family.side i d.period)) ∧
       ‖(∫ U,Z U*D U ∂μ)-(∫ U,Y U ∂prior G (R.family.side i d.period))‖ ≤
        η*regulatorRun R.family d.cutoff d.period i^q*amount R i d.cutoff d.period b*
          (safety R.family i*stock R.family i*amount R i d.cutoff d.period a) := by
  obtain ⟨C,cpos,s,bound⟩ := WilsonInvariantActionCurvatureGate.original R simple J A Q σ Φ L V cut 0
  have ready := (tendsto_add_atTop_nat 1).eventually (WilsonRootedGermSparseNumerator.purchased R simple stoves e (s+q+1))
  have rate := (tendsto_add_atTop_nat 1).eventually (WilsonRootedGermReportingTariff.earned R simple s q (C:=C) hη)
  have late := (tendsto_add_atTop_nat 1).eventually (eventually_ge_atTop (R.family.ref 4))
  filter_upwards [ready,rate,late] with m pay price age
  intro d dated r w v x y
  subst m
  let i := d.level+1
  let N := d.cutoff
  let p := d.period
  let a := atRef L 4 r (N,p) w
  let b := atRef L 4 r (N,p) v
  let D := row R simple J A Q σ d b y
  let u := amount R i N p a
  let v₁ := amount R i N p b
  let β := R.family.path.levels.clock.hatBeta i
  let H := C*β^s*v₁
  let tax := safety R.family i*stock R.family i*u
  have live : i≤N := d.below
  have vs : 0 ≤ v₁ := amount_nonneg R i N p b
  have tp : 0 ≤ tax := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (stage R.family i).columns_ge)) (amount_nonneg R i N p a)
  have raw := bound d b y v₁ vs age (by simp [v₁,amount,i,N,p])
  have vb : 0 ≤ β := zero_le_one.trans (R.family.path.levels.fits.delayed i).le
  have amplitude (U) : ‖D U‖ ≤ H := by
    by_cases lost : U∈WilsonInvariantActionCurvatureGate.rejected R simple J A Q σ d y
    · change ‖R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period b) y U - WilsonInvariantActionFineCurvature.masked R simple J A Q σ d b y U‖ ≤ C*(R.family.path.levels.clock.hatBeta (d.level+1))^s*v₁
      have au := raw U
      rw [Set.indicator_of_mem lost] at au
      exact au
    have zero : D U=0 := sub_eq_zero.mpr (WilsonInvariantActionCurvatureGate.clear R simple J A Q σ d y b age U lost)
    rw [zero,norm_zero]
    exact mul_nonneg (mul_nonneg cpos.le (pow_nonneg vb _)) vs
  obtain ⟨integ,sparse_int,closed⟩ := pay N p live age a x u (allocated R i N p a) D
    (WilsonInvariantActionWithinFine.expense R simple Q J A σ d b y age) H amplitude
  dsimp only
  rw [supported R simple J A Q σ d e b y age]
  refine ⟨integ,sparse_int,closed.trans ?_⟩
  let expFee := Real.exp (-((s+q+1:ℕ):ℝ)*Trace.Terrace.Lyra R.family.path.levels i)
  change H*expFee*tax ≤ η*regulatorRun R.family N p i^q*v₁*tax
  calc
    H*expFee*tax = (C*β^s*expFee)*v₁*tax := by dsimp only [H];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (price N p live) vs) tp

end YM.Integration.WilsonRootedGermRegisteredSparse
