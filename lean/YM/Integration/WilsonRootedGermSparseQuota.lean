import YM.Integration.WilsonRootedGermRegisteredSparse

/-! Prepay both authentic original label tariffs, including the thermal column factor, on one reported date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermSparseQuota
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker MergeProof
open OPE.Therm MS.Local.Physical LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato ActualRunPacketRetuning MergeProof.Accent Pert.Asymptotics RG17
open WilsonInheritedRegisteredField WilsonMatrixTicketLanesReportedPivot Trace.Physical.GermGraph Next.Rank.Price
open WilsonRootedGermSparseNumerator WilsonRootedGermSparseCorrelation WilsonRootedGermRegisteredSparse
open private amount_nonneg from YM.Integration.WilsonRootedGermRegisteredSparse
open scoped Classical Topology BigOperators
variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple)

/-- The very same thermal tariff that buys the dense flag income also buys the incumbent column. -/
theorem physical_column (stoves:Poetry R.family.path.levels) (i:ℕ) :
    safety R.family i*stock R.family i ≤ R.family.path.levels.clock.hatBeta i := by
  let P := R.family.path.levels.params i
  let β := R.family.path.levels.clock.hatBeta i
  have bill := (stoves.stage i).jobs
  change 100000*(1+P.paths+P.supportExponent+P.clip.relaxation+P.width+P.columns+P.clip.direct+P.clip.linear)≤Real.log β at bill
  have column : P.columns ≤ Real.log β := by linarith only [bill,P.paths_pos,P.price_pos,P.width_pos,P.columns_ge,P.clip.radius_pos,P.clip.quadratic_pos,P.clip.tail_pos]
  have hβ : 0<β := zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have bound : safety R.family i≤1 := Extra.Multi.divisor_le R.family i
  calc
    _ ≤ 1*P.columns := mul_le_mul_of_nonneg_right bound (zero_le_one.trans P.columns_ge)
    _ ≤ β := (one_mul _).le.trans (column.trans ((Real.log_le_sub_one_of_pos hβ).trans (sub_le_self _ zero_le_one)))

private theorem square {i N p:ℕ} (live:i≤N) :
    regulatorRun R.family N p i^2*R.family.path.levels.clock.hatBeta i ≤ 2 := by
  let β := R.family.path.β N p i
  let b := R.family.path.levels.clock.hatBeta i
  have hβ : 0<β := Overlay.beta_positive R.makes.wilson live
  have band : b/2≤β := (R.makes.wilson.represents N p i live).band.1
  change (Real.sqrt β)⁻¹^2*b≤2
  rw [inv_pow,Real.sq_sqrt hβ.le]
  simpa only [div_eq_inv_mul] using (div_le_iff₀ hβ).mpr (show b≤2*β by linarith only [band])

variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (Q:MS.Land.Prescription B) (σ:ℝ)
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
    (V:Ultrafilter (ℕ×ℕ)) (cut:(V:Filter (ℕ×ℕ)) ≤ L.lens)

/-- Both integrals keep the original finite regulator and old insertion. -/
def discrepancy (e:ℕ) (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
    (r:ℝ) (w v:R.family.label 4) (x y:Site (R.family.side (d.level+1) d.period)) : ℂ :=
  let i := d.level+1
  let a := atRef L 4 r (d.cutoff,d.period) w
  let b := atRef L 4 r (d.cutoff,d.period) v
  let D := row R simple J A Q σ d b y
  let Y := numerator R i d.cutoff d.period a x ((WilsonInvariantActionCurvatureGate.rejected R simple J A Q σ d y).indicator (sparse R e i d.period D))
  (∫ U,forced R.makes (Nat.succ_le_of_lt d.below) a x U *D U ∂scene R.family.path d.cutoff d.period i) -
      ∫ U,Y U ∂prior G (R.family.side i d.period)

include Φ L V cut

theorem purchased (stoves : Poetry R.family.path.levels) (e q old fresh:ℕ) {η:ℝ} (hη:0<η) :
    ∀ᶠ m:ℕ in atTop, ∀ d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)), d.level=m →
      ∀ (r:ℝ) (w v:R.family.label 4) (x y:Site (R.family.side (d.level+1) d.period)) (oldQuota freshQuota:ℝ),
      0≤oldQuota → 0≤freshQuota →
      let i := d.level+1
      let b := R.family.path.levels.clock.hatBeta i
      amount R i d.cutoff d.period (atRef L 4 r (d.cutoff,d.period) w) ≤ b^old*oldQuota →
      amount R i d.cutoff d.period (atRef L 4 r (d.cutoff,d.period) v) ≤ b^fresh*freshQuota →
      ‖discrepancy R simple J A Q σ Φ L e d r w v x y‖ ≤ η*regulatorRun R.family d.cutoff d.period i^q*freshQuota*oldQuota := by
  let T := old+fresh+1
  let δ := η/(2:ℝ)^T
  have two : 0<(2:ℝ)^T := pow_pos zero_lt_two _
  have pos : 0<δ := div_pos hη two
  filter_upwards [WilsonRootedGermRegisteredSparse.purchased R simple J A Q σ Φ L V cut stoves e (q+2*T) pos] with m sale
  intro d dated r w v x y M₁ M₂ p₁ p₂
  dsimp only
  intro cap₁ cap₂
  let i := d.level+1
  let N := d.cutoff
  let p := d.period
  let a := atRef L 4 r (N,p) w
  let c := atRef L 4 r (N,p) v
  let b := R.family.path.levels.clock.hatBeta i
  let g := regulatorRun R.family N p i
  have bpos : 0≤b := zero_le_one.trans (R.family.path.levels.fits.delayed i).le
  have gp : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have s₁ : 0≤amount R i N p a := amount_nonneg R i N p a
  have s₂ : 0≤amount R i N p c := amount_nonneg R i N p c
  have tax : 0 ≤ safety R.family i * stock R.family i := mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (stage R.family i).columns_ge)
  have raw := (sale d dated r w v x y).2.2
  have stock_paid := physical_column R stoves i
  have paid : (g^2*b)^T ≤ (2:ℝ)^T := pow_le_pow_left₀ (mul_nonneg (sq_nonneg g) bpos) (square R (d.below : i≤N)) T
  have field : ‖discrepancy R simple J A Q σ Φ L e d r w v x y‖ ≤ δ*g^(q+2*T)*amount R i N p c*(safety R.family i*stock R.family i*amount R i N p a) := raw
  refine field.trans ?_
  calc
    _ ≤ δ*g^(q+2*T)*(b^fresh*M₂)*(b*(b^old*M₁)) := by gcongr
    _ = δ*g^q*(g^2*b)^T*M₂*M₁ := by rw [pow_add,pow_mul,mul_pow,show b^T=b^old*b^fresh*b from by rw [show T=old+fresh+1 by rfl,pow_succ,pow_add]];ring
    _ ≤ δ*g^q*2^T*M₂*M₁ := by gcongr
    _ = _ := by
      change δ*g^q*2^T*M₂*M₁=η*g^q*M₂*M₁
      dsimp only [δ]
      field_simp [two.ne']

end YM.Integration.WilsonRootedGermSparseQuota
