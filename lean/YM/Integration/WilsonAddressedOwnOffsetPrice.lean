import YM.Integration.WilsonAddressedReportedColumns
import YM.Integration.WilsonThermometerOffsetLedger

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedOwnOffsetPrice
open Function Filter MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical ProjectorNext.Equivariance
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOffsetLedger WilsonAddressedReportedColumns
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G)

private theorem threshold_price (n : ℕ) :
    max 1 (R.family.path.levels.clock.threshold n)⁻¹ ≤
      1+Real.sqrt (R.family.path.levels.clock.hatBeta n) := by
  let A := R.family.path.levels.clock
  have big : 1 ≤ A.monitor n := Real.one_le_exp (sq_nonneg _)
  have bound : (A.threshold n)⁻¹ ≤ Real.sqrt (A.hatBeta n) := by
    change ((Real.sqrt (A.hatBeta n))⁻¹ * A.monitor n)⁻¹ ≤ _
    rw [mul_inv,inv_inv]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (inv_le_one_of_one_le₀ big)
  exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    (bound.trans (le_add_of_nonneg_left zero_le_one))

/-- At every age the same transported palette yields the genuine print and all
    finite inspected Wilson sources on the physical child path. The selection
    threshold precedes both regulators and every choice of reference vector. -/
theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop,∀ N p (_live : m≤N) (z : Site (R.family.side N p)),
      ∃ (V : Sight R.family d p) (r : Emblems R.family d),
        Enrolled R.makes R.doors (cash R) m N p d (digits R N p z) V r ∧
        ∀ (y : Palette R.family d) j (away : m≤j) (_reached : j≤N),
          let P := R.family.path.rep N p j
          let v := finer r away y
          let h := R.family.path.levels.clock.hatBeta j
          let mass := (2+Real.log (2+Real.log h)) *
            (Real.exp (ε*(R.family.S.scale j-R.family.S.scale m))*size y)
          ∃ x : Palette R.family d,
            Printed R.family d P 0 (kappa R.family.path j) (V j v) x v (cash R d j*size v) ∧
            size x ≤ mass ∧ size (weightsAt P.p.threshold x) ≤ (1+Real.sqrt h)^toll R.family d*mass := by
  obtain ⟨b,paid⟩ := eventually_atTop.mp (WilsonThermometerOffsetLedger.original R simple shop d)
  obtain ⟨b',wrapped⟩ := eventually_atTop.mp (RG05Readout.Copper.wraps R.family simple d)
  obtain ⟨b'',levels⟩ := eventually_atTop.mp (R.alloy.B.a.fits.deep.eventually_ge_atTop d)
  filter_upwards [eventually_ge_atTop b,eventually_ge_atTop b',eventually_ge_atTop b'',
    string_paid (C:=R.family) hε] with m active folded late tolls N p live z
  obtain ⟨V,r,H⟩ := enroll R.makes (paid m active).1 live (digits R N p z)
  refine ⟨V,r,H,?_⟩
  intro y j away reached P v h mass
  have hv : size v≤Real.exp (ε*(R.family.S.scale j-R.family.S.scale m))*size y :=
    (H.inverse le_rfl away reached y).trans (mul_le_mul_of_nonneg_right (tolls j away) (size_ge _))
  have funded := (paid j (active.trans away)).2
  have eq := (R.makes.wilson.represents N p j reached).vac
  have ord : d ≤ P.p.order := by rw [show P.p=_ from eq]; exact (levels j (late.trans away)).trans (R.b.clock.stage j).1
  have pw : d ≤ P.p.power := by rw [show P.p=_ from eq]; exact (levels j (late.trans away)).trans (R.b.clock.stage j).2
  have pos : 0 < P.p.threshold := by
    rw [show P.p=_ from eq]
    exact (R.family.path.levels.budget j).threshold_pos
  obtain ⟨x,printed,stored,fee⟩ := WilsonAddressedReportedColumns.original R z H away reached v ord pw pos
  have thin : wrap_price d R.family * Germ.wraps P.p (R.family.side j p) ≤ 1 := by
    rw [show P.p=_ from eq]
    refine ((wrapped j (folded.trans away) p).1).trans ?_
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (show 1 ≤ ((R.family.S.block j).val:ℝ) by
      exact_mod_cast (R.family.S.block j).property))
  have upper : cash R d j ≤ 1+Real.log (2+Real.log h) := funded.2
  have large : 1+wrap_price d R.family * Germ.wraps P.p (R.family.side j p) * cash R d j ≤
      2+Real.log (2+Real.log h) := calc
    _ ≤ 1+cash R d j := add_le_add_right
      ((mul_le_mul_of_nonneg_right thin (zero_le_one.trans funded.1)).trans_eq (one_mul _)) _
    _ ≤ _ := by linarith only [upper]
  let originalMass := (1+wrap_price d R.family*Germ.wraps P.p (R.family.side j p)*cash R d j)*size v
  have f : originalMass ≤ mass :=
    mul_le_mul large hv (size_ge _) (by linarith only [funded.1,upper])
  have θ : max 1 P.p.threshold⁻¹ ≤ 1+Real.sqrt h := by rw [show P.p=_ from eq]; exact threshold_price R j
  have mpos : 0≤originalMass := (size_ge x).trans stored
  exact ⟨x,printed,stored.trans f,fee.trans (mul_le_mul
    (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) θ _) f mpos
    (pow_nonneg (by positivity) _))⟩

end YM.Integration.WilsonAddressedOwnOffsetPrice
