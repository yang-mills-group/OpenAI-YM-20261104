import YM.Integration.WilsonReflectedPublicOrientedCoefficient
/-! The original before-cutoff readout grant already budgets the change of
coordinates of a reflected nonbare source at the fine side of each step. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicRotationFare
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open RG05Readout.Copper RG05Readout.Native
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
local notation "C" => R.family
local notation "B₀" => WilsonThermometerOffsetLedger.cash R

private theorem ticket {d:ℕ} {L:Side} {K c β B τ book:ℝ} (k:1≤K) (cp:1≤c) (bp:0≤β)
    (ap:0≤Doors.rate L) (tr:0≤τ) (base:0≤B)
    (paid:2*tollP d K c β + tollV d L K c (Doors.rate L) β*τ*B ≤ book) : τ*B ≤ book := by
  have kn:0≤K:=zero_le_one.trans k
  have cn:0≤c:=zero_le_one.trans cp
  have ac:1≤aCost d K:= k.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg kn _)))
  have tn:0≤tollP d K c β:=by unfold tollP; exact mul_nonneg (zero_le_one.trans ac) (by positivity)
  have tv:1≤tollV d L K c (Doors.rate L) β :=by
    unfold tollV
    apply le_add_of_le_of_nonneg (one_le_mul_of_one_le_of_one_le ac ?_) (by positivity)
    linarith [mul_nonneg kn ap]
  have x:τ*B ≤tollV d L K c (Doors.rate L) β*τ*B :=by
    rw [mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg tr base) tv
  exact x.trans ((le_add_of_nonneg_left (mul_nonneg (by norm_num) tn)).trans paid)

include simple shop in
theorem original (d:ℕ) : ∀ᶠ f in atTop,∀ N p, f≤N →
    let W:=(C).path.rep N p f
    turnCost W.p.order W.p.power*B₀ d f ≤1+Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta f)) := by
  obtain ⟨b,early⟩:=eventually_atTop.mp (WilsonThermometerOffsetLedger.original R simple shop d)
  have infinity:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  obtain ⟨j₀,large⟩:=eventually_atTop.mp (infinity.eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (max b j₀+1)] with f hf N p live
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (n:=f) (by omega)
  let L:=(C).S.block j
  let W:=(C).path.rep N p (j+1)
  let τ:=turnCost W.p.order W.p.power
  have hj:b≤j:=by omega
  have receipt:=(early j hj).1.toll p j N le_rfl (by omega)
  obtain ⟨s,K,c,β,T,Q,plot,_,_,_,fare,_⟩:=receipt.author
  have tr:0≤τ:=zero_le_one.trans (shift_pays (R:=W))
  have h:=ticket plot.cursor.fits plot.posp plot.b_pos plot.a_pos tr (zero_le_one.trans receipt.pos.1) fare
  have side:1≤(L.val:ℝ):=by exact_mod_cast L.property
  have exponent:(1:ℝ)/(((C).path.levels.clock.J (j+1):ℝ)+1) ≤ 1 :=by
    apply (div_le_one₀ (by positivity)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) ((C).path.levels.clock.J (j+1))]
  have clock:0<R.alloy.B.a.clock.hatBeta j :=lt_of_lt_of_le zero_lt_one (large j (by omega))
  have mono:=Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ j)
  have lognon:0≤Real.log (R.alloy.B.a.clock.hatBeta j):=Real.log_nonneg (large j (by omega))
  refine h.trans (le_trans (Real.rpow_le_rpow_of_exponent_le side exponent) ?_)
  rw [Real.rpow_one]
  exact (shop.preMesh j).trans (add_le_add_right
    (Real.log_le_log (by positivity) (add_le_add_right (Real.log_le_log clock mono) _)) _)

end YM.Integration.WilsonReflectedPublicRotationFare
end
