import YM.Integration.WilsonOlderFreshSoftSocketFare
import YM.Integration.WilsonIndependentCollarOpticalSpan

/-! The two genuine chronological intervals share one dated optical credit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketOptical
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftSocketRestored (stopped coin)
open WilsonIndependentCollarOrdinaryWeak (price)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonCoeffUV.Winding
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(p:ℕ)

open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure normalized cost)
open WilsonReportingAbsoluteInletForecastBooks (value)
open ActualRunPhysicalPages Pert.Asymptotics
local notation "g_" => regulatorRun R.family

open WilsonOlderFreshSoftSocketGross (seed)
open Filter
open WilsonCoeffUV.Bank.Ticket
open WilsonIndependentCollarOrdinaryWeak (price)
open scoped Topology
def share (C:Credit):Credit:=⟨C.d*2,C.x^2,one_le_pow₀ C.good⟩

def fixed (S:Finset I):ℝ:=((p+1:ℕ):ℝ)*(seed R D d p)^S.card

theorem fixed_nonneg (S:Finset I):0≤fixed R D d p S:=by
  have a:=((WilsonIndependentCollarSeedTariff.original G D d p).choose_spec).1
  have b:=((WilsonIndependentCollarPointBill.original R D d p (w:=1) zero_lt_one).choose_spec).1
  have h:0≤ seed R D d p:=mul_nonneg (zero_le_one.trans a) (zero_le_one.trans b)
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h _)

theorem original (S:Finset I)(simple:G.Simple)(A δ:ℝ)(a0:0≤A)(δ0:0<δ):
    ∀ᶠ v:ℕ in atTop,∀(V:Realm G (p+1) Credit.leanC),V.anchor≤v→
      V.draws=R.family.path.levels→V.y=zz R.family.path.levels→
      ∀N per K c,v≤c→c≤K→K≤N→v+1≤K→
      R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
      ∃Z:ℝ,PadRank V c K Z ∧ PadRank V v c Z ∧
        gross R D d p S Z Z≤fixed R D d p S*(g_ N per K)⁻¹^δ:=by
  let P:=price G (mass d S) p
  filter_upwards [WilsonIndependentCollarOpticalSpan.original R simple (share P) A a0 δ δ0] with v account
  intro V first draw heat N per K c vc ck live vk span
  let β:=R.family.path.β N per K
  have band:=(R.makes.wilson.represents N per K live).band.1
  change R.family.path.levels.clock.hatBeta K/2≤β at band
  have mono:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le vk
  have warm:R.family.path.levels.clock.hatBeta (v+1)/2≤β:=by linarith only [mono,band]
  have add:v+(K-v)=K:=by omega
  have pool:=account p V first draw heat (K-v) β warm (by rw [add];exact span)
  rw [add] at pool
  obtain ⟨Z,rank,bought⟩:=pool
  refine ⟨Z,rank.zone vc le_rfl,rank.zone le_rfl ck,?_⟩
  have βg:Real.sqrt β=(g_ N per K)⁻¹:=by change Real.sqrt β=((Real.sqrt β)⁻¹)⁻¹;rw [inv_inv]
  rw [βg] at bought
  calc gross R D d p S Z Z=fixed R D d p S*((share P).buy Z):=by
         unfold gross fixed Credit.buy share
         dsimp only [P]
         rw [pow_mul]
         ring
       _≤_:=mul_le_mul_of_nonneg_left bought (fixed_nonneg R D d p S)

end YM.Integration.WilsonOlderFreshSoftSocketOptical
end
