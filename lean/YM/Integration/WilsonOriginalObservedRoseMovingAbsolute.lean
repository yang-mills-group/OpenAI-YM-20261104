import YM.Integration.WilsonOriginalObservedRoseRawAbsolute
import YM.Integration.WilsonOlderFreshSoftSocketOptical
import YM.Integration.WilsonSeparatedPrefixKineticGeometry

/-! On the actual lower regulator, all high Taylor grades use the moment-zero structural price, at arbitrary original test and at every occupied coefficient of the true finite K roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseMovingAbsolute
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftSocketRestored (stopped coin rated)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (mass value)
open WilsonCoeffUV.Winding
open scoped Topology BigOperators Classical

variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(Q:ℕ)

open Filter Real
open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshSoftSocketOptical (fixed)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "g" => Pert.Asymptotics.regulatorRun R.family

theorem original (S:Finset I)(occupied:S.Nonempty)(simple:G.Simple)(A:ℕ):
    ∀ᶠ v:ℕ in atTop,∀V:Realm G (Q+1) Credit.leanC,
      ∀draw:V.draws=R.family.path.levels,V.paid=R.metals.O→V.y=zz R.family.path.levels→
      V.anchor≤v→Dormitory V (WilsonCoeffUV.Wheel.Mark.mass d S) 0 Credit.leanC→
      ∀N per K c:ℕ,v≤c→c≤K→K≤N→v+1≤K→σ K-σ v≤A*Real.log (H v)→
      ∀(κ:(i:I)→Knob (D i))(pt:I→Chamber)(cells:Digits V.draws I)
        (w:(i:I)→R.family.label (d i))(y:I→ Cover)(test:Pen D S→L[ℝ]ℝ),
      let path:=cast (congrArg (fun l=>Digits l I) draw) cells
      let θ:=g N per v
      let row:=normalized R d κ pt N per K c v path S w y test
      ∀k:ℕ,k≤Q → ‖row k θ‖≤(∑q:Selection R d S,‖weight R d N per K w S q‖)*
        (‖test‖*(2*fixed R D d Q S)*θ⁻¹):=by
  obtain ⟨_,_,clock⟩:=WilsonSeparatedPrefixKineticGeometry.corridor R simple A
  have grant:=WilsonOlderFreshSoftSocketOptical.original R D d Q S simple (A:ℝ) 1 (Nat.cast_nonneg _) zero_lt_one
  filter_upwards [clock,grant,WilsonSeparatedPrefixKineticGeometry.spend R simple 1 0] with v reach pads liquid
  intro V draw paid kinetic first dorm N per K c vc ck live next width κ pt cells w y test path θ row
  have vk:=vc.trans ck
  have positive:0<θ:=ActualRunKernelPackets.regulator_pos R N per v (vk.trans live)
  have one:1≤θ⁻¹:=by simpa using liquid N per (vk.trans live)
  have small:θ≤1:=by
    have cost:1≤1/θ:=by simpa only [one_div] using one
    simpa using (le_div_iff₀ positive).mp cost
  have heat:0<H v:=zero_lt_one.trans ((R.family.path.levels).fits.delayed v)
  have log_inc(t:ℕ)(ht:v≤t):Real.log (H v)≤Real.log (H t):=
    Real.log_le_log heat (WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le ht)
  have sum:σ K-σ v≤(A:ℝ)*(1+Real.log (H (v+1))):=
    width.trans (mul_le_mul_of_nonneg_left (by linarith [log_inc (v+1) (Nat.le_succ v)]) (Nat.cast_nonneg _))
  have long:WilsonSeparatedPrefixKineticGeometry.span R A v K:=
    width.trans (mul_le_mul_of_nonneg_left (log_inc K vk) (Nat.cast_nonneg _))
  obtain ⟨Z,front,march,grossPrice⟩:=pads V first draw kinetic N per K c vc ck live next sum
  have ratio:=((reach K N per vk live long).2 K vk le_rfl).1
  have low:θ/2≤g N per K:=by
    have h:3/4*θ≤g N per K:=(le_div_iff₀ positive).mp ratio
    linarith
  have invK:(g N per K)⁻¹≤2*θ⁻¹:=calc
    _≤(θ/2)⁻¹:=inv_anti₀ (half_pos positive) low
    _=_:=by rw [inv_div];ring
  have fixed0:0≤fixed R D d Q S:=WilsonOlderFreshSoftSocketOptical.fixed_nonneg R D d Q S
  rw [Real.rpow_one] at grossPrice
  have upstairs:gross R D d Q S Z Z≤fixed R D d Q S*(2*θ⁻¹):=
    grossPrice.trans (mul_le_mul_of_nonneg_left invK fixed0)
  intro k kept
  have published:=WilsonOriginalObservedRoseRawAbsolute.original R D d Q S occupied V draw paid dorm N per K c v first vc ck live Z Z front march κ pt cells w y test θ positive.le small k kept
  apply published.trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun _ _=>norm_nonneg _)
  calc ‖test‖*gross R D d Q S Z Z≤‖test‖*(fixed R D d Q S*(2*θ⁻¹)):=mul_le_mul_of_nonneg_left upstairs (norm_nonneg test)
       _=‖test‖*(2*fixed R D d Q S)*θ⁻¹:=by ring

end YM.Integration.WilsonOriginalObservedRoseMovingAbsolute
end
