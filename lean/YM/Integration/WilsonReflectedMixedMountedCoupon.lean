import YM.Integration.WilsonReflectedMixedThermalArms
import YM.Integration.WilsonReflectedPublicMountedInvoice
import YM.Integration.WilsonReflectedPublicFiledSingle
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedMountedCoupon
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "C₀" => R.family

open WilsonReflectedPublicOrientedFaces WilsonReflectedOriginalTwoDeposit
open WilsonThermometerReflectedTrajectory
open OPE.Therm


open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonReflectedPublicCommonDose
open WilsonReflectedPublicGuardedColumns
local notation "β" => R.family.path.levels.clock.hatBeta

/-- Read each signed inverse and original arm on the very census already filed on
the reporter.  The multiplier used on the physical word still contains its
own occupancy charge. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d e:I→ℕ):
    ∀ᶠ f:ℕ in atTop,∀N p K (up:f≤K)(live:K≤N)(A:(i:I)→Arm R (d i) N p f K)
    (V:(i:I)→Sight C₀ (d i) p)(u:(i:I)→Emblems C₀ (d i))
    (home:∀i,Opened C₀ (d i) f p)
    (_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p (d i)
      (digits R N p 0) (V i) (u i))(_ref:∀i k,k≤d i→(C₀).ref k≤f)
    (cap:I→ℝ)(_cp:∀i,0≤cap i)
    (_earned:∀i,Priced R (A i) (cap i*((β f)^(e i+1))⁻¹*((C₀).S.a f)^(d i)))
    (names:Census I)(t:ℕ),
    let turn:=fun i=>((A i).s,(A i).b)
    let root:=fun i=>(A i).o
    let y:=fun i=>offer R (A i).Y (home i) (up.trans live)
    let data:=fun i=>reduce (y i)
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn root data V u names (up.trans live) t →
    ∀i,let χ:=WilsonThermometerMarchSource.charge (y i)
       let c:=dose χ (cap i) 1
       let w:=WilsonReflectedPublicMountedInvoice.wage R f
       let Ω:=orbitCost ((C₀).labels.level (d i))
       let old:=marked R (N:=N) 0 (turn i) (root i) (V i) (u i) (data i) f
       ∃X E,Joined R (A i) up live (c:ℂ) (((c*χ:ℝ):ℂ) • old) w (Ω*(1+w))
         ((2+Ω)*((β f)^(e i))⁻¹) X E:=by
  classical
  filter_upwards [Filter.eventually_all.mpr (fun i=>(WilsonReflectedPublicSignedFare.original R simple shop (d i) (e i)).and
    (WilsonReflectedPublicMountedInvoice.original R simple shop (d i)))] with f funds
  intro N p K up live A V u home enrolled ref cap cp earned names t turn root y data filed i χ c w Ω old
  obtain ⟨Q,form,size,paid,soft,hard,field⟩:=(funds i).2 (up.trans live) (home i) (enrolled i) (A i).Y (turn i) (root i)
  have peer:=WilsonReflectedPublicFiledSingle.original R d (fun i=>(A i).Y) V u home (up.trans live)
    enrolled (fun i k hk=>(ref i k hk).trans (up.trans live)) turn root names t filed i
  have offerE:=(funds i).1 N p K (A i) up live (ref i _ le_rfl) (cap i) 1 (cp i) zero_le_one
  have clock:R.alloy.B.a.clock.hatBeta f=β f:=rfl
  rw [clock] at offerE
  obtain ⟨E,charged⟩:=offerE (by simpa only [mul_one] using earned i) 1 (by simp)
  let a:ℝ:=(2+Ω)*((β f)^(e i))⁻¹
  have ap:0≤a:=mul_nonneg (by linarith only [orbitCost_one_le (R.family.labels.level (d i))]) <|
    inv_nonneg.mpr (pow_nonneg (zero_le_one.trans ((R.family.path.levels.fits.delayed f).le)) _)
  have reorder:(2+Ω)*cap i*((β f)^(e i))⁻¹*1=a*cap i*1:=by dsimp [a];ring
  rw [reorder] at charged
  exact ⟨_,_,WilsonReflectedPublicCommonRows.original R (A i) up live χ (cap i) 1 a (le_max_left ..) ap old
    w (Ω*(1+w)) Q E form size paid soft hard field peer charged⟩

end YM.Integration.WilsonReflectedMixedMountedCoupon
end
