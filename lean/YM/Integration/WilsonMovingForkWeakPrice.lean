import YM.Integration.WilsonMovingForkWindowBooks
import YM.Integration.WilsonOriginalTwoFlatPublicNamedFare

/-! Registered weak wage of a physical field prescribed at its own scale. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMovingForkWeakPrice
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open scoped Topology Classical

open WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open scoped Classical Topology BigOperators
open GapsContact GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson
open Labels Source Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Matrix.Norms.Frobenius Classical
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalTwoFlatPublicFare (charge)
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
local notation "C" => R.family

private theorem clock (simple:G.Simple){r:ℝ}{j:ℕ}(dated:a j≤r):
    dock r ≤ (8+G.slopeConstant⁻¹)*(β j):=by
  have s:=Gauge.slopeConstant_pos simple
  have base:0≤(P).clock.bar:=(P).clock.bar_pos.le
  have b:1≤β j:=((P).fits.delayed j).le
  have first:=dock_fold (a j) r ((C).S.a_pos j) dated
  apply first.trans
  change 8+(C).S.scale j ≤ (8+G.slopeConstant⁻¹)*(β j)
  have size:(C).S.scale j ≤ (β j)/G.slopeConstant:=by
    apply (le_div_iff₀ s).mpr
    change _ ≤ (P).clock.bar+G.slopeConstant*(C).S.scale j
    linarith only [base]
  rw [div_eq_mul_inv] at size
  nlinarith only [size,b]

theorem original (simple:G.Simple)(_bliss:Bliss F l z H)(lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (d:ℕ)(x:RG17.Free C d):
    ∃K:ℝ,∃e:ℕ,1≤K ∧ ∀ᶠr in trail,∀{D k:ℕ}{s B:ℝ}{stock:Bank F l D s B}
      {cap:d≤D}{W:Vane C k}{fits:D≤k}{U:Spin.change S d}
      (A:Pair F stock cap W fits U r),W.checked f H k → W.wheel.r=r →
      (∀v:S.Field d, ‖U.symm v‖≤dock r*cost F d r v) →
      ∀j,W.k≤j →
        fee F A true (homogeneous F J Z r d x)≤K*(β j)^e:=by
  obtain ⟨C₁,e,one,old⟩:=WilsonReflectedPublicStationPrice.original C simple d
  obtain ⟨gate,late⟩:=eventually_atTop.mp old
  obtain ⟨C₂,pos,home⟩:=WilsonThermometerUnitFilingFourPoolRent.converted F J Z simple lead paid d x
    (u:=id) («a»:=fun _=>1) tendsto_id (by simpa only [one_mul] using! tendsto_id)
    (Eventually.of_forall (fun _=>⟨one_pos,le_rfl⟩))
  let A:=C₁*‖Further.CorrectedLift.ladder C d‖*(8+G.slopeConstant⁻¹)*C₂
  refine ⟨max 1 A,e+1,le_max_left ..,?_⟩
  filter_upwards [home 1 one_pos,(ge_mem_nhds ((C).S.a_pos gate)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin,(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r size small rp unit
  intro D k s B stock cap W hk U seats checked live due j reaches
  change 0<r at rp
  have wr:a W.k≤r:=(WilsonReflectedPublicBulbBerth.mesh R W checked).trans live.le
  have tiny:gate≤W.k:=by
    by_contra! earlier
    exact (not_le_of_gt ((C).S.strictAnti earlier)) (wr.trans small)
  have βp:0≤β j:=zero_le_one.trans ((P).fits.delayed j).le
  have advance:=WilsonStartup.Timing.hat_mono (P) (Gauge.slopeConstant_pos simple).le
  have press:preExpense C d W.k W.b≤C₁*(β j)^e:=(late _ tiny _ checked.high.2).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans ((P).fits.delayed W.k).le) (advance reaches) _) (zero_le_one.trans one))
  let v:=homogeneous F J Z r d x
  have own:cost F d r v≤C₂:=by simpa only [id_eq,one_mul,Real.one_rpow,mul_one] using size
  have inward: ‖U.symm v‖≤(8+G.slopeConstant⁻¹)*(β j)*C₂:=(due v).trans
    (mul_le_mul (clock (R:=R) simple (((C).S.strictAnti.antitone reaches).trans wr)) own (cost_pos F ..)
      ((zero_le_one.trans (dock_valid r ⟨rp,unit⟩)).trans (clock (R:=R) simple (((C).S.strictAnti.antitone reaches).trans wr))))
  let ladder:=Further.CorrectedLift.ladder C d
  have restore:= (ladder.le_opNorm (U.symm v)).trans (mul_le_mul_of_nonneg_left inward (norm_nonneg ladder))
  change preExpense C d W.k W.b*‖ladder (U.symm v)‖≤_
  calc
    _≤(C₁*(β j)^e)*(‖ladder‖*((8+G.slopeConstant⁻¹)*(β j)*C₂)):=mul_le_mul press restore (norm_nonneg _) (mul_nonneg (zero_le_one.trans one) (pow_nonneg βp _))
    _=A*(β j)^(e+1):=by dsimp [A,ladder];rw [pow_succ];ring
    _≤_:=mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg βp _)

end YM.Integration.WilsonMovingForkWeakPrice
end
