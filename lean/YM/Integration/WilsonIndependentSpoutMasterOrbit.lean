import YM.Integration.WilsonIndependentSpoutNormalizedMaster

/-! The genuine normalized public master on its bare top and the independent Wilson board. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonIndependentSpoutMasterOrbit
open Lattice Wilson Tree RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision Exterior Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.StableStrip WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket
open PhysicalNext PhysicalNext.Repeat Next.Foundations
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentRawRosterWord
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedOpeningHomes (rent name site pitch)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutRosterCashier (complex)
open scoped BigOperators Classical ENNReal NNReal
open WilsonIndependentSpoutPhysicalHomes (Labels pointsAt extent filmAt load profile)
open WilsonIndependentSpoutNormalizedMaster (vector)
open WilsonIndependentSpoutDoseBoundary (into)
open WilsonIndependentSpoutPhysicalClock (station)
open WilsonIndependentSpoutPhysicalOrbit (amount)
variable {G:Gauge}{J:Type}{n:ℕ}
local notation "C" => Credit.leanC
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(V:XSpace.Run)
    (m j:J → ℕ)(w:J → ℕ → ℕ)(blocks:∀v l,(R.family.S.block (m v+l)).val=V.ratio^(w v l))
    (Z:∀p:Patch,p.Branches R.family.path.levels.clock.kernel G){p:ℕ}{F:Tent j}
    (issued:WilsonOriginalPublicNodalPhysicalMerBook.Issued R V m j w blocks Z p F)
local notation "sky" => (WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
    (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)

variable (d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
    (home:J → ℕ)(φ:J → (i:Fin (n+1)) → Rarity (D i))(y:J→ℝ)(o:J → CellR)
    (sample:J → Sample 2)(ρ:J→Room)(ip:J→ℕ)(H c₀:ℝ)
local notation "P" => R.family.path.levels
local notation "Q" => (deck (G:=G) d D cut)
local notation "loc" => (fun v:J=>fun _:Fin (n+1)=>o v)
local notation "x₀" => (fun v:J=>fun _:Fin (n+1)=>paceT (P).S (home v) (m v+j v))
local notation "mode" => (fun _:Fin (n+1)=>false)
local notation "unit" => (fun _:Fin (n+1)=>(1:ℝ))

def Salary (q:ℕ)(stop:Choice j)(tail:J→ℝ)(r:ℕ)(H₀:ℝ):Prop:=
  ∀(v:J)(b:Herit Q)(cap:Fin (n+1)→ℝ), (∀i,Amplitude (φ v i) (cap i)) →
    station j m stop v ≤ home v →
    let K:=m v+j v
    let c:=vector R d D cut b (home v) K
    ‖PowerSeries.coeff q (∑z:WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v,
      complex (load R d D cut φ x₀ y loc v c unit z)*filmAt R W mode d D φ x₀ y loc sample v z)-
      PowerSeries.coeff q (complex (into P R.metals.O K (station j m stop v)
        (WilsonIndependentSpoutScalarLedger.ground (WilsonIndependentMatchedBufferedVacuum.stopped P R.metals.O Q
          (φ v) b (home v) K K (station j m stop v) (y v) (o v)))))‖ ≤
      (∏i,WilsonIndependentMatchedOpeningMenu.charge R (cut i) q (d i) (c i) (φ v i) (x₀ v i) (y v) (cap i)) *
        (H₀*(amount R V m j w ip H v)^r*tail v)

private theorem collect (simple:G.Simple)(pre:∀v,home v ≤ m v+j v)(q:ℕ)(stop:Choice j)(tail:J → ℝ)(nn:∀v,0≤tail v)
    (r:ℕ)(H₀:ℝ)(hn:0≤H₀)(paid:WilsonIndependentSpoutPhysicalVisits.price R W V m j w (fun _:Labels R d=>mode)
      d (fun l=>l) cut (branch n id) (pointsAt R d D φ x₀ y loc ρ) sample ip H q stop tail r H₀):
    Salary R W V m j w d D cut home φ y o sample ip H q stop tail r H₀:=by
  intro v b budget funded early
  let K:=m v+j v
  let c:=vector R d D cut b (home v) K
  let Visits:=WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v
  let label (z:Visits):Labels R d:=name R d D (φ v) (x₀ v) (y v) (loc v) z
  have cap (z:Visits):(branch n id).accounts (degree R d (label z)) ≤ ∑i,d i:=by
    rw [WilsonIndependentMatchedOpeningComposite.ranks]
    exact Finset.sum_le_sum fun i _=>valence_cap _ ((z i).2)
  let term:=load R d D cut φ x₀ y loc v c unit
  have booked:=WilsonIndependentSpoutNormalizedMaster.opened R W d D cut b (φ v) (home v) K (y v) (o v)
  dsimp only at booked
  have whole:=WilsonIndependentSpoutPhysicalClock.book R W m j d cut (branch n id) simple v stop
    (fun _:Visits=>mode) label (fun z=>pointsAt R d D φ x₀ y loc ρ v (some z)) term
    (∑i,d i) cap _ booked
  have cost:=paid v Visits some label (fun z=>complex (term z))
  rw [whole] at cost
  have norm(u:ℝ):‖algebraMap ℝ ℂ u‖=‖u‖:=Complex.norm_real u
  simp only [complex,PowerSeries.coeff_map,norm] at cost
  have road:=WilsonIndependentSpoutNormalizedMaster.passage R d D cut b (φ v) (home v) K
    (station j m stop v) early (pre v) (y v) (o v)
  dsimp only [WilsonIndependentSpoutDoseBoundary.measure] at cost
  simp only [show capP Q=(∑i,d i) from rfl,K] at road
  rw [←road] at cost
  apply WilsonIndependentSpoutHomePaidOrbit.settled cost
  · simpa only [one_smul] using profile R d D cut φ x₀ y loc v c unit budget funded
      (fun _=>pace_pos ..) (fun _=>pace_le _ (pre v)) q
  · exact mul_nonneg (mul_nonneg hn (pow_nonneg (zero_le_one.trans
      (WilsonPositionProgramInfraredMeter.lower R V m j w ip H v)) r)) (nn v)

variable (simple:G.Simple)(side:∀v,TopF (WilsonPositionProgramInfraredCircuit.count V j w) v=(sample v).F.p.side)
    (pre:∀v,home v ≤ m v+j v)
    (homes:∀v:J,1+∑i:Fin (n+1),(dist (ρ v) ((y v/paceT R.family.path.levels.S (home v) (m v+j v)) • (o v).val)+
      ((φ v i).radius+paceT R.family.path.levels.S (home v) (m v+j v))/paceT R.family.path.levels.S (home v) (m v+j v)) ≤ amount R V m j w ip H v)
    (clear:0<c₀)(safe:((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
      (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)).cushion c₀ ρ)
include issued simple side pre homes clear safe
theorem stopped (q:ℕ)(hq:q ≤ p)(stop:Choice j):
    ∃r:ℕ,∃H₀:ℝ,0≤H₀ ∧ Salary R W V m j w d D cut home φ y o sample ip H
      q stop (fun v=>(sky).modifyErr 0 1 (1/2) stop v) r H₀:=by
  letI (v:J):Nonempty (Option (WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v)):=⟨none⟩
  have inside (v:J)(z:Option (WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v)):1+WilsonIndependentRawRosterBudget.span (ρ v)
    (pointsAt R d D φ x₀ y loc ρ v z) (branch n id) ≤ amount R V m j w ip H v:=
    (add_le_add (le_refl 1) (extent R d D φ x₀ y loc ρ (fun _ _=>pace_pos ..) v z)).trans (homes v)
  obtain ⟨r,H₀,hn,cash⟩:=WilsonIndependentSpoutPhysicalVisits.stopped R W V m j w blocks Z issued
    (fun _:Labels R d=>mode) d (fun l=>l) cut (branch n id) (pointsAt R d D φ x₀ y loc ρ) sample
    (fun v _=>ρ v) ip H c₀ simple side inside clear (fun _=>safe) q hq stop
  refine ⟨r,H₀,hn,collect R W V m j w d D cut home φ y o sample ρ ip H simple pre q stop _ ?_ r H₀ hn cash⟩
  intro v
  apply add_nonneg ((sky).transfer_pos v).le
  exact inv_nonneg.mpr (Real.rpow_nonneg ((sky).hl _).le _)

theorem terminal (q:ℕ)(hq:q ≤ p):
    ∃r:ℕ,∃H₀:ℝ,0≤H₀ ∧ Salary R W V m j w d D cut home φ y o sample ip H
      q (WilsonIndependentRawPeriodPower.terminal j) (fun v=>(sky).P v ^ (-(1/4:ℝ))) r H₀:=by
  letI (v:J):Nonempty (Option (WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v)):=⟨none⟩
  have inside (v:J)(z:Option (WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v)):1+WilsonIndependentRawRosterBudget.span (ρ v)
    (pointsAt R d D φ x₀ y loc ρ v z) (branch n id) ≤ amount R V m j w ip H v:=
    (add_le_add (le_refl 1) (extent R d D φ x₀ y loc ρ (fun _ _=>pace_pos ..) v z)).trans (homes v)
  obtain ⟨r,H₀,hn,cash⟩:=WilsonIndependentSpoutPhysicalVisits.terminal R W V m j w blocks Z issued
    (fun _:Labels R d=>mode) d (fun l=>l) cut (branch n id) (pointsAt R d D φ x₀ y loc ρ) sample
    (fun v _=>ρ v) ip H c₀ simple side inside clear (fun _=>safe) q hq
  refine ⟨r,H₀,hn,collect R W V m j w d D cut home φ y o sample ρ ip H simple pre q (WilsonIndependentRawPeriodPower.terminal j) _ ?_ r H₀ hn cash⟩
  intro v
  exact Real.rpow_nonneg ((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).synchronize v).le _

end YM.Integration.WilsonIndependentSpoutMasterOrbit
