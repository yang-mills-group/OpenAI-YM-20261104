import YM.Integration.WilsonThermometerAncestralTrace
import YM.Integration.WilsonThermometerRegisteredTripleRoom
import YM.Integration.WilsonCapturedPrimaryTrailSites

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralHomes
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

open OPE.Therm Pert.Asymptotics WilsonReceivedFirstTrace WilsonPositionThermometerGradedSource WilsonThermometerCourseHearing

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m t N per k:ℕ}
  (top:t<N) (o:Positions (Fin 3) (R.family.side N per))
local notation "faces" itr:max => WilsonThermometerCourseHearing.offered R A simple itr o
local notation "arr" j:max jt:max => WilsonReceivedCloseHistory.history (N:=N) R WilsonThermometerCourseHearing.disks (faces top) j jt
variable (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls tab φ) (ahead:Mentor.Forecast D R.rolls tab φ books)
  (order shelf seats:ℕ)
local notation "ages" => (fun v:Fin 3=>(grade v).val)
local notation "post" j:max mj:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books
  ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j mj y
variable (W:Registration (m:=m) (N:=N) (k:=k) R D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks shelf seats)
  (mt:m≤t)
open WilsonThermometerAncestralTrace

open RG12 XSpace WilsonThermometerAlignedCells
local notation "sheet" j:max => R.family.path.levels.clock.op j per
local notation "homes" j:max L:max => ((L).passport.coarser (sheet j).ratio).origin
local notation "config" j:max => Config G (R.family.side j per)
local notation "room" j:max => halo ((Ψ j).p.B) ({0}:Support (R.family.side j per))

private theorem address {j:ℕ} {mj:m ≤ j} {a b:Wallet WilsonThermometerCourseHearing.disks →
     config (j+1) → Poly (Stock.census (Fin 3))} (P:post j mj a) (L:post j mj b)
     (same:a=b) (held:HEq P L) : homes j P = homes j L :=by
  subst b
  rw [eq_of_heq held]

/-- The incoming origin certificate is inherited on a genuine earlier counted archive. -/
theorem inherited {b:ℕ} (mb:m ≤ b) (cap:b<N)
    (before:Wallet WilsonThermometerCourseHearing.disks → config (b+1) → Poly (Stock.census (Fin 3)))
    (first:post b mb before) (c₀:Countable first.inputIndex) (q₀:ℕ) (ε:ℝ)
    (seated:∀v,first.passport.origin v=(R.family.S.toDepth cap per).parent (o.origin v))
    (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex)
    (archive:Chain R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
      WilsonThermometerCourseHearing.sectors ages order shelf seats W mb before first c₀ cap q₀ ε
      t mt top (faces top) inlet counted) :
    ∀v,inlet.passport.origin v=(R.family.S.toDepth top per).parent (o.origin v) :=by
  obtain ⟨tb,home⟩:=WilsonCapturedPrimaryTrailSites.original R hk D tab π Γ Ψ books ahead
    WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats
    mb before (install R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
      WilsonThermometerCourseHearing.sectors ages order shelf seats W first c₀ cap)
    (Chain.trail R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
      WilsonThermometerCourseHearing.sectors ages order shelf seats W mb before first c₀ cap q₀ ε archive)
  intro v
  have addressAt:inlet.passport.origin v=(R.family.S.toDepth (Nat.succ_le_succ tb) per).parent
    (first.passport.origin v) :=home v
  rw [addressAt,seated v]
  exact (Next.Rank.Station.parent_nested _ _ _ (R.family.S.toDepth_odd (Nat.succ_le_succ tb) per)
    (R.family.S.toDepth_odd cap per) _).symm

theorem placed (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (birth:∀v,inlet.passport.origin v=(R.family.S.toDepth top per).parent (o.origin v))
    {i:ℕ} (mi:m ≤ i) (it:i ≤ t) (L:post i mi (faces (it.trans_lt top)))
    (found:Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt
      inlet counted (q+2) 1 mi it L) : ∀v,(homes i L) v=(R.family.S.toDepth (it.trans top.le) per).parent (o.origin v) :=by
  obtain ⟨P,c,trail,hP,_,_⟩:=found
  have sites:=address R hk D tab π Γ Ψ books ahead order shelf seats P L
    (WilsonThermometerAncestralTrace.same R simple A top o refs it) (HEq.symm hP)
  intro v
  have location:=WilsonCapturedPrimaryTrailSites.outgoing R hk D tab π Γ Ψ books ahead
    WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats mt
    (faces top) (install R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
      WilsonThermometerCourseHearing.sectors ages order shelf seats W inlet counted top) it
    (Chain.trail R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors
      ages order shelf seats W mt (faces top) inlet counted top (q+2) 1 trail) v
  change (homes i P) v=(R.family.S.toDepth (it.trans (Nat.le_succ t)) per).parent (inlet.passport.origin v) at location
  rw [←sites,location,birth v]
  exact (Next.Rank.Station.parent_nested _ _ _ (R.family.S.toDepth_odd (it.trans (Nat.le_succ t)) per)
    (R.family.S.toDepth_odd top per) _).symm

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (birth:∀v,inlet.passport.origin v=(R.family.S.toDepth top per).parent (o.origin v))
    {i:ℕ} (mi:m ≤ i) (it:i ≤ t) (L:post i mi (faces (it.trans_lt top)))
    (found:Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt
      inlet counted (q+2) 1 mi it L) (profile:Test 3) (r:ℝ)
    (station:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose ≤ i)
    (spaced:|r| ≤ R.family.S.a i) (y:Site (R.family.side N per) × Site (R.family.side N per))
    (positions:o.origin=atOrigin y) (present:mass (R:=R) r (N,per) profile y≠0) :
    (0:Site (R.family.side i per)) ∈ room i ∧ (∀v:Fin 3,(homes i L) v∈room i) ∧
      ∀v:Fin 3,separation ((homes i L) v) 0 ≤ (Ψ i).p.B :=by
  have whereAt:=placed R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt
    inlet counted q refs birth mi it L found
  have point:=(W.course.1.walk i mi (it.trans top.le)).truep.point
  have sites:= (eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose_spec i
    station N per (it.trans top.le) r spaced y present
  have tariff(v:Fin 3):separation ((homes i L) v) 0 ≤ (Ψ i).p.B :=by
    rw [whereAt v,positions,point];exact sites v
  refine ⟨halo_spec.mpr ⟨0,Finset.mem_singleton_self _,by simp⟩,?_,tariff⟩
  intro v
  exact halo_spec.mpr ⟨0,Finset.mem_singleton_self _,by simpa only [separation_comm] using tariff v⟩

end YM.Integration.WilsonThermometerAncestralHomes
