import YM.Integration.WilsonIndependentSpoutMasterOrbitClock
import YM.Integration.WilsonIndependentSpoutMasterWordWage

/-! The measured genuine inversion-board return of the actual normalized roster, including its full finite fitted source fare. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonIndependentSpoutMasterEnrolledOrbit
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
open WilsonIndependentSpoutMasterOrbitClock (measure)
open WilsonIndependentSpoutMasterObserved (observed)
open WilsonIndependentSpoutMasterWordWage (wages)
open WilsonIndependentMatchedOpeningMenu (charge)
open WilsonIndependentSpoutMasterOrbit (Salary)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic Filter Finset
open WilsonCoeffUV.Mer.Patrol Source.Drops RG.Supply
open scoped BigOperators Classical ENNReal NNReal Topology
open WilsonIndependentSpoutPhysicalHomes (Labels pointsAt extent filmAt load profile)
open WilsonIndependentSpoutNormalizedMaster (vector)
open WilsonIndependentSpoutDoseBoundary (into)
open WilsonIndependentSpoutPhysicalClock (station)
open WilsonIndependentSpoutPhysicalOrbit (amount)
variable {G:Gauge}{J:Type}{n k f e q j₀:ℕ}
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


def raw (v:J)(b:Herit Q):PowerSeries ℂ:=
  ∑z:WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v,
    complex (load R d D cut φ x₀ y loc v (vector R d D cut b (home v) (m v+j v)) unit z)*
      filmAt R W mode d D φ x₀ y loc sample v z

def debit (q:ℕ)(v:J)(b:Herit Q)(M:Fin (n+1)→ℝ):ℝ:=
  ∏i,charge R (cut i) q (d i) (vector R d D cut b (home v) (m v+j v) i) (φ v i) (x₀ v i) (y v) (M i)

def total (q:ℕ)(r:Fin (q+1)→ℕ)(H₀:Fin (q+1)→ℝ)(v:J)(b:Herit Q)(M:Fin (n+1)→ℝ):ℝ:=
  ∑s:Fin (q+1),|debit R m j d D cut home φ y s.val v b M| *(H₀ s*amount R V m j w ip H v ^ (r s))

def Returned (q j₀:ℕ)(T:Credit)(r:Fin (q+1)→ℕ)(H₀:Fin (q+1)→ℝ)(stop:Choice j)(tail:J→ℝ):Prop:=
  ∀(v:J)(b:Herit Q)(M:Fin (n+1)→ℝ),j₀ ≤ home v → (∀i,Amplitude (φ v i) (M i)) →
    station j m stop v ≤ home v → ∀g:ℝ,|g|≤1 →
    let K:=m v+j v
    let recv:=stopped P R.metals.O Q (φ v) b (home v) K K (station j m stop v) (y v) (o v)
    ‖cash q g (measure (relativeF P R.metals.O K (home v) (K-home v)) (raw R W m j d D cut home φ y o sample v b))-
      observed P R.metals.O K (home v) (station j m stop v) q g recv‖ ≤
      (q+1:ℝ)*((q+1:ℝ)*((total R V m j w d D cut home φ y ip H q r H₀ v b M*tail v)*
        T.buy (Compar (P).S (zz P) (home v) K)))

variable (simple:G.Simple)(side:∀v,TopF (WilsonPositionProgramInfraredCircuit.count V j w) v=(sample v).F.p.side)
    (pre:∀v,home v ≤ m v+j v)
    (homes:∀v:J,1+∑i:Fin (n+1),(dist (ρ v) ((y v/paceT R.family.path.levels.S (home v) (m v+j v)) • (o v).val)+
      ((φ v i).radius+paceT R.family.path.levels.S (home v) (m v+j v))/paceT R.family.path.levels.S (home v) (m v+j v)) ≤ amount R V m j w ip H v)
    (clear:0<c₀)(safe:((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
      (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)).cushion c₀ ρ)

variable {T:Credit}(clock:WilsonIndependentSpoutMasterBareClocks.Paid R j₀ e T)
include simple pre clock in
theorem returned (hq:q ≤ e)(stop:Choice j)(tail:J→ℝ)(nn:∀v,0≤tail v)
    (r:Fin (q+1)→ℕ)(H₀:Fin (q+1)→ℝ)(hn:∀s,0≤H₀ s)
    (sale:∀s,Salary R W V m j w d D cut home φ y o sample ip H s.val stop tail (r s) (H₀ s)):
    Returned R W V m j w d D cut home φ y o sample ip H q j₀ T r H₀ stop tail:=by
  intro v b M beginAt funded older g small
  let K:=m v+j v
  let dst:=station j m stop v
  let Y:=stopped P R.metals.O Q (φ v) b (home v) K K dst (y v) (o v)
  let bill:=total R V m j w d D cut home φ y ip H q r H₀ v b M*tail v
  have size:0≤amount R V m j w ip H v:=zero_le_one.trans (WilsonPositionProgramInfraredMeter.lower R V m j w ip H v)
  refine WilsonIndependentSpoutMasterOrbitClock.posted R simple K (home v) dst q older (pre v) g bill
    (T.buy (Compar (P).S (zz P) (home v) K)) (raw R W m j d D cut home φ y o sample v b) Y small ?_ ?_
  · intro z zq
    let s:Fin (q+1):=⟨z,by omega⟩
    let a:=amount R V m j w ip H v
    let c (s:Fin (q+1)):=debit R m j d D cut home φ y s.val v b M
    have paid:=sale s v b M funded older
    apply paid.trans
    change c s*(H₀ s*a^(r s)*tail v) ≤ _
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (nn v)
    exact (mul_le_mul_of_nonneg_right (le_abs_self (c s)) (mul_nonneg (hn s) (pow_nonneg size _))).trans
      (single_le_sum (f:=fun t:Fin (q+1)=>|c t| *(H₀ t*a^r t))
        (fun t _=>mul_nonneg (abs_nonneg _) (mul_nonneg (hn t) (pow_nonneg size _))) (mem_univ s))
  · intro i iq a aq
    exact clock (home v) K i a beginAt (pre v) (iq.trans hq) (aq.trans hq)

include issued simple side pre homes clear safe in
theorem original {h window k u e:ℕ}(registry:ℕ→Gear G→ℝ)(budget:FundedMarkedCoverRows.prices registry R.kit)
    (seat:h<window)(rails:Rails h k u e)(capacity:capP Q ≤ k):
    ∃(A B:Fin (n+1)→Credit)(T:Credit),∀ᶠ j₀:ℕ in atTop,
    (∀m K,j₀ ≤ m → m ≤ K → ∀(b:Herit Q)(cap:Fin (n+1)→ℝ),(∀i,fee b e i ≤ cap i) →
      ∀(φ:∀i,Rarity (D i))(x:Fin (n+1)→ℝ)(y:ℝ)(M:Fin (n+1)→ℝ)(t:ℕ),t ≤ e →
      ∀i,charge R (cut i) t (d i) (vector R d D cut b m K i) (φ i) (x i) y (M i) ≤
        wages R d D cut A B m K t cap φ x y M i) ∧ ∀(q:ℕ),q ≤ p → q ≤ e →
    ∃(r:Fin (q+1)→ℕ)(H₀:Fin (q+1)→ℝ),(∀s,0≤H₀ s) ∧
      Returned R W V m j w d D cut home φ y o sample ip H q j₀ T r H₀ (WilsonIndependentRawPeriodPower.terminal j)
        (fun v=>(sky).P v ^ (-(1/4:ℝ))):=by
  obtain ⟨A,B,words⟩:=WilsonIndependentSpoutMasterWordWage.original R d D cut simple registry budget seat rails capacity
  obtain ⟨T,clock⟩:=WilsonIndependentSpoutMasterBareClocks.original R simple registry budget seat rails d D cut capacity
  refine ⟨A,B,T,?_⟩
  filter_upwards [words,clock] with j₀ next meters
  refine ⟨next,?_⟩
  intro q qp qe
  choose r H₀ hn paid using fun s:Fin (q+1)=>WilsonIndependentSpoutMasterOrbit.terminal R W V m j w blocks Z issued
    d D cut home φ y o sample ρ ip H c₀ simple side pre homes clear safe s.val ((Nat.le_of_lt_succ s.isLt).trans qp)
  refine ⟨r,H₀,hn,returned R W V m j w d D cut home φ y o sample ip H simple pre meters qe _ _ ?_ r H₀ hn paid⟩
  intro v
  exact Real.rpow_nonneg ((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).synchronize v).le _

end YM.Integration.WilsonIndependentSpoutMasterEnrolledOrbit
end
