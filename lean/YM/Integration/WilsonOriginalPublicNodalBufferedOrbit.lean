import YM.Integration.WilsonIndependentSpoutMasterOrbit
import YM.Integration.WilsonOriginalPublicNodalBufferedReport

/-! The original variable physical book reads the fully compensated finite source at its own old vector. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalBufferedOrbit
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


open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentPublicReportComplex (apply row)
open WilsonOriginalPublicNodalBufferedReport (read tariff)
open WilsonIndependentMatchedBufferedVacuum (stopped)

def film (v:J)(b:Herit Q):PowerSeries ℂ:=
  let c:=vector R d D cut b (home v) (m v+j v)
  ∑z:WilsonIndependentSpoutPhysicalHomes.Visits R d D φ x₀ y loc v,
    complex (load R d D cut φ x₀ y loc v c unit z)*filmAt R W mode d D φ x₀ y loc sample v z

def toll (tail:J→ℝ)(q r:ℕ)(H₀:ℝ)(v:J)(b:Herit Q)(cap:Fin (n+1)→ℝ):ℝ:=
  let c:=vector R d D cut b (home v) (m v+j v)
  (∏i,WilsonIndependentMatchedOpeningMenu.charge R (cut i) q (d i) (c i) (φ v i) (x₀ v i) (y v) (cap i))*
    (H₀*(amount R V m j w ip H v)^r*tail v)

def fresh (s:Choice j)(v:J)(b:Herit Q):Era G ℝ:=
  stopped P R.metals.O Q (φ v) b (home v) (m v+j v) (m v+j v) (station j m s v) (y v) (o v)

variable (simple:G.Simple)(side:∀v,TopF (WilsonPositionProgramInfraredCircuit.count V j w) v=(sample v).F.p.side)
    (pre:∀v,home v ≤ m v+j v)
    (homes:∀v:J,1+∑i:Fin (n+1),(dist (ρ v) ((y v/paceT R.family.path.levels.S (home v) (m v+j v)) • (o v).val)+
      ((φ v i).radius+paceT R.family.path.levels.S (home v) (m v+j v))/paceT R.family.path.levels.S (home v) (m v+j v)) ≤ amount R V m j w ip H v)
    (clear:0<c₀)(safe:((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
      (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)).cushion c₀ ρ)
include issued simple side pre homes clear safe
theorem original (q:ℕ)(hq:q ≤ p)(s:Choice j):
    ∃r:ℕ→ℕ,∃H₀:ℕ→ℝ,(∀i,0 ≤ H₀ i) ∧
    ∀(v:J)(b:Herit Q)(cap:Fin (n+1)→ℝ),(∀i,Amplitude (φ v i) (cap i)) →
    station j m s v ≤ home v →
    let K:=m v+j v
    let date:=station j m s v
    let common:=relativeC P R.metals.O K date (K-date)
    ∀(old:Era G ℝ)(fee:ℝ),(∀i ≤ q,‖PowerSeries.coeff i (ground old)-
      PowerSeries.coeff i (ground (fresh R m j d D cut home φ y o s v b))‖ ≤ fee) →
    ∀(clock:Feeds)(pole:ℕ),
    ‖PowerSeries.coeff q (apply clock pole (film R W m j d D cut home φ y o sample v b))-
      read clock pole q common (ground old)‖ ≤
      (∑i∈Finset.range (q+1),‖row clock pole q i‖*
        toll R V m j w d D cut home φ y ip H (fun z=>(sky).modifyErr 0 1 (1/2) s z)
          i (r i) (H₀ i) v b cap)+tariff clock pole q common*fee:=by
  choose r H₀ pos licensed using fun i:ℕ=>WilsonIndependentSpoutMasterOrbit.stopped R W V m j w blocks
    Z issued d D cut home φ y o sample ρ ip H c₀ simple side pre homes clear safe
    (min i q) ((min_le_right _ _).trans hq) s
  refine ⟨r,H₀,pos,?_⟩
  intro v b cap hcap hv
  dsimp only
  intro old fee atSource clock pole
  let K:=m v+j v
  let date:=station j m s v
  let common:=relativeC P R.metals.O K date (K-date)
  let kept:=fresh R m j d D cut home φ y o s v b
  let paper:=film R W m j d D cut home φ y o sample v b
  have orbit (i:ℕ)(hi:i ≤ q):‖PowerSeries.coeff i paper-
      PowerSeries.coeff i (complex (reel common (ground kept)))‖ ≤
      toll R V m j w d D cut home φ y ip H (fun z=>(sky).modifyErr 0 1 (1/2) s z) i (r i) (H₀ i) v b cap:=by
    have earn:=licensed i v b cap hcap hv
    rw [min_eq_left hi] at earn
    exact earn
  have bound: ‖PowerSeries.coeff q (apply clock pole paper)-read clock pole q common (ground kept)‖ ≤
      ∑i∈Finset.range (q+1),‖row clock pole q i‖*
        toll R V m j w d D cut home φ y ip H (fun z=>(sky).modifyErr 0 1 (1/2) s z) i (r i) (H₀ i) v b cap:=by
    change ‖PowerSeries.coeff q (apply clock pole paper)-
      PowerSeries.coeff q (apply clock pole (complex (reel common (ground kept))))‖ ≤ _
    rw [WilsonIndependentPublicReportComplex.difference]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi=>?_ )
    rw [norm_mul,Complex.norm_real,mul_comm]
    exact mul_le_mul_of_nonneg_left (orbit i (by have:=Finset.mem_range.mp hi;omega)) (norm_nonneg _)
  have compare:=WilsonOriginalPublicNodalBufferedReport.bought clock pole q common (ground old) (ground kept) fee atSource
  rw [norm_sub_rev] at compare
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add bound compare)

end YM.Integration.WilsonOriginalPublicNodalBufferedOrbit
