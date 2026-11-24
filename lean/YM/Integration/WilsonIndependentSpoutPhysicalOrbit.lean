import YM.Integration.WilsonOriginalPublicNodalPhysicalMerBook
import YM.Integration.WilsonOriginalPublicNodalEnrolledMerStop
import YM.Integration.WilsonIndependentSpoutScalarLedger
import YM.Integration.WilsonIndependentRawRosterOrbit

/-! The very same funded, variable-block physical circuit returns the bare normalized word and the full Mer scalar. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonIndependentSpoutPhysicalOrbit
open Lattice RG Tree Wilson Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick
open RegulatorIR.Atlas RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Epoch RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Momentum RegulatorIR.Ledger.Sky
open RegulatorIR.Profiles RegulatorIR.Budget.Packet RegulatorIR.Cluster RegulatorIR.Binding
open RegulatorIR.Clocks
open WilsonIndependentRawRosterWord WilsonIndependentRawWordGeometry
open WilsonOriginalPublicNodalPhysicalMerBook (Issued)
open WilsonOriginalPublicNodalEnrolledMerStop (aged series)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{X I:Type}(R:Run G)(W:Initialize G)(V:XSpace.Run)
    (m j:X→ℕ)(w:X→ℕ→ℕ)(blocks:∀x k,(R.family.S.block (m x+k)).val=V.ratio^(w x k))
    (Z:∀p:Patch,p.Branches R.family.path.levels.clock.kernel G){p:ℕ}{F:Tent j}(issued:Issued R V m j w blocks Z p F)
variable (σ:I→Bool)(d:I→ℕ)(key:∀i,(R.family.labels.level (d i)).Index){E:I→ℕ}(cut:∀i,d i<E i)
    (arms:Composite I)(sites:X→I → Cover)(sample:X→Sample 2)(x:X→Room)(ip:X→ℕ)(H c₀:ℝ)
local notation "C" => WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel
local notation "num" => WilsonPositionProgramInfraredCircuit.count V j w
local notation "S" => (C).dialect Y G Z (sheet F)
local notation "L" => WilsonPositionProgramInfraredMeter.wallet R V m j w ip H
local notation "A" => (fun _:X=>R.family.path.levels)
def returned (stop:Choice j)(v:X):PowerSeries ℂ:=
  series (aged R W A m R.metals.O σ d key cut arms sites stop v)
def raw (v:X):PowerSeries ℂ:=Bare.normalized (W.tree (sample v).F.p) G (film R W σ d key (sample v) (sites v) arms)
def amount (v:X):ℝ:=WilsonPositionProgramInfraredMeter.amount R V m j w ip H v
variable (simple:G.Simple)(same:∀x,TopF (WilsonPositionProgramInfraredCircuit.count V j w) x=(sample x).F.p.side)
    (fare:∀v,1+WilsonIndependentRawRosterBudget.span (x v) (sites v) arms ≤ amount R V m j w ip H v)
    (clear:0<c₀)(safe:((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)).cushion c₀ x)
include simple issued same fare clear safe
theorem stopped (q:ℕ)(hq:q≤p)(stop:Choice j):
    ∃H₀:ℝ,∃k:ℕ,0≤H₀ ∧ ∀v:X,
      ‖PowerSeries.coeff q (raw R W σ d key arms sites sample v)-PowerSeries.coeff q
        (returned R W m j σ d key cut arms sites stop v)‖ ≤
        H₀*(amount R V m j w ip H v)^k*(S).modifyErr 0 1 (1/2) stop v:=by
  obtain ⟨cash,lamp,ending⟩:=issued.funded ip H
  obtain ⟨unit,_⟩:=WilsonPositionProgramInfraredCircuit.units R V m j w blocks
  have debt (v:X):ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x v) (sites v) arms)≤(L).val v:=
    ENNReal.ofReal_le_ofReal (fare v)
  obtain ⟨C₀,k,nn,price⟩:=WilsonIndependentRawRosterOrbit.stopped R W σ d key arms sites cash lamp ending sample x
    unit issued.flat same debt clear safe q hq stop (fun _=>Nat.zero_le _)
  refine ⟨C₀,k,nn,?_⟩
  intro v
  have hit:=WilsonOriginalPublicNodalEnrolledMerStop.original R W C Y Z F A m R.metals.O σ d key cut arms sites
    simple (RunFormalChain.fromRun R).receipt p issued.marked stop v
  have weight:((L).val v).toReal = amount R V m j w ip H v:=ENNReal.toReal_ofReal
    ((zero_le_one.trans (WilsonPositionProgramInfraredMeter.lower R V m j w ip H v)))
  simpa only [raw,returned,series,PowerSeries.coeff_mk,←hit q hq,weight] using price v

theorem terminal (q:ℕ)(hq:q≤p):
    ∃H₀:ℝ,∃k:ℕ,0≤H₀ ∧ ∀v:X,
      ‖PowerSeries.coeff q (raw R W σ d key arms sites sample v)-PowerSeries.coeff q
        (returned R W m j σ d key cut arms sites (WilsonIndependentRawPeriodPower.terminal j) v)‖ ≤
        H₀*(amount R V m j w ip H v)^k*(S).P v ^ (-(1/4:ℝ)):=by
  let s:=WilsonIndependentRawPeriodPower.terminal j
  obtain ⟨C₀,k,nn,price⟩:=stopped R W V m j w blocks Z issued σ d key cut arms sites sample x ip H c₀
    simple same fare clear safe q hq s
  obtain ⟨cash,lamp,_⟩:=issued.funded ip H
  obtain ⟨unit,last,bounded⟩:=WilsonPositionProgramInfraredCircuit.units R V m j w blocks
  let gain:=2+(last:ℝ)^(1/2:ℝ)
  have pos:0≤gain:=by unfold gain;positivity
  refine ⟨C₀*gain,k,mul_nonneg nn pos,?_⟩
  intro v
  have bill:=WilsonIndependentRawPeriodPower.cost ((C).lane Y G Z (sheet F)) (1/2:ℝ) lamp.gleams (by norm_num)
    1 last cash.positive unit bounded v
  norm_num only [show -((1/2:ℝ)/2)=-(1/4:ℝ) by norm_num] at bill
  have base:0≤amount R V m j w ip H v:=zero_le_one.trans (WilsonPositionProgramInfraredMeter.lower R V m j w ip H v)
  exact (price v).trans ((mul_le_mul_of_nonneg_left bill (mul_nonneg nn (pow_nonneg base k))).trans_eq (by unfold gain;ring))

end YM.Integration.WilsonIndependentSpoutPhysicalOrbit
