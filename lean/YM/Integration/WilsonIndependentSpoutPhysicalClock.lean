import YM.Integration.WilsonIndependentSpoutPhysicalOrbit
import YM.Integration.WilsonIndependentSpoutRosterCashier

/-! Read the common measured scalar, with every constant and its proper age, on an arbitrary licensed stop. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPhysicalClock
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Cluster RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ledger.Sky
open RegulatorIR.Ledger RegulatorIR.Binding RegulatorIR.Oracle RegulatorIR.Uniform
open WilsonIndependentRawRosterWord (degree)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentSpoutFundedClocks (clock age)
open WilsonIndependentSpoutScalarLedger (scalar)
open WilsonIndependentSpoutPhysicalOrbit (returned)
open WilsonIndependentSpoutRosterCashier (complex)
open WilsonIndependentMatchedOpeningPayment (affiled)
open scoped Classical BigOperators
variable {G:Gauge}{T I X:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(m j:X → ℕ)
    (d:I → ℕ){E:I → ℕ}(cut:∀i,d i<E i)(arms:Composite I)

def station (j m:X → ℕ)(s:Choice j)(v:X):ℕ:=m v+(j v-s.age v)

theorem original (σ:I → Bool)(key:∀i,(R.family.labels.level (d i)).Index)(sites:X → I → Cover)(stop:Choice j)(v:X):
    returned R W m j σ d key cut arms sites stop v=complex
      (WilsonIndependentSpoutDoseBoundary.measure R.family.path.levels R.metals.O (m v+j v)
        (arms.accounts (degree R d key)) (m v+j v) (station j m stop v) (field R W σ d key cut (sites v) arms)):=by
  let A:=fun _:X=>R.family.path.levels
  let Y:=cruises (A v) R.metals.O (m v+j v) (arms.accounts (degree R d key)) (m v+j v)
    (station j m stop v) (field R W σ d key cut (sites v) arms)
  have h:=WilsonIndependentSpoutScalarLedger.reported A R.metals.O m (stop.choose v) Y
  have cal:clock A R.metals.O m (stop.choose v)=relativeC (A v) R.metals.O (m v+j v) (station j m stop v)
      ((m v+j v)-station j m stop v):=by
    have lim : stop.age v ≤ j v := stop.young v
    unfold clock age Choice.choose station
    dsimp
    congr 1
    omega
  rw [cal] at h
  ext q
  rw [complex,PowerSeries.coeff_map]
  change ((PowerSeries.coeff (R:=ℝ) q (scalar (WilsonIndependentSpoutOriginalMarkedJourney.source A m R.metals.O (stop.choose v) Y))):ℂ)=_
  rw [h]
  rfl

theorem book (simple:G.Simple)(v:X)(stop:Choice j){T:Type}[Fintype T]
    (σ:T → I → Bool)(key:T → (i:I) → (R.family.labels.level (d i)).Index)(o:T → I → Cover)
    (ω:T → Blue.Cost)(k:ℕ)(cap:∀i,arms.accounts (degree R d (key i)) ≤ k)(full:Era G ℝ)
    (filed:full=∑i,affiled (ω i) (field R W (σ i) d (key i) cut (o i) arms)):
    ∑i,complex (ω i)*returned R W m j (σ i) d (key i) cut arms (fun _=>o i) stop v=
    complex (WilsonIndependentSpoutDoseBoundary.measure R.family.path.levels R.metals.O (m v+j v) k (m v+j v)
      (station j m stop v) full):=by
  let U (i:T):=field R W (σ i) d (key i) cut (o i) arms
  let rawGrade (i:T):=arms.accounts (degree R d (key i))
  have paid(i:T):Auth (rawGrade i) (U i):=WilsonIndependentMatchedOpeningRoster.enrolled R W
    (σ i) d (key i) cut (o i) arms
  have before:station j m stop v ≤ m v+j v:=by unfold station;omega
  have closed:=WilsonIndependentSpoutFiledDoseReturn.original R.family.path.levels R.metals.O simple (RunFormalChain.fromRun R).receipt
    (m v+j v) k _ (station j m stop v) before le_rfl rawGrade cap full (fun i=>affiled (ω i) (U i)) U ω filed
    (fun i=>WilsonIndependentMatchedOpeningFee.grant (U i) (paid i) (ω i)) paid (fun _ _=>rfl)
  simp_rw [WilsonIndependentSpoutFiledDoseReturn.opening] at closed
  rw [closed,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,original]

end YM.Integration.WilsonIndependentSpoutPhysicalClock
