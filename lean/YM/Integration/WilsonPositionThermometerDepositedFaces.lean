import YM.Integration.WilsonPositionThermometerGradedBirth
import YM.Integration.WilsonAllDateHarvestObservables

/-! The optimized bare station pages on independent fine sites, through any
number of original interacting Wilson pushes. Every face uses the same
quiet denominator and carries the full signed product in its numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerDepositedFaces
open Extra.Trajectories FVA1 RG05Readout.Records
open Set Function Filter Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker
open Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open OriginalForcedAddresses Push.GridApprox.Nil ActualRunUnmaskedPartners WilsonPositionThermometerGradedBirth
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) (smooth : G.Simple) (N p : ℕ)
    {I : Type} [DecidableEq I] [Fintype I] {D : ℕ} (V : Vane R.family D)
    (j : I → Fin (D+1)) (v : ∀ i, (Bel R.family.book).Field (j i))
    (o : Positions I (R.family.side N p))
local notation "J₀" => Replicum.Bud I
local notation "C" => R.family

def pages := fun U => essence (ActualRunFullPages.pages R smooth N p N le_rfl o
    (fun i => (j i).val) (payload R N p V j v)) (fun _=>0) (fun _=>1) U

def leg (i:I) := R.family.O N p (V.wheel.atCut (N,p) (j i) (v i)) (o.origin i)

theorem entered (ref : ∀ i, R.family.ref (j i) ≤ N) :
    pages R smooth N p V j v o = birth J₀ (R.family.path.rep N p N) (leg R N p V j v o) := by
  funext U
  exact WilsonPositionThermometerGradedBirth.original R N p V j v smooth ref o U

theorem paid (ref : ∀ i, R.family.ref (j i) ≤ N) {k : ℕ} (upper : k≤N) :
    Integrable (gust R.family.path N p N (pages R smooth N p V j v o) k upper) (prior G _) := by
  rw [entered R smooth N p V j v o ref]
  apply gust_live _ _ _ _ _ _ upper
  have price : Continuous (R.family.path.rep N p N).eval := by rw [(show (R.family.path.rep N p N).eval = _ from (R.makes.wilson.starts N p).2)]; exact bare_cont _
  have earned := hatCont C N p (leg R N p V j v o) (fun i => R.family.continuousO N p (j i) _ (o.origin i)) price J₀
  exact earned.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem deposited (ref : ∀ i, R.family.ref (j i) ≤ N) {k : ℕ} (upper : k≤N)
    (s : (Replicum.Bud I).Mode) (U : Config G (R.family.side k p)) :
    (gust R.family.path N p N (pages R smooth N p V j v o) k upper U).part s =
      (R.family.path.rep N p k).eval U • actualTransport C (N:=N)
        (fun Y => ∏ i∈s.val,R.family.O N p (V.wheel.atCut (N,p) (j i) (v i)) (o.origin i) Y) upper U := by
  let f := leg R N p V j v o
  let Y := R.family.path.rep N p
  have bill := paid R smooth N p V j v o ref (le_rfl : N≤N)
  rw [gust_base,entered R smooth N p V j v o ref] at bill
  rw [entered R smooth N p V j v o ref,actualTransport_unnormalize C R.makes (le_rfl : N≤N)]
  have part := congr_fun (pushpart upper (birth J₀ (Y N) f) s bill) U
  rw [part]
  have terms (W) : ((birth J₀ (Y N) f) W).part s =
      (Y N).eval W • (∏ i∈s.val, R.family.O N p (V.wheel.atCut (N,p) (j i) (v i)) (o.origin i) W) := by
    unfold birth Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
    rfl
  simp_rw [terms]
  rfl

end YM.Integration.WilsonPositionThermometerDepositedFaces
end
