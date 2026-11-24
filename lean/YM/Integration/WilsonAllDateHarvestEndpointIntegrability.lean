import YM.RG05Readout.Many.Stage

/-! Admission of a counterfactual marked comparison at a purchased physical (step).
The original inventory reassembles every old hard cofactor and proves the full
comparison density is integrable against the actual lattice prior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestEndpointIntegrability

open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker MergeProof
open MergeProof.Accent MergeProof.Menu RG05Readout RG05Readout.Many RG05Readout.Address
open Extra.Histories Push Ac GridApprox.Nil Local Extra.Trajectories Extra.Multi
open scoped BigOperators Classical

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {J:Census V}
variable {A:History G} {N m p:ℕ} {r:ℕ→ℕ} {a b c:ℝ}
set_option quotPrecheck false
local notation "fine" => A.rep N p (m+1)
local notation "coarse" => A.rep N p m
local notation "step" => A.levels.clock.op m p
local notation "f" => A.S.side (m+1) p
local notation "v" => A.S.side m p
variable {D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
variable {I:V→Address.Three G (A.S.side (m+1) p)} {Q:V→Address.Three G (A.S.side m p)}
variable {o:V→Site (A.S.side (m+1) p)} {w l:V→ℝ} {X:Config G (A.S.side (m+1) p)→Poly J}

theorem original : Coursework A r D a b c → A.Selected → m<N →
    (∀i,0<w i) → (∀i,Ride step (o i) ((step).ratio.parent (o i)) D 1 (I i) (Q i) (l i)) →
    Occupancy o (r m) → (∀i,2*w i*l i≤1) →
    Served fine (fun i=>(I i).2.1) (fun i=>profile (fine).activities (I i).2.2)
      X o w ((A.levels.budget (m+1)).supportExponent-1) 1 →
    MenuBoard fine I X o w ((A.levels.budget (m+1)).supportExponent-1) 1 := by
  intro course sel hm hw ride ho cost served
  refine ⟨?_,fun i=>(ride i).old,served⟩
  have valid:=sel.represents N p (m+1) hm
  have freight : Served fine (fun i=>(I i).2.1) (fun i=>profile (fine).activities (I i).2.2)
      X o w ((A.levels.budget (m+1)).supportExponent-4) 1 := by
    obtain ⟨H,K,ck,hH,hK,eq⟩:=served
    exact ⟨H,K,ck,hH.shrink (by linarith) le_rfl hw,hK.shrink (by linarith) le_rfl hw,eq⟩
  choose sets finite coins hcoins evidence using fun i=>(ride i).pays
  have level : (fine).p=A.levels.budget (m+1):=valid.vac
  obtain ⟨L,inst,packet,_,_,_,_,appearance⟩:=
    inventory (p:=(coarse).p.supportExponent) hw course.publishes.contact
      course.publishes.tunes course.publishes.propagate valid.good freight
      (by linarith only [course.poses.exp.2]) (by rw [level]; linarith only)
      (fun i=>⟨sets i,finite i,evidence i⟩) ho zero_le_one cost
      (fun i=>(mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (hw i).le one_le_two) (ride i).nonneg).trans (cost i)) (by linarith only)
  let promoter : Poly J →ₗ[ℂ] Poly J :=
    { toFun:= (Poly.pass (Mach J coins)*·)
      map_add':=fun _ _=>mul_add ..
      map_smul':=fun _ _=>mul_smul_comm .. }
  rw [show X=(fun U=>Poly.pass (Mach J coins)*Expense packet w step U) from funext appearance]
  exact (promoter.restrictScalars ℝ).toContinuousLinearMap.integrable_comp
    (heat packet step w valid.good)

end YM.Integration.WilsonAllDateHarvestEndpointIntegrability
