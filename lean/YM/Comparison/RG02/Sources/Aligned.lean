import YM.Comparison.RG02.Sources.Origins
/-!
# On origin/subhistory alignment

 History chosen once, even for the singleton removal. If top root aligned (`embed` at every
 step between), re-use EXACT source density propagation with all masks & engineering bump.
 If not, no such equality with origin transfer asserted; can use unaligned array endpoint. Use
 actual display at reference level with its certified budgets, not a new choice of masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sources
open Function Filter Finset MeasureTheory RG Lattice Wilson Overlay
open YM.Marker YM.Multi YM.Comparison.RG02.Order Actual Local
open YM.Extra.Trajectories (Names Insertions Probes matrixField)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V : Type} [DecidableEq V] (R : Census V)
variable {N p d m : ℕ} {C : Family G} (A : Probes C V N p) (h : C.Makes)
  (x : V) (s : ∀ i : ℕ, Site (C.side i p))
local notation "X" => array A.toInsertions R
local notation "P"=> (C.path.rep N p)
local notation "T" => (C.factory (A.d x) N p)
local notation "B"=> (A.effective x)
local notation "J"=> (C.localSection (A.d x))
def paidPoint (j : ℕ) := ((T).entries j ((T).terminal.symm B)).density 0 J (P j)
-- embedding may be proper subset (spacing).
def StepAlign := ∀ i, m≤ i → i < N → (C.path.levels.clock.op i p).ratio.embed (s i)=s (i+1)
def Rooted := A.place x=s N
variable (hr : C.ref (A.d x) ≤ m) (hm : m≤N) (hb : StepAlign (N:=N) (m:=m) (C:=C) s)
   (hx : Rooted A x (C:=C) s)
include hx hb hm hr h
local notation "R'"=> (R.fire x)
omit hx hb hm hr h in
private lemma degreeToken (j : ℕ) : amount (zoom A.toInsertions j) (R.fire x) = ((C.S.block j).val:ℂ)^(A.d x) := by unfold amount zoom; simp [Census.fire,Family.S,History.S,Levels.S]; rfl
lemma pin_origin : atMark (R') (X m)=paidPoint A x m ∘ Lattice.translate (s m) := by
   induction hm using Nat.decreasingInduction with
   | self=>
       funext U
       change (X N U).part _ = paidPoint ..; -- RHS infer
       rw [top]; unfold Overlay.Ride.bump Overlay.Ride.Product; simp_rw [Census.fire, Finset.prod_singleton]; rw [A.physical]
       have he:= h.calibrated (A.d x) N p hr; unfold paidPoint; rw [he.encode, (h.wilson.starts N p).2,A.eval_relocated h _ hr U,hx]
       have hv : bare (C.path.β N p N) (Lattice.translate (s N) U)=bare (C.path.β N p N) U:= by rw [← pull_one]; unfold bare; rw [energy_pull]
       rw [hv]; have ht:= C.translation (N:=N) (p:=p) 0 (s N) B U; rw [zero_add] at ht; rw [← ht]; rfl
   | of_succ k hk IH =>
       let D:= (C.path.levels.clock.op k p)
       have hg := h.calibrated (A.d x) N p (hr.trans hk.le)
       have ht:= show paidPoint A x k= ((C.S.block k).val : ℂ)^(A.d x) • D.push (C.path.β N p (k+1)) (paidPoint A x (k+1)) from hg.unnormalized k hr hk _
       have he : atMark (R.fire x) (yield (P (k+1)) (X (k+1)) D)= D.push _ (atMark (R.fire x) (X (k+1))) := funext fun V=> congrFun (grades ..) (R.fire x)
       change atMark (R') _=_; rw [← along R _ hk,at_times]
       have hj :=hr.trans k.le_succ
       change amount (zoom A.toInsertions k) _ • atMark (R') (yield _ _ D) = _
       have hB : StepAlign (N:=N) (m:=k+1) (C:=C) s:=fun i hi h=> hb i (k.le_succ.trans hi) h
       rw [he,IH hj hB,← hb k le_rfl hk]
       -- expose cost
       have hI:= Source.TransferData.density_int h.wilson hg ((C.factory _ N p).terminal.symm B) (k+1) hj hk
       rw [show D.push (P (k+1)).beta (paidPoint A x (k+1) ∘ Lattice.translate _) = _ from AxisShift.commute_tr (A:=C.path.levels) (m:=k) (p:=p) (s k) ((P (k+1)).beta) (paidPoint A x (k+1)) hI,degreeToken,ht]; rfl
lemma calibration_part (x₁ : Config G (C.side m p)) : (X m x₁).part (R') = tangent (P m)
    (AxisShift.carry (s m) (BranchOne.center ((T).entries m ((T).terminal.symm B)) J 0 (P m))) x₁ := by
   let F:= (T).entries m ((T).terminal.symm B)
   let D:= BranchOne.center F J 0 (P m)
   have hT:= h.calibrated (A.d x) N p (hr.trans hm)
   have hp : tangent (P m) D=paidPoint A x m := BranchOne.present F _ _ (h.wilson.represents N p m hm).good (hT.cap m hr hm _)
   rw [AxisShift.transported hm h.wilson D (s m), hp]; exact congrFun (pin_origin R A h x s hr hm hb hx) x₁
end YM.Comparison.RG02.Sources
