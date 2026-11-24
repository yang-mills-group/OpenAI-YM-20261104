import YM.MS.ScaleForest.ScreenArm
import YM.MS.ScaleForest.Joints

/-!
# The two marked insertion example. Which contribution do we calculate?

General construction used with the genuine proper subgraph `bubble`. Keep
its **pole vertex** in the same way as we do in all the other graph families.
The precise summand:

* Leading quadratic part of each mark (on the fibre with those two
  distinct pins). Left `X` is shifted by position A, anchor at `Y`.
* Drawings in which the proper two-point subtree `V` has formed before any
  line joining that component to the rest. Then join that to X or Y and the
  pair to the other mark, or X to Y and the pair to V. Then close. Use
  even lines in these three outer joins. No extra symmetrization at the pins.
  When rank of `V` is 2 this counts the SIX scale orders of the triangle
  outside the subgraph (two choices of second-line endpoint at the first
  pair; counted via the differentiations in the Feynman rules). No scale
  ordering with a disjoint component, in particular in the graph sums the
  rest of the triangle need not necessarily use only lines longer than ALL
  of those in V. In the ghost case choose V as in `Bubbles`.
* **Include all admissible pole subtractions therein**. The triangle outside
  the bubble has three edges: there is no symmetry divisor for the triangle
  made with full differentiated vertices as we use here. In particular don't
  divide the read by a further 2. See the calculation for the full
  complement. Of the further potential subtractions the only one outside V
  would be of a marked parent with just one mark attached to V. Use the
  jet criterion, proving it ZERO (not omitting that term based on ghost lore).
  Result below is before specializing on the dimension germ.

Care: our precise sum isn't claiming the *whole automorphism-free unordered
term with all lines of the ghost self-energy integrated from 0 to the upper
length, wherever they connect*. It's a sector family, using sectors with
that subtree. This is how a subdivergence appears under this choice of
forest prescription; the example family alone never supplies the whole
order. The other sectors are included in the big graph sum with their own
subtractions. The order-two ghost-loop contribution is one example. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder
open scoped Topology ContDiff
namespace Triangle
open Planted Quadratic
variable {G : Gauge} {I : Type} (μ : ℝ) (X Y : Pupil) (A:I→QP) (V:GraphSum G true 4)

/- forest convention for the contribution (before pin flows) -/
abbrev originPin (X:Pupil)(G:Gauge):= vertex (enrol X G 0)
local notation "K"=> cursor false
abbrev armBranch := bridge K V (originPin X G)

def nearX := Planted.P K A (bed (armBranch X V)) (bed (originPin Y G))
def nearY := Planted.P K A (bed (originPin X G)) (bed (armBranch Y V))
def mid (G:Gauge) := Planted.P K A (bed (originPin X G)) (bed (originPin Y G))
def nearB := Planted.B K V (mid X Y A G)
def streets : Planted.Plan G I true:= [nearX X Y A V,nearY X Y A V,nearB X Y A V]
def triangle : Planted.Plan G I true:= (streets X Y A V).map (Planted.U K)

theorem streetArity (W:Planted G I true) (h:W∈streets X Y A V)(he:V.slots=2): W.slots=2 := by
   simp [streets] at h; rcases h with rfl|rfl|rfl
   all_goals simp only [nearX,nearY,nearB,mid,Planted.slots,armBranch,originPin,GraphSum.slots,term_grade,he]; ring

theorem triangleArity (W:Planted G I true) (h:W∈triangle X Y A V) (he:V.slots=2): W.slots=0:= by
   obtain ⟨x,hx,rfl⟩:=List.mem_map.mp h; rw [Planted.slots,streetArity X Y A V _ hx he]; exact sub_self 2

variable [TopologicalSpace I] (h:AdmittedGap A)
include h
theorem hiredWalk : Hired (streets X Y A V):= by unfold streets Hired; simp [nearX,nearY,nearB,mid,Planted.Stand,h]
theorem hiredFamily : Hired (triangle X Y A V):= by intro i hi; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hi; exact hiredWalk X Y A V h j hj
omit h
-- also define the equivalent integral via preparing the bubble and contracting.
-- specified prior to summing the three branches.

variable (T:Flats G)
abbrev plain (X:Pupil) (G:Gauge) := (originPin X G).instructions.renorm
def armData := combine false 4 K T (plain X G)

def xSlope : Curtain G I := Pfor K μ (startPaid μ 4 (armData X T)) (startPaid μ 4 (plain Y G)) A
def ySlope : Curtain G I := Pfor K μ (startPaid μ 4 (plain X G)) (startPaid μ 4 (armData Y T)) A
def mCurve (G:Gauge): Curtain G I := vertical (Pfor K μ (startPaid μ 4 (plain X G)) (startPaid μ 4 (plain Y G)) A)
def bSlope : Curtain G I := Bfor K (startPaid μ 0 T) (mCurve μ X Y A G)
abbrev sealUp (μ:ℝ) (F:Curtain G I) := Ufor K μ (vertical F)
def sealPay (μ:ℝ)(F:Curtain G I) := vertical (sealUp μ F)

/-- Actual continued two-mark integral. Specification used with PREPARED
bulk body + PP complement. V represented here by its rank two tensor and Flats
pages (still viewed at arbitrary z). -/
def lineIntegral : Curtain G I := sealPay μ (xSlope μ X Y A T) + sealPay μ (ySlope μ X Y A T) + sealPay μ (bSlope μ X Y A T)

-- root replacement on the arm
omit [TopologicalSpace I] in
theorem arm_proper : (armBranch X V).instructions.prep=armData X V.instructions.renorm:= rfl
omit [TopologicalSpace I] in
lemma arm_ren (hV:V.slots=2) : (armBranch X V).instructions.renorm=armData X V.instructions.renorm:= by rw [Result.renorm,armBranch,branch_cursor X _ V hV,collapsed,Finsupp.single_zero,add_zero]; rfl
omit [TopologicalSpace I] in
theorem x_at (hV:V.slots=2): Iris (push μ (nearX X Y A V)) (xSlope μ X Y A V.instructions.renorm) := by simp only [nearX,push,resolve,xSlope]; rw [arm_ren X V hV]; exact pin_delivery (popTie _) (popTie _) _ _ _
omit [TopologicalSpace I] in
theorem y_at (hV:V.slots=2): Iris (push μ (nearY X Y A V)) (ySlope μ X Y A V.instructions.renorm) := by simp only [nearY,push,resolve,ySlope]; rw [arm_ren Y V hV]; exact pin_delivery (popTie _) (popTie _) _ _ _
omit [TopologicalSpace I] in
theorem b_at : Iris (push μ (nearB X Y A V)) (bSlope μ X Y A V.instructions.renorm) := bridge_delivery (popTie _) (recoil (pin_delivery (popTie _) (popTie _) _ _ _)) _
omit [TopologicalSpace I] in
private theorem seal_at {F:Planted G I true}{μ:ℝ}{U:Curtain G I} (ht:Iris (push μ F) U) : Iris (resolve μ (Planted.U K F)) (sealPay μ U) := by rw [resolve,rooting F μ]; exact recoil (close_delivery (recoil ht) _ _)
omit [TopologicalSpace I] in
theorem accounted (hV:V.slots=2): Iris (nominal μ (triangle X Y A V)) (lineIntegral μ X Y A V.instructions.renorm) := by
   obtain ht:= EventuallyEq.add (EventuallyEq.add (seal_at (x_at μ X Y A V hV)) (seal_at (y_at μ X Y A V hV))) (seal_at (b_at μ X Y A V)); unfold triangle streets nominal; simpa only [ List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero, ← add_assoc ,lineIntegral ] using ht

-- comparison to actual forest integral and reconstruction.
include h
variable [FirstCountableTopology I]
theorem full_account (hV:V.slots=2): Iris ((triangle X Y A V).flatMap (forests μ)).sum (lineIntegral μ X Y A V.instructions.renorm) ∧ Frontier (nominal μ (triangle X Y A V)) ∧
    ∀ s x, Lift (fun z=> lineIntegral μ X Y A V.instructions.renorm z s x) (nominal μ (triangle X Y A V) 0 s x) := by
    obtain ⟨⟨R,hR,hT⟩,hF,hP⟩:= abide μ _ (hiredFamily X Y A V h); obtain H:= accounted μ X Y A V hV; exact ⟨ EventuallyEq.trans (EventuallyEq.symm hP) H, hF,fun s x=> Lift.congr (Lift.trim (hT s x) hR.1) (H.mono (fun i hp=> congr_fun (congr_fun hp s) x))⟩

end Triangle
end YM.MS.ScaleForest
