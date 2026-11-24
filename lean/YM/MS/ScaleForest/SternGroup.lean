import YM.MS.ScaleForest.SternBranch
import YM.MS.ScaleForest.Bubbles

/-!
# Factor the actual simple-pole subgraph complement

Before infrared limits, show explicitly that we used the still-regulated
D(z)/z ADDEND to the triangle. In particular the arithmetic correction in the
GhostPole comparator alone doesn't prove this. All diagrams in the groups
specified in `Triangle.triangle` computed by the stated integrals. Use later
for finite term, including in the smooth placements. Distinguish the local
vertex $g²/2 A.R.A / z$ (on AA as computed in Bubbles) from the W-jet on
the whole two-loop example. Neither determines the finite piece of the
laurent coefficient by itself. The preparatory PP outside the subgraph V
vanishes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder
open scoped Topology ContDiff
namespace Triangle
open Planted Quadratic
variable {G : Gauge} {I : Type} (μ : ℝ) (X Y : Pupil) (A:I→QP) (V:GraphSum G true 4) {F H:Flats G} {U W P:Curtain G I}
local notation "L"=> LocalVertex G true 4
local notation "d"=> cursor false
local notation "prep" F=> Result.prep F
variable (R:LocalVertex G true 4) (k:ℕ)

def pol := collapsed (Ice k R.symbol)
def proton (U:Curtain G I): Curtain G I := fun z=> z⁻¹ ^ k • U z

lemma start_single (F:Coat G)(n w:ℕ): (startPaid μ w (Finsupp.single n F):Curtain G I)=slicePage μ w n F:= by
    unfold startPaid; change Finsupp.sum _ _=_; rw [ Finsupp.sum_single_index ]; funext z s t; change _ • (0:Mob G)= 0; exact smul_zero _
lemma start_proton (F:Mob G)(n w:ℕ): (startPaid μ w (Finsupp.single n (Ice k F)): Curtain G I)=proton k (startPaid μ w (Finsupp.single n (fun _=> F))) := by
   funext z s t; simp only [start_single,slicePage,proton,Pi.smul_apply,Ice]; exact smul_comm ..

lemma Arm_fixed : armData X (pol R k)= collapsed (Ice k (firstSymbol R (enrol X G 0) d)):= by
    unfold armData plain; rw [ originPin, renorm_vertex ]; exact frozenLeft ..
lemma Arm_vertex : armData X (vertex R).instructions.renorm= classicalPage (firstSymbol R (enrol X G 0) d):= Eq.trans (arm_proper X (vertex R)).symm (first_prep ..)

lemma plantVert : vertical (proton k U)=proton k (vertical U) := by
    funext z s x n l; simp only [proton,vertical,mend,velocity,Pi.smul_apply,← cert,map_smul,integral_smul]
lemma uVal (ht:Visits U): Iris (Ufor (cursor false) μ (proton k U)) (proton k (Ufor (cursor false) μ U)) := by
    filter_upwards [ht] with z h; funext s x; simp only [proton,Pi.smul_apply,Ufor,closeG_eq]; rw [scaleR (cursor false|>.ok.forms false) (h _ _),smul_comm]
lemma pVal (hp:Visits U)(ht:Visits W) : Iris (Pfor d μ (proton k U) W A) (proton k (Pfor d μ U W A)) ∧
    Iris (Pfor d μ W (proton k U) A) (proton k (Pfor d μ W U A)) := by
    constructor <;> (filter_upwards [hp,ht,Shine.high0] with z hP hT hZ; funext s x; let hK:= (cursor (G:=G) false).ok; have H(F T:Mob G) (h:Form0 false F)(hh:Form0 false T)(a b:ℂ): pinned (cursor false).half z (μ+s) (exp (-s) • A x) (a • F) (b • T)= (a*b) • pinned (cursor false).half z (μ+s) (exp (-s) • A x) F T:= pin_smul _ (hK.forms false) hK.even hK.rev h hh hZ .. )
    · obtain he:=H _ _ (hP s x) (hT s x) (z⁻¹^k) 1; rw [mul_one,one_smul] at he; exact he
    obtain he:=H _ _ (hT s x) (hP s x) 1 (z⁻¹^k); rw [one_mul,one_smul] at he; exact he
lemma bVal : Bfor d (proton k U) W= proton k (Bfor d U W):= by funext z s t; simp only [proton,Pi.smul_apply,Bfor,bridgeG_eq (cursor (G:=G) false).ok.rev, ← schedule,map_smul,LinearMap.smul_apply ]
lemma coal_seal (ht:Visits (vertical U)): Iris (sealPay μ (proton k U)) (proton k (sealPay μ U)):= by unfold sealPay sealUp; rw [plantVert,← plantVert (U:=Ufor d μ (vertical U))]; exact recoil (uVal _ _ ht)

section
variable [TopologicalSpace I][FirstCountableTopology I] (hA:AdmittedGap A) (hR:R.rank=2)

include hR
omit [TopologicalSpace I][FirstCountableTopology I] in
lemma roll : Board true (vertex R).instructions.renorm:= by obtain ht:=(vertex R).accepted; have hp:(vertex R).slots=2:=hR; exact ⟨ ⟨_, hp ▸ ht.usable⟩, hp ▸ ht.after_rank⟩
include hA
omit hA hR in
private theorem priceCo (W U: Curtain G I)(hp: Iris W (proton k U))(hu:cred U 2) : Iris (sealPay μ W) (proton k (sealPay μ U)):=
    EventuallyEq.trans (seals μ hp) (coal_seal μ k ((migrate_m hu.choose_spec).tide (fun _ h=> paceVisits (paceFuel h.1))))

-- q graph integral numerator, factor off the pole
lemma x_light : Iris (sealPay μ (xSlope μ X Y A (pol R k))) (proton k (sealPay μ (xSlope μ X Y A (vertex R).instructions.renorm))) := by
   apply priceCo
   · obtain h:= (pVal μ A k (mercVisit (I:=I) μ (stored X (roll R hR))) (mercVisit μ (seat Y G))).1; unfold xSlope; rw [Arm_fixed]; rw [ Arm_vertex ] at h ⊢; rw [collapsed,start_proton]; exact h
   exact funded_x _ _ _ _ hA (roll R hR)
lemma y_light : Iris (sealPay μ (ySlope μ X Y A (pol R k))) (proton k (sealPay μ (ySlope μ X Y A (vertex R).instructions.renorm))) := by
   apply priceCo
   · obtain h:= (pVal μ A k (mercVisit (I:=I) μ (stored Y (roll R hR))) (mercVisit μ (seat X G))).2; unfold ySlope; rw [Arm_fixed]; rw [ Arm_vertex ] at h ⊢; rw [collapsed,start_proton]; exact h
   exact funded_y _ _ _ _ hA (roll R hR)
lemma b_light : Iris (sealPay μ (bSlope μ X Y A (pol R k))) (proton k (sealPay μ (bSlope μ X Y A (vertex R).instructions.renorm))) := by
   apply priceCo
   · unfold bSlope; rw [renorm_vertex]; unfold pol collapsed; rw [start_proton,bVal]
   exact funded_b _ _ _ _ hA (roll R hR)

lemma lighting : Iris (lineIntegral μ X Y A (pol R k)) (proton k (lineIntegral μ X Y A (vertex R).instructions.renorm)) := by
   unfold lineIntegral; have ht(X Y:Curtain G I): proton k (X+Y)=proton k X+proton k Y:= funext fun z=> smul_add ..
   rw [ ht,ht ]; exact EventuallyEq.add (EventuallyEq.add (x_light μ X Y A R k hA hR) (y_light μ X Y A R k hA hR)) (b_light μ X Y A R k hA hR)

variable (hV:V.slots=2) (hs:V.instructions.pole=Ice k R.symbol)
include hV hs

lemma combined : Iris (nominal μ (triangle X Y A V)) (lineIntegral μ X Y A V.instructions.prep+proton k (nominal μ (triangle X Y A (vertex R)))) := by
   obtain ht:= EventuallyEq.trans (accounted μ X Y A V hV) (line_pair μ X Y A hA (boarded V hV) (board_q V hV))
   rw [hs] at ht; have hz:= lighting μ X Y A R k hA hR
   refine EventuallyEq.trans ht (EventuallyEq.add EventuallyEq.rfl (EventuallyEq.trans hz ?_)); filter_upwards [accounted μ X Y A (vertex R) hR] with z hv; rw [proton,proton,hv]
end

open TwoPoint
def ghostV (G:Gauge):= bubble G true true
lemma ghostT (G:Gauge): kPrice (poleTensor G true true):= ((rank_pole G true true).1.fine.tune.mer.price.exists).choose_spec

def ghostR (G:Gauge):= PoleVertex (ghostV G) 1 (poleK G true true) (ghostT G)

-- Not claiming the same for a different proposed tensor-mark template.
-- This family uses the calculated ghost self-energy.
theorem ghost_input [TopologicalSpace I][FirstCountableTopology I] (h: AdmittedGap A) :
    Iris (nominal μ (triangle X Y A (ghostV G))) (lineIntegral μ X Y A (ghostV G).instructions.prep + proton 1 (nominal μ (triangle X Y A (vertex (ghostR G))))) := by
    exact combined μ X Y A (ghostV G) (ghostR G) 1 h rfl rfl (poleK G true true)

theorem prep_no_pole_mark : (bridge d (ghostV G) (originPin X G)).instructions.pole=0:= branch_cursor X _ _ rfl
lemma in_page1 : (ghostV G).instructions.prep= Finsupp.single 1 (fun z=> scaleIntegral z 4 1 (ratePair G true true z)):= by rw [ ghostV, (twoVertex_laurent ..).1 ]; exact integrate_single ..

end Triangle
end YM.MS.ScaleForest
