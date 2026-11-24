import YM.Integration.WilsonPositionProgramTrialPublicJointSourceParity

/-! The entire original inherited finite and covered transport of a marked source preserves its thermal and angular parity. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceParityCourse
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
open PowerSeries Matrix WilsonCoeffUV.Bank.Carp
open WilsonPositionProgramTrialPublicJointSourceParity (one turned faded)
local notation "MarkParity" => WilsonPositionProgramTrialPublicJointSourceParity.Signed
theorem scaled {M U:Type*}[AddCommGroup M][Module ℝ M]{l:ℕ}{P:Pal M U}
    (head:MarkParity l P)(c:ℝ):MarkParity l (c • P):=by
  intro e r miss
  simp only [Pi.smul_apply,head e r miss,smul_zero]

theorem gathered (A:Patch){D l:ℕ}{U:Type}{V:Type*}[AddGroup U](w:Site A.L)(x:U)
    (F:Pal (Vote D) (U×V))(head:MarkParity l F):MarkParity l (gatherT A w x F):=by
  intro e r miss
  funext p
  simp [gatherT,revolve,head e r miss]

theorem actual (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N m h k l:ℕ)(now:m<N)(P:TowerS G D)(head:∀n,MarkParity l (P.1 n)):
    ∀n,MarkParity l ((Spout A O' N m h k P).1 n):=by
  intro n
  change MarkParity l (gradeH (ll A m) h k • cloakP A O' N m k n (P.1 (n*(ll A m).L)))
  refine scaled (M:=Vote D) (U:=Woods G n) ?_ _
  unfold cloakP
  apply turned (M:=Vote D) (U:=Woods G n)
  · unfold collarT
    refine scaled (M:=Vote D) (U:=Woods G n) ?_ _
    intro e r miss
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro w _
    apply one _ _ _ _ _ _ ((old A O' simple valid N (m+1) (by omega)).basis _).evenP _ l _
      (gathered _ w _ _ (head _)) e r miss
  · exact back_cc (angle_tilt simple valid now)
  · exact even_back (angle_tilt simple valid now) (perch A O' simple valid now).parityC

theorem traveled (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k h m j l:ℕ)(before:m+j≤N)(P:TowerS G D)(head:∀n,MarkParity l (P.1 n)):
    ∀n,MarkParity l ((spools A O' N k h m j P).1 n):=by
  induction j generalizing P with
  | zero => exact head
  | succ j ih =>
    apply ih (by omega) _ (actual A O' simple valid N (m+j) h k l (by omega) P head)

theorem covered (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k h m j l:ℕ)(before:m+j≤N)(P:TowerS G D)(openLaw:On k P)
    (head:∀n,MarkParity l (P.1 n)):MarkParity l ((spools A O' N k h m j P).2):=by
  let Y:=spools A O' N k h m j P
  have available:On k Y:=spoolEnd before simple valid openLaw
  have finite:=traveled A O' simple valid N k h m j l before P head
  intro e r wrong
  exact ((available.shore e r).congr (Eventually.of_forall fun n=>finite n e r wrong)).exten Bends.zero

theorem leading {F:Frame G h}(T:SectionData F)(fit:h<D)(a:Alma F)(n:Side):
    MarkParity (valence F a) ((vein (plate T fit) a).1 n):=by
  intro e r miss
  funext x
  change fade (spear (dockG T n)) (sprig (collar T (sheet F a)) (valence F a) e) r x • jewelBloom fit a=0
  have name:MarkParity (valence F a) (sprig (collar T (sheet F a)) (valence F a)):=
    fun e r outside=>shine_dark (by omega)
  have gone:fade (spear (dockG T n)) (sprig (collar T (sheet F a)) (valence F a) e) r=0:=
    faded name (spear (dockG T n)) e r miss
  rw [gone,Pi.zero_apply,zero_smul]

theorem read {F:Frame G h}(P:TowerS G D)(l:ℕ)(head:MarkParity l P.2)(i:Alma F)(q:ℕ)
    (miss:(q+l)%2≠(valence F i)%2):coeff q (opal F P i)=0:=by
  rw [opal,coeff_mk]
  unfold glean
  apply Finset.sum_eq_zero
  intro r _
  split
  · rename_i room
    rw [head (q+r-valence F i) r (by omega),echo_zero]
  · rfl

theorem original (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k h m j:ℕ)(before:m+j≤N){F:Frame G h}(T:SectionData F)(fit:h<D)
    {H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)(hk:h≤k)(a i:Alma F)(q:ℕ)
    (miss:(q+valence F a)%2≠(valence F i)%2):
    coeff q (opal F (spools A O' N k h m j (vein (plate T fit) a)) i)=0:=by
  have healthy:Shimmer (plate T fit):=freshly T H fit sound pop
  exact read _ _ (covered A O' simple valid N k h m j _ before _
    (hailed (plate T fit) healthy a ((valence_cap ..).trans hk)) (leading T fit a)) i q miss

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceParityCourse
