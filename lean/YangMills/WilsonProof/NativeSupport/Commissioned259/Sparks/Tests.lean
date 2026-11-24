import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Legs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
/-! # The smeared probes of (G.9)(i) & their translation derivatives.
    Keep full unsmeared comparison cost since tests multiply the complete joint budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix Quotes
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d}
    (hJ:Leading U J) (P:Realized J Y N A (Paper.meter U J N.criterion))
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    (h : Shop U J N) (hp: normal U J N.store)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
abbrev storyV (u: Tags G d n)(x:Points n) := Reg.Point.story (fxt (V d) x) u
abbrev physicalY (v:Viewers U) (u : Tags G d n)(r:ℝ)(x:Points n) := trueK U Y v r x d u
lemma story_charge (u:Tags G d n)(p:ℕ)(x:Points n) : coeff p (storyV N u x)= fxt (V d) x p u:= coeff_mk ..
include H
lemma PT_cost (u:Tags G d n)(p:ℕ) : ContDiffOn ℝ ∞ (fun x=> coeff p (storyV N u x)) (conf n) := by
  let P:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  intro i hi; refine ((Speed.notice 0 N.scheme N.criterion M u i hi p).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(conf_open n).mem_nhds hi] with x hx
  rw [story_charge,fxt,dif_pos hx,Speed.now 0 N.scheme N.criterion σ M sim P.Taylor P.still P.base x hx]

-- integration by parts in this Test convention (compare `RG11Proof/Arrow/Start.hand`)
omit H
variable (a: Test n)
abbrev shiftT (i:Fin n) (b:Axis) (a:Test n) : Test n := (- TestFunction.lineDerivCLM ℂ (Points.direction i b)) a
lemma shiftT_app (i:Fin n) (b:Axis)(x:Points n): shiftT i b a x= - Points.gradient i b a x := by
   change -(TestFunction.lineDerivCLM (k:=⊤) ℂ _ a x)=_
   rw [TestFunction.lineDerivCLM_eq_fderivCLM (k:=⊤),show (TestFunction.fderivCLM ℂ ⊤ ⊤ a:Points n→ Points n →L[ℝ] ℂ)=_ from TestFunction.fderivCLM_apply_of_le a le_top]; rfl
lemma dcost {f : Points n → ℂ} (hf:ContDiffOn ℝ ∞ f (conf n))(i:Fin n)(b:Axis): ContDiffOn ℝ ∞ (Points.gradient i b f) (conf n):= by
  intro x hx; exact (Analysis.dSmooth ((hf x hx).contDiffAt ((conf_open _).mem_nhds hx)) (Points.direction _ _) (by simp : (∞:WithTop ℕ∞)+1≤∞)).contDiffWithinAt
lemma translate (f : Points n→ℂ)(hf: ContDiffOn ℝ ∞ f (conf n))(i:Fin n)(b:Axis) :
    a.applyTo (Points.gradient i b f)= (shiftT i b a).applyTo f := by
   unfold Test.applyTo; change (∫ x, a x*fderiv ℝ f x (Points.direction i b))=_
   simp_rw [shiftT_app,Points.gradient,Analysis.D,neg_mul,integral_neg]
   refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ((show Integrable (fun x=>a x * Points.gradient i b f x) volume from a.smearing (dcost hf i b).continuousOn)) (a.smearing hf.continuousOn) (fun x _=> a.contDiff.differentiable (by simp) x) (fun x hx=>hf.differentiableOn (by simp) x (a.tsupport_subset hx) |>.differentiableAt ((conf_open _).mem_nhds (a.tsupport_subset hx)))
   have he:= (shiftT i b a).smearing hf.continuousOn
   simp_rw [shiftT_app,Points.gradient,Analysis.D,neg_mul] at he
   simpa using he.neg

def profile (w:Points n→PowerSeries ℂ)(a:Test n) := PowerSeries.mk fun i=> a.applyTo (fun x=>coeff i (w x))
lemma testprofile {w:Points n→PowerSeries ℂ} (hh:∀ k:ℕ, ContinuousOn (fun x=>coeff k (w x)) (conf n)) (p:ℕ)(t':ℝ) :
    a.applyTo (fun x=>crop p t' (w x))=crop p t' (profile w a) := by
  simp_rw [crop_apply,profile,coeff_mk,Test.applyTo,Finset.mul_sum]
  rw [integral_finsetSum]; · exact Finset.sum_congr rfl fun i _=> by rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun i=> by ring)
  intro i _; exact a.smearing ((hh i).const_mul _)
lemma test_coin {w : Points n → PowerSeries ℂ} (hh:∀ k:ℕ,ContinuousOn (fun x=>coeff k (w x)) (conf n)) (g s:I→ℝ) (p:ℕ)
    (X : I→Points n→ℂ) (hs:∀ᶠ i in L, ContinuousOn (X i) (conf n))
    (V':Coin (booth (tsupport a) L) home (s∘Prod.fst) (g∘Prod.fst) p home (fun i=>X i.1 i.2) (fun i=>w i.2)) :
    Coin L home s g p home (fun i=> a.applyTo (X i)) (fun _=>profile w a) := by
  refine ⟨fun j=>Fare.constant _,Fare.bare ?_⟩
  have ho i : ContinuousOn (fun x=>crop p (s i) (w x)) (conf n) := by simp_rw [crop_apply]; exact continuousOn_finsetSum _ fun k _=> (hh k).const_mul _
  refine (opening (w:=fun i=>g i^(p+1)) (hs.mono fun i h=>⟨h,ho i⟩) ?_ (subset_refl (tsupport a))).congr (fun i=>?_ ) (fun _=> (mul_one _).symm)
  exact (homebound V'.expense).congr_right fun i=>mul_one _
  rw [testprofile a hh]
include hJ h hp H P
lemma point_coin (u:Tags G d n) (R:Set (Points n))(x:I→Points n) {r:I→ℝ} (hr:Tendsto r L late)(hR:IsCompact R)(hz:R⊆conf n)(hx:∀ᶠ i in L,x i∈R)(p:ℕ) :
    Coin L Pose.home (t∘r) (δ ∘ r) p Pose.home (fun i=> physicalY U Y none u (r i) (x i)) (fun i=> storyV N u (x i)) := by
  let h' := Pose.guaranteed U J hJ N hp M H h
  refine Eval.fixed (Y:=fun i=> fxt (V d) (x i)) (peson _ _ _ M H P h' hr) (hr.eventually ( (coupling_payment sim h').mono fun i hi=> hi.2.1)) (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) (one_paid _) _ u ?_
  exact Quotes.cut U J Y N hJ h hp P M H hr ⟨n,R,hR,hz⟩ x hx d p
lemma true_coin (u:Tags G d n)(p:ℕ) : Coin late Pose.home t δ p Pose.home
    (fun i=> a.applyTo (physicalY U Y none u i)) (fun _=>profile (storyV N u) a) :=
   test_coin a (fun i=>( PT_cost N M H u i).continuousOn) _ _ p _ ((show ∀ᶠ i in late, 0 < i from self_mem_nhdsWithin).mono fun i hi=>fun x hx=>(regular_at U Y none hi hx u).continuousAt.continuousWithinAt)
    (point_coin U J Y N hJ P M H h hp u (tsupport a) _ tendsto_fst a.hasCompactSupport a.tsupport_subset placed p)
end YM.FVA2.GradedFar259.Sparks
