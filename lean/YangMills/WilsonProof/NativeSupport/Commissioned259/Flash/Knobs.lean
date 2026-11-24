import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Decks
/-! # (G.9): all derivatives & values after grid comparison. Hypotheses as earned.
 Use G.6 with phase-covariant mixed fields. This all at H_r.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open FVA2.Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d e :ℕ}{I:Type}{F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {K:Set (Points n)}{E:Set (Points m)}{x:I→Points n}{y:I→Points m}{r T:I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S)(N:WilsonPrescription G)(Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(H0:LogTrace U Q.port)
    (hJ : Leading U J)(hp: normal U J N.store) {sim:G.Simple}{dial:Bool}
    (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial){A' :∀ d:ℕ,ℝ→Change G d}
    (P:Realized J Y N A' (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "g" => (fun i=>g0 G (r i))
local notation "t" => Paper.meter U J N.criterion
local notation "τ" => t ∘ r
local notation "Φ" => (fun i=>joins (x i) (y i) (T i))
variable (h : Aim F G W a b r T) (R:Room W c δ A B)(hx:∀ᶠ i in F,x i∈K)(hy:∀ᶠ i in F,y i∈E)(hm:Amplifies K A)(hv: Amplifies E B)
    (v:Tags G d (n+m))
    (o:I→Viewers U) (L : Loader G U J N W K E)
    (ha:0<a)(hb:0<b) (ν:ℝ)
include H
lemma height_reply (w:Tags G e n) (hp:e≤d) {x:Points n} (hx:x∈conf n) : storyV N w x=storyV N (up hp ∘ w) x := by
  let P:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  refine PowerSeries.ext (fun i=>?_); rw [story_charge,story_charge,fxt,fxt,dif_pos hx,dif_pos hx]; exact Scale.Measure.paths N.scheme N.criterion 0 M _ sim P.Taylor P.still P.base hp _ _ _ w
lemma align {r:ℝ}{x:Points n} (hx:x∈conf n) (v:Tags G e n)(he:e≤d)(h:heights U Y r d)(o:Viewers U)(h':0<r)(p:ℕ) :
    differ (N:=N) U J Y r p o v x=differ (N:=N) U J Y r p o (up he ∘ v) x := by
  unfold differ; rw [Pi.sub_apply,Pi.sub_apply]; refine congr_arg₂ (·-·) ?_ (congr_arg (crop p (t r)) (height_reply N M H v he hx))
  exact Eq.symm (rises_on U Y o h' hx h (D:=fun _=>e) v (fun _=> he))
include P hJ U J Y N M H Q H0 S0 S1 hp hx hy R h hm hv ha hb ν L
lemma round (p:ℕ) : Coin F T τ g p Pose.home (fun i=> physicalY U Y (o i) v (r i) (Φ i)) (fun i=>storyV N v (Φ i)) := by
  have hp' := hx.mono fun i hi=> includes hm hi; have hE := hy.mono fun i hi=> includes hv hi
  let D:= max 6 d; let w:= up (G:=G) (show d≤D from le_max_right ..) ∘ v
  refine ⟨PT_value R ν H h hp' hE _,Fare.congr ((lands U J Y N Q H0 hJ hp M H P S0 S1 h R hx hy hm hv (le_max_left ..) w o L ha hb ν p).extend (v:=fun i=>g i^(p+1)*1) (Eventually.of_forall fun _=>(mul_one _).symm)) ?_⟩
  filter_upwards [h.reach.eventually (Original.height (taking U J Y N hJ P M H S1 hp) D), h.reach.eventually self_mem_nhdsWithin,permit R h hp' hE] with i hi e p0
  exact (align U J Y N M H p0 v (show d≤D from le_max_right ..) hi (o i) e p).symm

variable (l : List (Fin (n+m)×Axis))
local notation "X" => physicalY U Y
lemma fitted (p:ℕ): Coin F T τ g p Pose.home (fun i=> dots l (X (o i) v (r i)) (Φ i)) (fun i=>indexed N l v (Φ i)) := by
  induction l generalizing d with
  | nil=> refine (round U J Y N Q H0 hJ hp M H P S0 S1 h R hx hy hm hv v o L ha hb ν p).congr (EventuallyEq.refl ..) (Eventually.of_forall fun i=>?_) (EventuallyEq.refl ..); apply PowerSeries.ext; intro i; simp_rw [indexed,storyV,Reg.Point.story,coeff_mk,dots]
  | cons k l ih=>
    let Qk:= Classical.choice (enrollment N M H (d+1)); have h0 := aspirant R h
    have he:= Pose.guaranteed U J hJ N hp M H S1
    let w(i:I):= upgrade U Y d (r i) k.2 (v k.1)
    have hphi b: Coin F T τ g p Pose.home (fun i=> coord b (w i)) (fun _=> sizeIt N Qk (v k.1) k.2 b):= currency (Worth.comp h.reach ( Sparks.size U J Y N hJ P M H S1 hp Qk (v k.1) k.2 b ) p)
    have hof a:= Coin.mul (peson _ _ _ M H P he h.reach) (h.reach.eventually ((coupling_payment sim he).mono fun i hi=>hi.2.1)) (h.reach.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) h0 (hphi a) (ih (roster v k.1 a))
    have hp0 := permit R h (hx.mono fun i hi=> includes hm hi) (hy.mono fun i hi=> includes hv hi)
    refine (Coin.sum h0 (s:=Finset.univ) (fun i _=>hof i)).congr ?_ ?_ (Eventually.of_forall fun _=> one_mul _)
    · filter_upwards [hp0,h.reach.eventually (Original.height (taking U J Y N hJ P M H S1 hp) (d+1)),h.reach.eventually self_mem_nhdsWithin] with i hi x hz
      exact (banked k l hi U Y v (o i) hz x).symm
    filter_upwards [hp0] with i hi
    exact (compounded k l hi U J Y hJ P H S1 hp v Qk).symm
end YM.FVA2.GradedFar259.Flash
