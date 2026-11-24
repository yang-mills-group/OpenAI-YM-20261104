import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Money
import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Jets
import YM.Work.B10
/-! # Upper bounds for all required derivatives, in the two-length hypothesis.
   No G.9 expense input. To purchase M.1, need these near the rounding budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ} {I:Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W c δ A B)
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge} {N : WilsonPrescription G} (ν:ℝ) {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S) (Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (H0: LogTrace U Q.port)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial) {A0:∀d:ℕ,ℝ→Change G d}(P:Realized J Y N A0 (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ,Mixture U J N d) (S1: Shop U J N) (hJ: Leading U J)(hp: normal U J N.store)
    (h:Aim F G W a b r T)(hb:0<b) (hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
    (u:Tags G d (n+m)) (v : I → Viewers U)
    (l : List (Fin (n+m)×Axis))
local notation "s" => fun i:I=>r i*T i
local notation "t" => Paper.meter U J N.criterion
local notation "τ" => t∘r
local notation "g" => g0 G ∘ r
local notation "Jx" => (fun i:I=> joins (x i) (y i) (T i))
local notation "P'" => Pose.home

include R h H P hJ S1 hp hx hy ν U J Y
lemma V_price : Tunes T F P' (fun i=> indexed N l u (Jx i)) := by
  induction l generalizing d with
  | nil=> intro i; simp_rw [Sparks.indexed, coeff_mk, Sparks.dots]; have ht := PT_value R ν H h hx hy u i; simp_rw [storyV, Reg.Point.story, coeff_mk] at ht; exact ht
  | cons a l ih=>
    let Q:= Classical.choice (enrollment N M H (d+1))
    have hf (i:Toon G (d+1)) : Tunes T F Pose.home (fun _=>sizeIt N Q (u a.1) a.2 i):= fun _=> Fare.constant _
    intro j; refine (Tunes.sum (aspirant R h) _ Finset.univ (fun i (_:i∈(Finset.univ:Finset (Toon G (d+1))))=> Tunes.mix (aspirant R h) (hf i) (ih (roster u a.1 i))) j).congr ?_ |>.extend ?_
    · filter_upwards [permit R h hx hy] with i hi; exact congr_arg (coeff j) (compounded a l hi U J Y hJ P H S1 hp u Q).symm
    exact Eventually.of_forall fun _=> one_mul _
-- TRUE kernels prices. Use earlier Q hypotheses now paid separately.
include S0 H0 hb
lemma account : Allowance F r P' (fun i=> dots l (physicalY U Y (v i) u (r i)) (Jx i)) := by
  have hp':= taking U J Y N hJ P M H S1 hp
  have hh:= Pose.guaranteed U J hJ N hp M H S1
  induction l generalizing d with
  | nil=> exact (onRows R ν U Y Q H0 hp' H (G1_step U J Y N hJ P ν M H S1 hp S0) hh h hb hx hy u v v).1
  | cons a l ih=>
    let Q:= Classical.choice (enrollment N M H (d+1)); have hf i := Worth.comp h.reach ( Sparks.size U J Y N hJ P M H S1 hp Q (u a.1) a.2 i ) 0
    have hc i : Allowance F r P' (fun j=> coord i (upgrade U Y d (r j) a.2 (u a.1))) := Allowance.covers (isBigO_const_of_tendsto ( Sparks.cost (peson _ _ _ _ H P hh h.reach) ((g0_zero sim).comp h.reach) (hf i)) one_ne_zero)
    refine (Allowance.sum h.reach Finset.univ _ (fun i (_:i∈(Finset.univ:Finset (Toon G (d+1))))=> Allowance.mul (hc i) (ih (roster u a.1 i))|>.extend (u:=Pose.home) (Eventually.of_forall fun _=> one_mul _) )).congr ?_
    filter_upwards [h.reach.eventually (Original.height hp' (d+1)),permit R h hx hy, h.reach.eventually self_mem_nhdsWithin] with i hi p hr
    exact (banked a l p U Y u (v i) hr hi).symm
lemma nominated : Allowance F r P' (fun i=> fderiv ℝ (physicalY U Y (v i) u (r i)) (Jx i)) := by
  have ht z:= account R ν U J Y Q H0 H P S0 S1 hJ hp h hb hx hy u v [z]
  apply Allowance.travels (Allowance.sum h.reach Finset.univ _ (fun i (_:i∈(Finset.univ:Finset (Fin (n+m)×Axis)))=> (ht i).norm))
  apply IsBigO.of_bound'; apply Eventually.of_forall; intro i
  exact ( Work.B10.norm_le_direction_sum _ ).trans ( le_abs_self _ )
omit S0 H0 hb
lemma patent (p:ℕ) : Fare T F P' (fun i=> fderiv ℝ (fun z=> coeff p (storyV N u z)) (Jx i)) := by
  have ht z:= V_price R ν U J Y H P S1 hJ hp h hx hy u [z] p
  have hz z : Fare T F P' (fun i=> ‖coeff p (indexed N [z] u (Jx i))‖) := by obtain ⟨i,h⟩:=ht z; exact ⟨i,isBigO_norm_left.mpr h⟩
  obtain ⟨k,H⟩:= Fare.sum (aspirant R h) ( «s»:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Fin (n+m)×Axis)))=> hz i)
  refine ⟨k,(IsBigO.of_bound' (Eventually.of_forall fun i=>?_ )).trans H⟩
  exact ( Work.B10.norm_le_direction_sum _ ).trans ( by rw [Real.norm_eq_abs]; simp_rw [ Sparks.indexed, coeff_mk ]; exact le_abs_self _ )
end YM.FVA2.GradedFar259.Flash
