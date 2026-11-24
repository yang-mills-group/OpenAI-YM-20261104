import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Clockwise
/-! # Choose resolution AFTER perturbative order and B. Space & derivative costs
on every point inside even the enlarged profiles. Use Viewers on H families.
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
variable {n m d :ℕ}{I:Type}{F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W c δ A B) {E:Type*} [Norm E]
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge} {N : WilsonPrescription G} (ν:ℝ) {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S) (Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (H0:LogTrace U Q.port)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial) {A0:∀d:ℕ,ℝ→Change G d}(P:Realized J Y N A0 (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)(hJ: Leading U J)(hp: normal U J N.store)
    (h:Aim F G W a b r T)(hb:0<b)(hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
    (u: Tags G d (n+m)) (v:I→Viewers U)
local notation "t" => Paper.meter U J N.criterion
local notation "g" => g0 G
local notation "Jx" => (fun i:I=> joins (x i) (y i) (T i))
abbrev reply (u:Tags G d n)(r:ℝ)(p:ℕ)(x:Points n):= crop p (t r) (storyV N u x)
def differ (r:ℝ)(p:ℕ)(v:Viewers U)(u:Tags G d n) := physicalY U Y v u r-reply U J (N:=N) u r p
include H
lemma responds (r:ℝ) (p:ℕ) (u:Tags G d n) : ContDiffOn ℝ ∞ (reply U J (N:=N) u r p) (conf n) := by
  unfold Flash.reply; simp_rw [crop_apply ]; exact ContDiffOn.sum fun j _=> contDiffOn_const.mul (PT_cost N M H u _)
lemma diff_smooth {r:ℝ} (hr:0<r)(p:ℕ)(u: Tags G d n)(v: Viewers U) {x:Points n}(hx:x∈conf n) :
    DifferentiableAt ℝ (differ U J Y (N:=N) r p v u) x := by
  refine ((regular_at U Y _ hr hx u).differentiableAt (by simp)).sub (((responds U J H r p u).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp))

include ν R P hJ hp S1 hx hy h
lemma fit (p:ℕ) : Fare T F Pose.home (fun i=> fderiv ℝ (reply U J (N:=N) u (r i) p) (Jx i)) := by
  have h0 := aspirant R h
  let w i (j:ℕ) := (t (r i):ℂ)^j
  let q i (j:ℕ) (x:Points (n+m)) := w i j * coeff j (storyV N u x)
  have hp0 : ∀ᶠ i in F, |t (r i)| ≤ 1 := h.reach.eventually ((coupling_payment sim (Pose.guaranteed U J hJ N hp M H S1)).mono fun i hi=> hi.2.1)
  -- multiplication with fare smul.CLM handles.
  have V j:= Tunes.budget_b (T:=T) hp0 j
  have W j : Fare T F Pose.home (fun i=> w i j • fderiv ℝ (fun x=>coeff j (storyV N u x)) (Jx i)) := by
    obtain ⟨z,hz⟩:= V j; obtain ⟨k,K⟩:= patent R ν U J Y H P S1 hJ hp h hx hy u j
    refine ⟨z+k,(hz.smul K).congr_right ?_⟩; intro i; rw [smul_eq_mul,pow_add]; unfold Pose.home; ring
  apply (Fare.sum h0 (s:=Finset.range (p+1)) (fun j _=> W j)).congr ?_
  filter_upwards [permit R h hx hy] with i hi; unfold reply; simp_rw [crop_apply]; symm; rw [fderiv_fun_sum]; · exact Finset.sum_congr rfl fun j _=> fderiv_const_mul (𝕜:=ℝ) (((PT_cost N M H u j).contDiffAt ((conf_open _).mem_nhds hi)).differentiableAt (by simp)) _
  intro j _; exact (contDiffAt_const.mul ((PT_cost N M H u j).contDiffAt ((conf_open _).mem_nhds hi))).differentiableAt (by simp)
include hb S0 H0
lemma buys (p:ℕ) : ∃ k:ℕ, (fun i=>fderiv ℝ (differ (N:=N) U J Y (r i) p (v i) u) (Jx i))=O[F] fun i=> (g (r i))⁻¹^k := by
  obtain ⟨k,V⟩:= now_pays R h (sim:=sim) (nominated R ν U J Y Q H0 H P S0 S1 hJ hp h hb hx hy u v)
  have f := (cents R h (sim:=sim) hb (fit R ν U J Y H P S1 hJ hp h hx hy u p))
  have Hn (a' b':ℕ) (ht:a'≤b') : (fun i=> (g (r i))⁻¹^a')=O[F] fun i=> (g (r i))⁻¹^b':= by
    apply IsBigO.of_bound'; filter_upwards [ now ((pace sim).comp h.reach), near ((pace sim).comp h.reach)] with i l L
    change 0 < g (r i) at l; rw [norm_pow,norm_pow,norm_inv,Real.norm_of_nonneg l.le]; exact pow_le_pow_right₀ ((one_le_inv₀ (show 0 < g (r i) from l)).mpr L) ht
  refine ⟨k+1,(((V.congr_right fun _=>mul_one _).trans (Hn k (k+1) (by omega))).sub (f.trans ?_)).congr' ?_ (EventuallyEq.refl ..)⟩
  · simpa only [Pose.home, one_mul,pow_one] using (Hn 1 (k+1) (by omega))
  filter_upwards [permit R h hx hy,h.reach.eventually self_mem_nhdsWithin] with i hi hr
  unfold differ; rw [fderiv_sub ((regular_at U Y (v i) hr hi u).differentiableAt (by simp)) (((responds U J H _ p u).contDiffAt ((conf_open _).mem_nhds hi)).differentiableAt (by simp))]

omit hx hy h
-- use the resulting uniform bound BEFORE asking mesh-comparison purchase.
structure Register (U:Final C f S)(W a b:ℝ)(A:Set (Points n))(B:Set (Points m)) where
    r : ℝ
    T : ℝ
    inside : W ≤ T
    second : T ≤ a*g0 G r^(-b)
    x : A
    y : B
    v : Viewers U
lemma cost_y (p:ℕ) : ∃ K:ℕ, ∃ c₀:ℝ,0<c₀ ∧ ∀ᶠ r in late, ∀ T≥W, T≤ a*g r^(-b) →
    ∀ x∈A,∀ y∈B,∀ v, ‖fderiv ℝ (differ (N:=N) U J Y r p v u) (joins x y T)‖ ≤ c₀ * (g r)⁻¹^K := by
  let I:= Flash.Register U W a b A B; let r (i:I):= i.r; let F:=comap r late
  have H' : Aim F G W a b r Flash.Register.T := ⟨ tendsto_comap, Eventually.of_forall fun i=>i.inside,Eventually.of_forall fun i=> i.second ⟩
  obtain ⟨k,P⟩:= buys R ν U J Y Q H0 H P S0 S1 hJ hp H' hb (Eventually.of_forall fun i:I=> i.x.property) (Eventually.of_forall fun i:I=>i.y.property) u Flash.Register.v p (x:=fun i:I=>i.x.val) (y:=fun i:I=>i.y.val)
  obtain ⟨c₀,hc,C⟩:= P.exists_pos
  refine ⟨k,c₀,hc,?_⟩; filter_upwards [g0_pos sim,eventually_comap.mp C.bound] with r h e T hT hz x hx y hy v
  exact (e (⟨r,T,hT,hz,⟨x,hx⟩,⟨y,hy⟩,v⟩:I) rfl).trans_eq (by change c₀*‖(g0 G r)⁻¹^k‖=_; rw [Real.norm_of_nonneg (by positivity)])
end YM.FVA2.GradedFar259.Flash
