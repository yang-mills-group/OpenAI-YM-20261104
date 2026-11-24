import YM.Juniper.Bright.Lift
import YM.Juniper.Provider.Console
/-!
# Scheduling boost G: obtains the NEW epoch modeling atlas numbers.
 autumn pan Terms c/(8) from INCORE. Budget support through current stage; doesn't
 ask supershell next β permits. Stage high chosen `mast`, derivative uses current stage.
 Expenditure warranties. (console). Signature for Companion L2 expansion later.
 Calling WHEN sparse clocks actual.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {i j :ℕ}

-- numerical predicate s actual and kernel R before boost
variable {C: Targets X.p X.K} (D: Rolls X.p) {E: Expenses C}
    {p:Return.Wages}{v : ℕ→ℝ} (R:PhysicalNext.Repeat.Register D E p v) (P: PostCost D)
abbrev widest (D:Rolls X.p)(C: Targets X.p X.K) (j i:ℕ) (t:ℝ): ℝ := Trio.paySide G (D.L j) (trek (C j i|>.halo) (mast j)) t
-- StageFee uses the profile at the selected stage and index.

def StageFee (j i:ℕ) (t :ℝ) : Prop :=
    let L:= D.L j; let u:= radiusB t; let k:= X.p.profile i; let Y:= trek (C j i|>.halo) (mast j); let T:=Trio.base Y u; let e:=E j i; let n:= betaF G t L; let s:=gold G L t; let z:= Height.away k
    (e.wanting= -(7/16:ℝ)) →
    ((PearlAt (C j i) L) → Valuable (E j i) L (mast j) k.power k.order Chi.canonical t (R.μ j i) (deep j) (R.o j i)) ∧
    z*((n^deep j+n^deep j)+n^deep j) ≤ s ∧
    Real.exp (-(k.width/4)*u)*(n^(-(7/16):ℝ))≤ n^deep j ∧
    (s+ z*(planks G L Y k t*Real.exp (stout k*coverTicket Y))≤(1/2:ℝ)*(Time.credit G k * δE t)) ∧
    Marlin.tithe (2*T) (Trio.lossFee G L e.wanting Y k t) ⟨k.power,k.order,k.supportExponent,1,1,k.power_ge,k.order_ge,k.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicket Y) ≤ n^(-(1/8):ℝ) ∧
    ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G t L→∀ c f:Side, 2*T<c.val→∀ w:ℕ,w+1≤T→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors T o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), Boulevard.actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L t < eaves G L t
local notation "L" => D.L j
local notation "H" => trek (C j i|>.halo) (mast j)
local notation "Y"=> X.p.profile i
local notation "e"=> C j i
local notation "K"=> E j i
lemma pricetag (h:StepStages j i): ∀ᶠ x in atTop, StageFee D R j i x:=by
  let u:= R.o j i
  -- Rate.cutoff applies any x^late
  by_cases hF:(E j i).wanting= -(7/16:ℝ)
  swap; · exact Eventually.of_forall fun x hx=> (hF hx).elim
  have hh: Rate G L (deep j) (fun x=> Real.exp (-((Y).width/4)*radiusB x)):=by
     refine (Rate.cutoff (G:=G) («L»:=L) (a:=deep j) (show 0<(Y).width/4 from div_pos (Y).width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_)
     rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=(Y).width_pos; linarith))
  let s:= Height.away (Y)
  let t:= ((Rate.power (G:=G) («L»:=L) (a:=deep j)))
  have hξ : ∀ᶠ x:ℝ in atTop, PearlAt (C j i) L → Valuable (E j i) L (mast j) (Y).power (Y).order Chi.canonical x (R.μ j i) (deep j) u:= by
    by_cases hz:PearlAt (C j i) L
    · have hu:0<p j i:= (R.consumes _ _ h).1 -- check
      exact (hz (E j i) (p j i) (R.μ j i) u hu (R.consumes _ _ h).2.1 (by rw [hF]; norm_num) (deep j) (mast j) (Y).power (Y).order (meaningful j) Chi.canonical).mono fun x h _=> h
    exact Eventually.of_forall fun x h=> (hz h).elim
  filter_upwards [hξ,(((t.add t).add t).mul_left s) (-(23/20):ℝ) (by unfold deep; linarith only [Nat.cast_nonneg (α:=ℝ) j]),(hh.mul (Rate.power (G:=G) («L»:=L) (a:= -(7/16:ℝ)))) (deep j) (by linarith),Roof.compar G L H Y,Trio.cheap G L _ H Y hF, Trio.pledges G L (fun x=>Trio.base H (radiusB x)) (Trio.rows G L H|>.2.2.1.uses),Delay.shift_pos G L] with x hx hf hk he hh hq hX
  refine fun _=> ⟨hx,(le_abs_self _).trans hf,(le_abs_self _).trans hk,?_,hh,hq⟩
  have hu : 0≤ Height.away (Y):= by unfold Height.away; unfold Push.Local.turnCost; positivity
  exact le_trans (add_le_add (le_add_of_nonneg_left (mul_nonneg hu (Real.rpow_nonneg hX.le _))) le_rfl) he

variable {U: Protection D}
structure Gems (W:Delays U) : Prop where
    fees (j i:ℕ) : StepStages j i→∀ x,W.betaEntry j ≤ x → StageFee D R j i x
    penned (j i:ℕ): StepStages j i→Trio.maxFixed (trek (C j i|>.halo) (mast j)) ≤ W.shells j
    width : Pane.Planks D R P (widest D C) W (fun _ i=> (X.p.profile i).order)
lemma velvet (V : Delays U) : ∃ W:Delays U, DelayLe V W∧ Gems D R P W := by
   obtain ⟨W,hW,hp⟩:= Pane.school D R P (widest D C) (fun _ i=> (X.p.profile i).order) (fun i j h=> le_trans (by decide : 2≤6) (X.p.profile j).order_ge) (fun i j h=>Trio.circles ..) V
   obtain ⟨u,-,hu,hq⟩:= collect_upper W.betaEntry _ fun j=>eventually_transitions j _ _ (fun i (h:StepStages j i)=> pricetag D R h)
   let f i j:= Trio.maxFixed (trek (C i j|>.halo) (mast i)); let w:Delays U:= {W with betaEntry:=u, shells:= fun j=> fromMax f j ⊔ W.shells j}; have hw:DelayLe W w:=⟨hu,le_rfl,fun i=>le_sup_right,le_rfl⟩
   exact ⟨w,hW.trans hw,fun j i h x hx=> hq j x hx i h,fun i j h=> (le_fromMax f h).trans le_sup_left,hp w hw⟩

def charging (G:Gauge) : Legato.Booster G where
   asks S A _ W:= Gems _ S A W
   buy S A _ W:= velvet _ S A W
   mono h hv:= ⟨fun i j hi x hx=> h.fees i j hi x ((hv.beta _).trans hx),fun i j hi=> (h.penned i j hi).trans (hv.shells _),fun i j hi x hx=> h.width i j hi x ((hv.beta _).trans hx)⟩ -- Gems
end YM.Juniper.Bright
