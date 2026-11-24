import YM.AllOrder.Horizon.Ticket

/-!
# Pre-L needs on any admit stage (extra Taylor estimates inside career)

Only high-veteran weighting needs pre-L for these costs; post-L arbitrary
permitted radius product ~ fixed KT and forecast. Choose stage-dependent
analysis index `ι`, affiliated derivative tape. Still require later licenses
for formal expansions/coupling. Does not change factor fields so can be added
before Delay.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {i j:ℕ}
section altitude
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P} {μ a e:ℝ} {s: Sheet G} {K : MapPrices} {C : Targets s K} (v : ℕ→ℕ) (Z : Expenses C)
local notation "X" => Z j i

def licensed (J : Q.Expense) (π : ℕ) (v Lw a : ℝ) (o : Target.Order G Lw) (x : ℝ) (L : Side) (k n : ℕ) (r : ℝ) :=
    ∀ (c' f : Side) (S : StepData c' f) (T : Tube G S), Works P L x S T → Stamp T → ∀ (R:RG.Rep G f) (H:Cash Lw x v L Q o a T R),
    ∃ (C' d v t A b r' B q i : ℝ) (l : ℕ) (N:Captain H k C' d v t A b r' B q l Chi.canonical), KeyStone J π H k n Chi.canonical N (betaF G x L ^ r) i

def Freq (v:ℕ→ℕ): Prop := ∀ j i, StepStages j i → ∀ L:Side,v j ≤ L.val →(C j i).rate < -(3/8:ℝ) → ∀ (u W c : ℝ) (o:Target.Order G W), 0<W→0<u→∀ k n, ∀ᶠ x:ℝ in atTop,
      licensed (Z j i) (tall i) u W c o x L k n (seam_hat i-1)
lemma leased (s : Sheet G) (C : Targets s K) (Z:Expenses C) : ∃ v:ℕ→ℕ, Freq Z v := by
  choose m hm using fun j i=> high_earns (C j i) (tall i);
  refine ⟨fromMax m, fun j i hij L hL hr u W c o hw hu k n=>hm j i L ((le_fromMax m hij).trans hL) _ W u _ o hw hu hr _ ?_ k n _⟩
  unfold tall seam_hat; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) i]

def creep (P : Stage) (s b : ℝ) (t:ℝ) (L:Side) : Prop := ∀ P':BudgetPoint,P'.threshold ≤2*Pressure.fiery G t L → P'.power=P.power→ P'.order=P.order→ P'.supportExponent=P.supportExponent→ P'.B = radiusB t → ∀ β z Λ,
    |β| ≤ 2*betaF G t L→ |z|≤ b → 0≤ Λ→ Λ≤ ConnectedActivityE6.loopBill G L t →
    Real.exp (-(P.width/4)*P'.B)*Song.octaveNeed G P' P.clip P.width P.paths Λ β z ≤ betaF G t L ^ s
variable (G)
lemma dues (P:Stage) (L : Side) (a e : ℝ) (h:0<a) : ∀ᶠ t:ℝ in atTop, creep (G:=G) P e a t L := by
  -- degree arbitrary width tail for all BudgetPoint, express post after ℓ shelf done.
  have ht: Rate G L (e-1) (fun x=>Real.exp (-(P.width/4)* (radiusB x:ℝ))) := by
    refine (Rate.cutoff (G:=G) (L:=L) (a:=e-1) (show 0<P.width/4 from div_pos P.width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_) -- from flights
    rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=P.width_pos; linarith)
  filter_upwards [Meadow.flights G L P _ h, Delay.shift_pos G L,(ht.mul (Rate.power (G:=G) (L:=L) (a:=-(7/16)))) e (by linarith)] with x hx hY hs P' hP hp hρ hT hX β z Λ ha he hu hL
  have hv := hx P' hP hp hρ hT hX β z Λ ha he hu hL; rw [hX]; exact (mul_le_mul_of_nonneg_left hv.1 (Real.exp_nonneg _)).trans ((le_abs_self _).trans hs)
end altitude

section summit
variable {X: Metals G} (D: Rolls X.p) {C : Targets X.p X.K} {Z :Expenses C} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v) (η : ℕ→ℕ→ℝ)
    {P : Protection D}

structure Summit (i j :ℕ) (t:ℝ) : Prop where
  script (k : ℕ) : k ≤ i → MorningP D R i j k ((X.p.profile i).order+i+3) t (η j i)
  sails : licensed (Z j i) (tall i) (R.μ j i) (p j i) (R.c j i) (R.o j i) t (D.L j) (X.p.profile i).order (X.p.profile i).power (seam_hat i-1)
  ducts : creep (G:=G) (X.p.profile i) (seam_hat i-1) (cloak D j) t (D.L j)
  total (B:BudgetPoint) : B.order=(X.p.profile i).order → B.power=(X.p.profile i).power →
    let u:= betaF G t (D.L j); let y:=u^(seam_hat i-1); turnFee B*(y+y)+y ≤ u^(seam_hat i)

-- retain key post Wish. choose launch `qpost` after ξ etc, e info never needed. Use Shelf basis.
lemma cloak_gt (j:ℕ) : 0<cloak D j:= by
  have hh := (X.p.profile j).drift_ge; unfold cloak; linarith [abs_nonneg (G.slopeConstant*Real.log (D.L j).val)]
lemma over_top (he:StepStages j i) {u:ℕ→ℕ} (h: Freq Z u) (hp:u j≤ (D.L j).val) (hq : (C j i).rate < -(3/8:ℝ)) (ho:0<η j i) : ∀ᶠ x in atTop, Summit D R η i j x:= by
  have hv := h j i he (D.L j) hp hq _ _ (R.c j i) (R.o j i) (R.consumes j i he).1 (R.consumes j i he).2.1
    (X.p.profile i).order (X.p.profile i).power
  have hf k (hi:k ≤ i) := announces D R he (show k+3 ≤ (X.p.profile i).order+i+3 by omega) ho
  set L:=D.L j; have ht:= Rate.power (G:=G) (L:=L) (a:=seam_hat i-1); set q:= X.p.profile i
  filter_upwards [(eventually_all_finset (Finset.range (i+1))).mpr (fun k hk=> hf k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))), hv, dues G _ L _ (seam_hat i-1) (cloak_gt D j), (((ht.add ht).mul_left (away q)).add ht) _ (show seam_hat i-1<seam_hat i by linarith)] with x hX hv hC hs
  refine ⟨fun k hk=>hX k (mem_range.mpr (Nat.lt_succ_of_le hk)),hv,hC,?_⟩
  intro B hB hP u' y; rw [show turnFee B=away q from congr_arg₂ (fun i j:ℕ=> Push.Local.turnCost i j) hB hP]; exact (le_abs_self _).trans hs

structure Lodge (W : Delays P) : Prop where
  terms j x (h: W.betaEntry j ≤ x) i : StepStages j i → Summit D R η i j x
  sizes j i : StepStages j i → Trio.maxFixed (parking (tall i) (C j i|>.halo)) ≤ W.shells j
  cost_growth i : 1 ≤ W.growth i

lemma funding (V:Delays P) {u:ℕ→ℕ} (h: Freq Z u) (hp : ∀ j,u j ≤ (D.L j).val) (hf: ∀ j i,StepStages j i → (C j i).rate < -(3/8:ℝ)) (he : ∀ j i,0<η j i) : ∃ W:Delays P,DelayLe V W ∧ ∀ Z': Delays P, DelayLe W Z' → Lodge D R η Z':= by
  obtain ⟨x,-,hv,hV⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi => over_top D R η hi h (hp _) (hf _ _ hi) (he _ _)))
  let v j i:= Trio.maxFixed (parking (tall i) (C j i|>.halo))
  refine ⟨{V with betaEntry:=x,shells:= fun i=> V.shells i+fromMax v i,growth:= fun j=>V.growth j+1},⟨hv,le_rfl,fun i=> Nat.le_add_right ..,fun i=> Nat.le_succ _⟩,fun _ h=>⟨fun j t he i hi=> hV j t ((h.beta j).trans he) i hi,fun j i hi=>?_,fun j=> (Nat.le_add_left 1 _).trans (h.growth _)⟩⟩
  exact ((le_fromMax v hi).trans (Nat.le_add_left (fromMax _ _) _)).trans (h.shells _)
end summit
end YM.AllOrder.Shop
