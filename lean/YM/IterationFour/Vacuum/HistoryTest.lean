import YM.IterationFour.Schedule.Price

/-!
# Actual provenance and nontrivial cutoff test

See concretely how far the supplied iteration gets. Prove actual quantitative
matching to the *construction's* α reset and canonical cubic,quartic, loop
prescriptions, with exact `Early`-STYLE local interface (at different costs --
this one doesn't supply spendable σ and doesn't pretend to have already paid
the change to cubic/quartic). Leave all other columns as real residual activity,
no Laurent/counterterm ansatz on them. This is still partial: NO claim the
numbers in the construction agree with the desired Fk convention at positive
order. `z`-rates are specified and can be met on the shared witness. The formula
here is an estimate on the actual *remainder in* beta, not interpreting an
asserted drift law as a contraction. Pulls pre-local assemblies from the recipe
of the actually shot path at TWO or more steps, not from one constructive
example unrelated to calibration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum.HistoryTest
open Lattice Wilson RG Function MeasureTheory Filter Currency Render Progress.DirectedRecipe
open AnalyticBridge VerifiedReset Averaging Collection
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}
-- Important keep the same X output on all the identities.
structure Stamped (C : Family G) (N q i : ℕ) (α H w δ γ : ℝ) : Prop where
    income : ∃ (X : Listing G (C.side i q)) (s : Collection.Source G (C.side i q)) (τ : ℝ),
      let V:= C.path.rep N q (i+1); let U:= C.path.rep N q i
      let D:= C.path.levels.budget i; let r:=U.path; let c:= (C.path.levels.params i).clip
      let t:= branch X r c D s α
      Local X D s H w ∧
        earlyValue X r c D s V.beta τ α=(C.path.levels.clock.op i q).push V.beta V.eval ∧
        Ingredients (shelves X r D) t D δ γ ∧
        finish r c D (shelves X r D) t (V.beta+α+delta (X.read s)) (vac s τ) = U
variable (C : Family G) (eBeta : ℕ→ℕ→ℝ)

/-- `eBeta`: the constructed reference kinetic *increment* (with all its own
    assumptions). -/
def leadingPlan (N q : ℕ) : Plan C N q 2 :=
  { layers := fun _=>[]
    orders := fun _ _ _ he=> False.elim (by simp at he)
    coefficient := fun m _=>if m<N then eBeta N m else 0
    alpha := eBeta N }

-- extra provenance in addition to Oasis.Floral. Reuses real β data via
-- specified constructor, not from merely having masses.
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org Input Supply
open Precision UVExtension Roost Spire Orchard Mast Camp

def Installed (C : Family G) (hg : G.Simple) (eBeta : ℕ→ℕ→ℝ) :=
  ∃ (X : Metals G) (D:Rolls X.p) (A:Alloy X D) (R:Factor A)
    (S : Spire.Uses R hg) (t:ℕ→ℕ)(K:ℕ→ℝ)(w:Bid.Worth)
    (B:Bandage R K w) (L:Mast.Cellar S t B),
    C=Cellar.yard (Mast.roseA S) L ∧ eBeta=A.B.kin.alpha
structure Held (hg : G.Simple) : Prop where
    ink : Installed (C:=C) hg eBeta -- defined below
    profile (i N q : ℕ) (h:i<N) : ∃ w δ γ, Stamped C N q i (eBeta N i) (Time.forecastE C.path.levels i) w δ γ
    momentum (i N : ℕ) (h:i<N) : |eBeta N i + G.slopeConstant * Real.log (C.S.block i).val|+1 ≤ (C.path.levels.params (i+1)).drift
end YM.IterationFour.Vacuum.HistoryTest

namespace YM.UVExtension.Spire.IterationFour
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
open Orchard Mast
open YM.IterationFour.Vacuum.HistoryTest
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} {hG:G.Simple}

lemma local_registered (S: Uses R hG) {t K w} {B:PhysicalNext.Repeat.Legato.Bandage R K w} (L:Mast.Cellar S t B)
    (N q i:ℕ) (h:i<N) :∃ w δ γ, Stamped (Cellar.yard (Mast.roseA S) L) N q i (A.B.kin.alpha N i) (Time.forecastE A.B.a i) w δ γ:=by
  let H:=S.fits N q; let x:= H.Rest (S.cart N q) S.grove.coins 0
  let y:= H.Third (S.cart N q) S.grove.coins 0; let z:=H.Sail (S.cart N q) S.grove.coins 0
  let T:= H.race x y z; let J:= H.charts i h; let a:= A.B.a
  have ht : H.Shot x y z:= (H.acts _ (S.token N q) _ (Uses.centerP a)).1
  let W:= Market R J.atTopH; let V:= J.oracle R _ (ht.alive _ h) (z (i+1)); let P:= T (i+1)
  let s:= Item.song R J.atTopH J.W J.k V
  have he:T i= Item.issue R J.atTopH J.W J.k V:= ht.passes i h
  let D0:= a.budget i; let cStage:=(a.params i).clip; let α:= A.B.kin.alpha N i; let B₀:= A.B.kin.path N i
  have hv:= Guild.ready R h J.atTopH J.W J.k V.atH (V.links R J.atTopH) rfl V.related V.price V.aisle rfl S.grove.pledge J.hr
  have hp:= (Guild.standing R h J.atTopH J.W J.k V.atH (V.links R J.atTopH) rfl V.related V.price V.aisle rfl S.grove.pledge J.hr hG).1
  obtain ⟨hv',hD⟩:= Guild.hp_width R h P
  let Z':= flatRate a i q (T (i+1))
  let τ : ℝ:= Z' + (∑' i,s.logRead i 1)/ (UVNext.CouplingReset.sites (a.S.side i q)) -- namespace inspect
  have hs: Collection.vac s τ= Z' := by unfold Collection.vac τ; ring
  let d : ℝ:= P.beta+α+ Averaging.delta (W.read s)
  let Y:= Collection.branch W B₀ cStage D0 s α
  have hh : T i=finish B₀ cStage D0 (Collection.shelves W B₀ D0) Y d (Collection.vac s τ):=by rw [he,hs]; rfl
  have hΩ : earlyValue W B₀ cStage D0 s P.beta τ α = (a.clock.op i q).push P.beta P.eval:= by
    rw [←(A.B.links h ((H.serves ht i h).1)).link]
    funext U
    change _=(T i).eval U
    rw [hh]
    exact ((hp.unshifted B₀ cStage d (Collection.vac s τ) U).trans (hv.raw_evaluator hG (A.B.support.cap N i h.le) hv' hD α
      (by have h:= a.fits.sizeT i q; change 20 < (a.clock.schedule.side i q).val; omega) P.beta τ U)).symm
  exact ⟨_,_,_,W,s,τ,hv,hΩ,hp,hh.symm⟩
end YM.UVExtension.Spire.IterationFour
namespace YM.IterationFour.Vacuum.HistoryTest
open Lattice Wilson RG Function MeasureTheory Filter Currency Render Progress.DirectedRecipe
open AnalyticBridge VerifiedReset Averaging Collection
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} (hg : G.Simple) (ht : C.Makes)
lemma baked (h : UVExtension.Oasis.Floral (hG:=hg) C) : ∃ A, Held C A hg := by
  obtain ⟨M,P,Y,R,S,T,t,k,W,Q,L,H,hx,_⟩:=h
  subst C
  exact ⟨Y.B.kin.alpha,⟨⟨_,_,Y,R,S,t,k,W,Q,L,rfl,rfl⟩,
    fun _ _ _=> UVExtension.Spire.IterationFour.local_registered S L _ _ _,fun i N hp=> Y.B.support.kinetic N i hp⟩⟩

/-- Actual coefficient cost for α at these lengths, with a pre-L drift price. -/
lemma priced (a : Levels G) (m : ℕ) : (a.params (m+1)).drift ≤ Real.log (a.S.block m).val := by
  have he := a.fits.driftSmall m
  let k:=(a.clock.J (m+1):ℝ)
  have hq: 1 ≤ k:= by unfold k; exact_mod_cast (show 1≤a.clock.J (m+1) from by linarith only [a.clock.adm (m+1)]) -- binder
  have h : (k^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq)
  have hp:=Real.log_pos (show 1<((a.S.block m).val:ℝ) by
    exact_mod_cast (show 1<(a.S.block m).val by linarith only [a.S.block_large m]))
  simpa only [one_mul] using (div_le_iff₀ hp).1 (he.trans h)

variable {f : ℕ→ℕ→ℝ}
open Spending
lemma instance_spend (h : Held C f hg) {before after} (hp : Clock.Register C.path.levels before after) :
    Account C.path.levels Address.level (Financed.tenor Set.univ)
      (Financed.modelCharge (leadingPlan C f)) 0 := by
  let a := C.path.levels
  let g u:= Clock.doubleLog a (Address.level u)
  have hτ:= Spending.Account.gathered _ (Financed.warm Set.univ) (Clock.smallDouble C.path.levels hg) -- args
  have hz : Account a Address.level (Financed.tenor Set.univ) (fun u=> (G.slopeConstant+1)*g u) 0:= by
    simpa only [zero_add] using! Spending.Account.product (Spending.Account.constant hg (Financed.warm _) a (G.slopeConstant+1)) hτ
  apply hz.relax
  refine (Spending.okay _).mono fun ⟨N,q,i⟩ hv=>?_
  unfold Financed.modelCharge; simp only [leadingPlan]
  by_cases he:i<N
  swap
  · simp [he]; positivity
  simp only [if_pos he,Nat.reduceSubDiff,Finset.sum_const,Finset.card_range,zero_add,one_smul,abs_abs]
  apply le_trans ?_ (le_abs_self _)
  let R:ℝ:= (a.S.block i).val
  let L:=Real.log R
  have hx:=h.momentum i N he
  have hL : L≤Clock.doubleLog a i := by
    have ht:0<R:=by unfold R; positivity
    exact (Real.log_le_self ht.le).trans (hp.complete i |>.2)
  have hu : 0 ≤ L := Real.log_nonneg (IterationFour.Kinetic.block_one_le a i)
  have hq:= abs_sub_abs_le_abs_sub (f N i) (f N i + G.slopeConstant*L)
  rw [show f N i-(f N i+G.slopeConstant*L)=- (G.slopeConstant*L) by ring, abs_neg,abs_of_nonneg (mul_nonneg (G.slopeConstant_pos hg).le hu)] at hq
  change |f N i| ≤ (G.slopeConstant+1)*Clock.doubleLog a i
  linarith only [hq,hx,hL,priced a i,mul_le_mul_of_nonneg_left hL (G.slopeConstant_pos hg|>.le)]

include hg
lemma tangible (h : Held C f hg) (N q i : ℕ) (hi : i<N) :
    let P := leadingPlan C f N q
    |P.predict i - C.path.β N q i| ≤ weight C.path.levels (1/5) i := by
  intro P
  let a:= C.path.levels
  obtain ⟨w,u,b,hK⟩ := h.profile i N q hi
  obtain ⟨X,s,τ,H,r,hZ,hs⟩ := hK.income
  have he := Averaging.delta_bound hg H.projects
  let d:=delta (X.read s)
  have hW : (P.predict i)=(C.path.β N q (i+1))+f N i:=by simp [Plan.predict,hi.ne,P,leadingPlan,Plan.poly,hi]
  have hT: C.path.β N q i=P.predict i+d := hW.symm ▸ (congr_arg RG.Rep.beta hs).symm
  rw [hT]; simp only [sub_add_cancel_left,abs_neg]
  let t:=(a.budget i).threshold
  let g:=(a.clock.allowance i)
  have hu: Time.forecastE a i ≤ g:= by
    apply le_trans (b:=1*g) _ (by rw [one_mul])
    have hy:=Time.authorized G (a.params i)
    change Time.credit G (a.params i)*_ ≤ _
    apply mul_le_mul_of_nonneg_right (le_trans hy.1 (by norm_num))
    exact Real.rpow_nonneg (WardBin.stepG _ _|>.le) _
  calc
    _ ≤ (t^(2:ℕ))⁻¹ *(weight a (11/5) i) := by
       rw [show weight a (11/5) i=g from rfl]
       have hx: |d| ≤ g/(t^2):= (le_div_iff₀ (sq_pos_of_pos (a.budget i).threshold_pos)).2 ((mul_comm |d| _).trans_le (he.trans hu))
       exact hx.trans_eq (div_eq_inv_mul ..)
    _ ≤ B a i * weight a (11/5) i:=mul_le_mul_of_nonneg_right (threshold_receipt a i) (Currency.weight_pos a _ _).le
    _ = _ := by rw [beta_payment]; norm_num [a]

include ht
/-- σ = 11/5. **Not** claiming 3-η with η<1/2. -/
def postage : Purse := ⟨11/5,3,by norm_num,1,1/2,by norm_num,by norm_num,by norm_num,by norm_num⟩
def bench (a : Levels G) (i : ℕ) : Pocket:=⟨0,0,0,0,0,0,a.clock.forcedAllowance i,by norm_num⟩
-- pockets no Room: just Issued for orientation test.
lemma caped (h : Held C f hg) (N q i : ℕ) (hm : i<N) :
    Issued (leadingPlan C f N q) postage (bench C.path.levels) i (C.path.levels.clock.allowance i) (C.path.rep N q i):=by
  let a:= C.path.levels; let R:=C.path.rep N q i
  have he : C.path.Conv N q i:= ht.wilson.represents _ _ _ hm.le
  have hz:a.clock.allowance i= weight a (11/5) i:=rfl
  constructor
  · exact (Currency.weight_pos a i (11/5)).le
  · change _ ≤ 1 * weight a (11/5) i; rw [one_mul]; exact le_rfl
  · constructor
    · exact ⟨rfl,he.clip,he.vac⟩
    · exact he.vac ▸ he.good.labels
    · exact he.vac ▸ he.good.labels
    · intro w hv; change w∈ ([]:List _) at hv; simp at hv
    · rfl
    change |R.beta - R.beta|≤ _; rw [sub_self,abs_zero]; exact (postage.guard_pos a i).le
  change _ ≤ ((1:ℝ)+1)*weight a (11/5-2) i
  rw [show (11/5:ℝ)-2=1/5 by ring]; exact (tangible hg h N q i hm).trans (le_mul_of_one_le_left (Currency.weight_pos a i (1/5)).le (by norm_num))

structure Enjoys (C : Family G) (f : ℕ→ℕ→ℝ) (N q i : ℕ) : Prop where
    old : ∃ w δ γ, Stamped C N q i (f N i) (Time.forecastE C.path.levels i) w δ γ
    caps : Issued (leadingPlan C f N q) postage (bench C.path.levels) i (C.path.levels.clock.allowance i) (C.path.rep N q i)
    relative : let g := g C N q; let R := Series.root (direction (leadingPlan C f N q) i) 2
               |g i/g (i+1)-R.eval (g (i+1))| ≤ movement postage * g i ^(11/5:ℝ)

theorem exercised (hF : UVExtension.Oasis.Floral (hG:=hg) C) {before after}
    (hp : Clock.Register C.path.levels before after) : ∃ f,Installed C hg f ∧
    ∀ᶠ m:ℕ in atTop, ∀ N q, m<N → Enjoys C f N q m := by
  obtain ⟨F,H⟩:= baked hg hF
  let a:=C.path.levels; let P:=leadingPlan C F
  have he := instance_spend hg H hp
  have hv:=Financed.validPrediction hg ht he
  have hW:=Financed.ticket_income hg ht (P:=P) postage (by norm_num [postage]) he
  obtain ⟨M,hM⟩:= Filter.eventually_atTop.mp (g_small hg ht 1 zero_lt_one)
  refine ⟨F,H.ink,?_⟩
  filter_upwards [(Spending.pass_iff (Financed.eligible Set.univ) _).1 hv,hW,
    adjacent a hg 4 (by norm_num),eventually_ge_atTop M] with i hv hX he hw N q hm
  have hh:= caped hg ht H N q i hm
  have ht0 : g C N q (i+1) ≤ 1:= (hM _ (hw.trans i.le_succ) N q hm).le
  have hp:= hX N q (Set.mem_univ _) hm
  have hU:= radius (P N q) hg ht postage i hm (hv N q ⟨Set.mem_univ _,hm.le⟩) hh he ht0 hp.1
  refine ⟨H.profile _ _ _ hm,hh,?_⟩
  refine le_trans (hU.trans (add_le_add_right hp.2 _)) ?_
  change ratioConstant postage*weight a (11/5) i + weight a (11/5) i ≤ _
  calc
    _ = (ratioConstant postage+1)*weight a (11/5) i := by ring
    _ ≤ (ratioConstant postage+1)*((2:ℝ)^(11/5:ℝ)*g C N q i^(11/5:ℝ)) := mul_le_mul_of_nonneg_left
      ((g_weight ht hm.le _ (by norm_num)).1) (by linarith only [ratioConstant_nn postage])
    _ = _ := by unfold movement; dsimp only [postage]; ring

omit ht in
/-- TWO consecutive step sanity check near arbitrarily fine cutoffs,
    instantiated, E2^- test only. -/
theorem twice : ∃ (C : Family G) (J : Extraction.Order) (T : Table C.book)
        (F : Spec.Final C J T) (L : EveryPhase.Almanac F), C.Makes ∧
        C.path.levels.clock.kernel.penalty=1 ∧ UVExtension.Oasis.Floral (hG:=hg) C ∧ EveryPhase.Completed F L ∧
        ∃ f, Installed C hg f ∧ ∀ᶠ m : ℕ in atTop,∀ q, Enjoys C f (m+2) q m ∧ Enjoys C f (m+2) q (m+1):=by
  obtain ⟨C,J,T,F,L,hM,hc,hp,hF,hq,ha,hV,hL⟩:= IterationFour.Clock.beginning (fun _ _ _ _=> 0) (fun _ _ _ _ _=> 0) hg zero_lt_one
  obtain ⟨f,hG,ht⟩:= exercised (C:=C) hg hM hF hq.1
  refine ⟨C,J,T,F,L,hM,hp,hF,hL,f,hG,?_⟩
  filter_upwards [ht, (Filter.tendsto_add_atTop_nat 1).eventually ht] with i hi he q
  exact ⟨hi _ _ (by omega),he _ _ (by omega)⟩
end YM.IterationFour.Vacuum.HistoryTest
