import YM.RG01.Vacuum.Beacon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy

/-!
# On the *same* Song catalogue

Move the arity abstraction to the actual pre-reset local output. `Collection.Source`
here contains log and occurrence readings (no claim of physical/source-field
coefficients despite that name). Take the Presentation BEFORE re-expression: path,
scalar, extra masked alpha receipt, posted labels and their forced partners
unchanged. Hence even when using the analytic mode theorem on a real log family,
the residual/keep use the actual masks and Anchored budget. See ResetTrays for the
later reclosure costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a β τ i : ℝ} {k j n : ℕ}
    {χ : Chi} (p : BudgetPoint) (H : Cash W s μ L Q o α T I) {J : Cash W s μ L Q o α T R}
    (X : Match.Alliance H J 1 0) (γ : ℝ)

/-- Apply field-independent weights to integrated regular letters before orbit average.
When `comparePart` is false, omit the explicit `Songbook` counterterm channels.
Hard untouched, even for the partial catalogue. -/
def weigh (χ : Chi) (ρ : J.fragrances → ℝ) (comparePart : Bool) (γ : ℝ) : Collection.Source G c where
  logRead := choir (fun t : Magazine H =>
    (Sum.elim (fun u => ρ (X.furrow u)) (fun _ : Songbook c => if comparePart then (1:ℝ) else 0) t) • opus H X χ γ t) ∘ pennant H
  hardRead := (plusone H X χ γ).hardRead

/-- Log catalogue weight at a *posted* address. -/
def weightAt (ρ : J.fragrances → ℝ) (comparePart : Bool) (i : ℕ) : ℝ :=
  Sum.elim (fun u => ρ (X.furrow u)) (fun _ : Songbook c => if comparePart then (1:ℝ) else 0)
    (pennant H i).2

lemma weightedReading (ρ : J.fragrances → ℝ) (b : Bool) (i : ℕ) :
    (weigh H X χ ρ b γ).logRead i = weightAt H X ρ b i • (plusone H X χ γ).logRead i := by
  funext U
  dsimp [weigh, plusone, choir, weightAt]; ring

lemma forcedFamily (ρ : J.fragrances → ℝ) (b : Bool) :
    let x := posting p H
    let u := x.read (weigh H X χ ρ b γ)
    p.threshold=Pressure.temp s → u.ForcedFamily p := by
  intro x u hp
  apply qualified p H X χ _ _ hp

lemma catalogueMoves (ρ : J.fragrances → ℝ) (gain : Bool) (u : Signed) (b : Site c) :
    Nonempty (((posting p H).read (weigh H X χ ρ gain γ)).Moves u b) := by
  obtain ⟨π⟩ := J.laws.intake.cap.labels.moves u (S.ratio.embed b)
  obtain ⟨η,hη⟩ := settles H X χ u b π
  let g (t : Magazine H) := (Sum.elim (fun i=>ρ (X.furrow i)) (fun _ : Songbook c=> if gain then (1:ℝ) else 0) t) • opus H X χ γ t
  let e := whirl (ι:=Magazine H) u b; let a:=pennant H; let k:=badge H
  have hk i : k (congo k η i)=_ := perch k η i; have ha i : a (congo a e i)=_ := perch a e i
  let h x:= spirit (scaleT p H) g u b x
  refine ⟨⟨congo a e,congo k η,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩⟩
  · change (revolve _ (a (congo a e i))).site=_; rw [ha]; exact (h _).1
  · change (revolve _ (a (congo a e i))).support=_; rw [ha]; exact (h _).2.1
  · change (reserve H (k (congo k η i))).support=_; rw [hk]; exact (hη _).1
  · change (reserve H (k (congo k η i))).inventory=_; rw [hk]; exact (hη _).2.1
  · change (reserve H (k (congo k η i))).extraTest V ↔ _; rw [hk]; exact ((hη (k i)).2.2 V).1
  · change choir g (a (congo a e i)) V=_; rw [ha]; exact congr_fun (h (a i)).2.2 V
  change fuse H X χ (k (congo k η i)) V=_; rw [hk]; exact ((hη (k i)).2.2 V).2

variable (N : Captain J j C' d v Y A b r B q k χ) (hp : p.threshold=Pressure.temp s) (hP : p.order ≤ j)
    (hB : p.B=radiusB s) (n : ℕ) (hn : p.power ≤ n) (w : ℝ) (ρ m : J.fragrances → ℝ)
    (hq : ∀ z, |ρ z| ≤ m z)
include N hp hP hB hn hq
/-- Transport an absolute log moment to regular Real-family EBound with exact supports.
No `Healthy` restriction is imposed on a forced partner. -/
lemma logPrice (ha : preExponent p ≤ a)
    (hM : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) (fun z=>m z*N.markΦ z n) a w) :
    ∃ u : ℕ → ℝ, Quotes.early p (posting p H).reg u (turnFee p*w) ∧
      ∀ l, p.Regular ((posting p H).reg l).support ((weigh H X χ ρ false γ).logRead l) ∧
        p.supBounds ((posting p H).reg l).site ((posting p H).reg l).support ((weigh H X χ ρ false γ).logRead l) (u l) := by
  let g (t : Magazine H) := (Sum.elim (fun i=>ρ (X.furrow i)) (fun _ : Songbook c=> (0:ℝ)) t) • opus H X χ γ t
  let q (i:H.fragrances) := m (X.furrow i) * N.markΦ (X.furrow i) n
  let f : Magazine H → ℝ := Sum.elim q (fun _=>0)
  have hg : (weigh H X χ ρ false γ).logRead = choir g ∘ pennant H := rfl
  rw [hg]
  have ht (z : Magazine H) : p.Regular (scaleT p H z).support (g z) ∧ p.supBounds (scaleT p H z).site (scaleT p H z).support (g z) (f z) := by
    rcases z with z|z
    · have he:= pocketScore p H X χ N hp hP n hn z
      exact ⟨CouplingShape.reg_scale _ he.1, sup_le (CouplingShape.sup_scale _ he.2)
        (mul_le_mul_of_nonneg_right (hq (X.furrow z)) he.2.1)⟩
    change _ ∧ p.supBounds _ _ ((0:ℝ) • _) 0
    simp only [g, Sum.elim_inr, zero_smul]
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(scaleT p H (.inr z)).support) (o:=(scaleT p H (.inr z)).site) 0)⟩
  have hE : Quotes.early p (scaleT p H) f w := by
    rw [← add_zero w]
    intro y
    apply Cost.sum (f:=fun l => if (scaleT p H l).site=y then f l*Real.exp (preExponent p * coverNumber p.B (scaleT p H l).support) else 0)
      (A:=w)
    · have hv:=budget_pull X.furrow X.furrow.injective (hM y)
      refine budget_mono hv (fun z=> ?_) fun z=>?_
      · split
        · exact mul_nonneg (ht (.inl z)).2.1 (Real.exp_pos _).le
        exact le_rfl
      dsimp only; split
      next hz =>
        have hb' : y∈Captain.reachability (X.furrow z) := show y∈perf J _ from reconnects H X z ▸ (show y∈perf H z from hz ▸ (locate H z).anchor)
        rw [if_pos hb',show (scaleT p H (Sum.inl z)).support= _ from reconnects H X z,hB]
        apply mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (ht (.inl z)).2.1
      exact hv.1 z
    simp [SumBudget, f]
  obtain ⟨hc,hh⟩:=spiral _ _ f (fun i=>(ht i).1) (fun i=>(ht i).2) hE
  exact ⟨_,fun i=> Cost.equiv (pennant H) (hh i),fun i=> hc (pennant H i)⟩

variable (ha : preExponent p ≤ a) (hd : 1 ≤ grow G L s)
    (hHeavy : Heavy N.conduit)
    (ht : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hc : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)
variable {m' : ℕ} (hj : Cash.Renewed m' a β τ J)
include ha hd hHeavy ht hs hc hj
omit hq
/-- Weighting of the real vacuum-log letters in a disc share of the beacon.
In particular this includes the arbitrary-order high-arity filter even at the
actual occupation on the UV constructor. The hard budget is unchanged. -/
theorem beaconLocal (E : ℝ) (hE : 0 ≤ E)
    (hρ : ∀ z, |ρ z| ≤ E * beacon J z) :
    Collection.Local (posting p H) p (weigh H X χ ρ false γ)
      (turnFee p * (E * (collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹))))
      (Cash.armK Q L μ s 0 m') := by
  have h:= beaconMoment N hd hHeavy n ht hs hc
  have hm : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) (fun z=> (E*beacon J z)*N.markΦ z n) a (E * (collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
    have hh := hit_scale hE h
    simpa only [mul_assoc] using! hh
  obtain ⟨u,hu,hU⟩:= logPrice p H X γ N hp hP hB n hn _ ρ _ hρ ha hm
  obtain ⟨f,hf,hF⟩:= chargesOut p H X χ hj hB (show p.supportExponent+1≤a by unfold preExponent at ha; linarith)
  exact ⟨fun i=> (hU i).1, forcedFamily p H X γ ρ false hp,
    catalogueMoves p H X γ ρ false,
    ⟨u,fun i=>(hU i).2,hu⟩,
    f,hf,hF⟩

abbrev arityFilter {H : Cash W s μ L Q o α T I} (m : ℕ) : H.fragrances → ℝ := fun z=> if m ≤ degree H z then 1 else 0
abbrev arityKeep {H : Cash W s μ L Q o α T I} (m : ℕ) : H.fragrances → ℝ := fun z=> if m ≤ degree H z then 0 else 1
local notation "D" => grow G L s

theorem arityLocal (M : ℕ) :
    Collection.Local (posting p H) p (weigh H X χ (arityFilter M) false γ)
      (turnFee p * ((D^M)⁻¹ * (collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹))))
      (Cash.armK Q L μ s 0 m') := by
  have he:0 < D:=zero_lt_one.trans_le hd
  apply beaconLocal p H X γ N hp hP hB n hn _ ha hd hHeavy ht hs hc hj _ (by positivity)
  intro z
  unfold arityFilter; split
  next h=>
    rw [abs_one, mul_comm, ← div_eq_mul_inv]
    apply (one_le_div (pow_pos he _)).mpr
    exact (pow_le_pow_right₀ hd h).trans (beacon_ge hd z)
  rw [abs_zero]
  apply mul_nonneg (by positivity) ((pow_nonneg he.le _).trans (beacon_ge hd z))

omit N hp hP ha hHeavy ht hd hB hn hs hc hj
/-- Arbitrary thinning (or attenuation; useful with zero extension tags)
on an already purchased Local. ForcedFamily still on actual eligibility. -/
lemma attenuate (E w : ℝ)
    (hE : Collection.Local (posting p H) p (plusone H X χ γ) E w)
    (hρ : ∀ z, |ρ z| ≤ 1) (c' : Bool) :
    Collection.Local (posting p H) p (weigh H X χ ρ c' γ) E w := by
  obtain ⟨h,hF,hM,⟨u,hu,hU⟩,hk⟩:=hE
  have hw i:= weightedReading H X γ ρ c' i (χ:=χ)
  have hQ i : |weightAt H X ρ c' i| ≤ 1 := by
    unfold weightAt
    cases (pennant H i).2 with
    | inl z=> exact hρ _
    | inr z=>
      cases c' <;> norm_num
  refine ⟨fun i=> hw i ▸ ?_,?_ ,catalogueMoves p H X γ ρ c', ⟨u,fun i=> hw i ▸ ?_,hU⟩,hk⟩
  · exact CouplingShape.reg_scale _ (h i)
  · exact ⟨hF.sym,hF.symtest,hF.meas,hF.meas_test,hF.reads,hF.reads_test,hF.permit⟩  -- order?
  apply sup_le (CouplingShape.sup_scale _ (hu i)) (mul_le_of_le_one_left (hu i).1 (hQ i))

/-- Exact multiplicative corrections to the physical density from the log share.
NOT taking a Taylor norm of this correction itself. -/
def exponentialShare (X : Listing G c) (p : BudgetPoint) (v : Collection.Source G c) (U : Config G c) :=
  Real.exp (-(X.read v).additive p U)

/-- Split earlyValue on ONE Listing; requires no analytic continuation of
indicators and no global summability hypotheses beyond the two EBounds on
these same addresses. -/
theorem earlySplit {X : Listing G c} {p : BudgetPoint} {s s₁ s₂ : Collection.Source G c}
    (h : s.logRead = s₁.logRead+s₂.logRead) (hr : s.hardRead = s₁.hardRead)
    (R : PathData G) (t : Clip) (β τ γ : ℝ)
    {a b : ℝ} (h₁ : (X.read s₁).EBound p a) (h₂ : (X.read s₂).EBound p b) :
    earlyValue X R t p s β τ γ = earlyValue X R t p s₁ β τ γ * exponentialShare X p s₂ := by
  funext U
  have he (s : Collection.Source G c) {a} (h : (X.read s).EBound p a):
      Summable fun i=>masked p.threshold (X.reg i).support (s.logRead i) U := by
    obtain ⟨d,hd,hD⟩:= Activities.E_total h
    apply Dominated.summable (F:=fun i (V:Config G c)=>masked p.threshold (X.reg i).support (s.logRead i) V) _ U
    refine ⟨d,hd,fun i V=>?_⟩
    dsimp only
    by_cases ha:Healthy p.threshold (X.reg i).support V
    · rw [masked_eq _ _ _ _ ha]; exact (hD i).2 V ha [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ ha,norm_zero]; exact (hD i).1
  have hA : (X.read s).additive p U=(X.read s₁).additive p U+(X.read s₂).additive p U := by
    unfold Activities.additive Activities.regularOccurrence
    dsimp only [Listing.read]; rw [h, ← Summable.tsum_add (he s₁ h₁) (he s₂ h₂)]
    apply tsum_congr; intro i
    by_cases hU:Healthy p.threshold (X.reg i).support U <;> simp [hU]
  have hG : (X.read s).gas p U=(X.read s₁).gas p U := by
    unfold Activities.gas Activities.gasOccurrence; dsimp [Activities.admissible,Listing.read]; rw [hr]
    apply tsum_congr; intro i; split <;> simp [*]
  dsimp only [Pi.mul_apply, earlyValue, Collection.frozen, RG.Rep.eval, RG.Rep.exponent, exponentialShare]
  rw [hA,hG, show τ*(Fintype.card (Site c) : ℝ)-R.inChannels t p β U-(_+_) = τ*(Fintype.card (Site c):ℝ)-R.inChannels t p β U-(X.read s₁).additive p U+(-(X.read s₂).additive p U) by ring, Real.exp_add]
  ring

/-- Local K is a one-exponent-stronger KBound. -/
lemma localK {X : Listing G c} {p : BudgetPoint} {u : Collection.Source G c} {a b : ℝ}
    (h : Collection.Local X p u a b) : (X.read u).KBound p b := by
  obtain ⟨k,hk,hF⟩:=h.expensive
  refine ⟨k,hk, fun x=> budget_mono (hF x) (fun i=> ?_) (fun i=> ?_)⟩
  · split
    next => exact mul_nonneg (Real.exp_pos _).le (hk i).1
    exact le_rfl
  dsimp only [Listing.read]; split
  next =>
    rw [BudgetPoint.mass,mul_comm (k i)];
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one' ℝ)) (Nat.cast_nonneg _))) (hk i).1
  exact le_rfl

lemma weigh_split (n : ℕ) :
    (plusone H X χ γ).logRead = (weigh H X χ (arityKeep n) true γ).logRead+(weigh H X χ (arityFilter n) false γ).logRead := by
  funext i
  simp only [Pi.add_apply, weightedReading, ← add_smul]
  rw [show weightAt H X (arityKeep n) true i + weightAt H X (arityFilter n) false i = 1 by
        unfold weightAt
        cases (pennant H i).2 <;> simp [arityKeep, arityFilter]; split <;> simp_all, one_smul]

include N hp hP hB hn hj ht hs hc ha hd hHeavy
open Geo
/-- Pointwise reassembly on the actual pre-reset output of the vacuum E6
component arithmetic (α is written γ here). No field-independent vacuum
scalar is lost and no branch indicator on a gas or path or the regular log is
dropped. Tasks 2 and 3 can work on the Keep, and shouldn't infer this result
for other catalogues without a support, norm and incidence adaptor. -/
theorem vacuumPurchase (O : Tree.Forest S.ratio)
    {σ C Λ : ℝ} (hx : T.down.Bounds T.low σ C Λ)
    (ht' : WilsonStartup.Decent T.low p) (hw : preExponent p / p.B ≤ σ/2) (M : ℕ) :
    let t := weighty J χ O
    let keep := weigh H X χ (arityKeep M) true γ
    let err := weigh H X χ (arityFilter M) false γ
    let A := posting p H
    let cost := turnFee p*((collars G i s j n*(salary Q L μ B s j k*(1-1/2)⁻¹)) + octaveNeed G p T.low σ C Λ R.beta γ)
    let tar := turnFee p * ((D^M)⁻¹ * (collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹)))
    let w := Cash.armK Q L μ s 0 m'
    Collection.Local A p keep cost w ∧ Collection.Local A p err tar w ∧
      S.push R.beta R.eval = earlyValue A T.down T.low p keep R.beta t γ * exponentialShare A p err := by
  intro t keep err A C t' w
  have he: Collection.Local A p (plusone H X χ γ) C w:= Song.loaded p H X χ γ N hp hP hB hx hj ha ht hn ht' hw
  have hh : Collection.Local A p keep C w:= attenuate p H X γ _ C w he (by
    intro z; unfold arityKeep; split <;> norm_num) true
  have ht': Collection.Local A p err t' w := arityLocal p H X γ N hp hP hB n hn ha hd hHeavy ht hs hc hj M
  refine ⟨hh,ht',?_⟩
  rw [← earlySplit (s:=plusone H X χ γ) (s₁:=keep) (s₂:=err) (weigh_split ..) rfl (T.down) T.low _ _ _ hh.unweighted ht'.unweighted]
  exact funext fun V => (Song.forward p H X χ γ N O hp hP hx hj V).symm

end YM.RG01.Vacuum
