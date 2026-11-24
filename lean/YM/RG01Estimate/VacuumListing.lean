import YM.RG01Estimate.CensusTail
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Rest
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-!
# Filtering a vacuum pre-reset representation *as a representation*

Retain the genealogy on the Beam marquee (needed, for example, when charging
inheritance to real incoming E). Split only the regular sum; the hard labels
including every flag and exclusion test are held common. No projection and no
comparison to a CHANGED mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.VacuumListing

open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open PhysicalNext PhysicalNext.Repeat Height Beam Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i K γ : ℝ} {k j n ℓ : ℕ}
    (H : Cash W s μ L Q o α T I) (p : BudgetPoint) {J : Cash W s μ L Q o α T R} (χ : Chi)
    (X : Alliance H J 1 0)
    (N : Captain J j C' d v Y A b r B q k χ)
    (hP : p.threshold=Pressure.temp s) (hj : p.order ≤ j) (hw : p.power ≤ n)
    (ht : p.B=radiusB s) (hv : preExponent p ≤ a)

include hP hj hw
lemma pocket_dash (z : H.fragrances) :
    p.Regular (dashboard H z).support (Song.sequence H X χ z) ∧
    p.supBounds (dashboard H z).site (dashboard H z).support (Song.sequence H X χ z) (N.markΦ (X.furrow z) n) := by
  have hk := N.gloryBudget (X.furrow z) p hP hj
  have hz : (dashboard H z).support=perf J (X.furrow z):= (see H z).trans (reconnects H X z)
  rw [hz]; refine ⟨CouplingShape.reg_scale _ hk.2.1,?_⟩
  have hh:= CouplingShape.sup_scale (-1) (hk.2.2 n hw (dashboard H z).site (show _ ∈ perf J (X.furrow z) from hz ▸ (dashboard H z).anchor))
  rw [abs_neg,abs_one,one_mul] at hh; exact hh

include N ht hv
omit N hj hw hP in
lemma dash_hit (Z : J.fragrances → ℝ) (h : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) Z a K) :
    Quotes.early p (dashboard H) (Z ∘ X.furrow) K := by
  intro x
  have he := Cost.equiv X.furrow (h x)
  refine budget_mono he (fun u=>?_) fun u=>?_
  · dsimp only [comp_apply]; split
    next hu=>
      apply mul_nonneg _ (Real.exp_pos _).le
      have hk := he.1 u; dsimp only at hk
      rw [if_pos (show x∈Captain.reachability _ from hu ▸ (((see H u).trans (reconnects H X _)) ▸ (dashboard H u).anchor : (dashboard H u).site ∈ perf J (X.furrow u)))] at hk
      exact nonneg_of_mul_nonneg_left hk (Real.exp_pos _)
    exact le_rfl
  dsimp only [comp_apply]; split
  next hu=>
    rw [see,reconnects H X u,ht]
    have hz : x∈Captain.reachability (X.furrow u):= hu ▸ (((see H u).trans (reconnects H X _)) ▸ (dashboard H u).anchor : (dashboard H u).site ∈ perf J (X.furrow u))
    have hk:= he.1 u; dsimp only at hk
    rw [if_pos hz] at hk
    rw [if_pos hz]
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _)))
      (nonneg_of_mul_nonneg_left hk (Real.exp_pos _))
  exact he.1 u

variable (Z : J.fragrances → Prop) (hf : Cash.Renewed ℓ a δ e J)
include hf

omit N hj hw in
lemma to_local (f : Magazine H→ Config G c→ℝ) (g : Magazine H → ℝ)
    (hb : Quotes.early p (Beam.contents H p) g K)
    (hp : ∀ i, p.Regular (contents H p i).support (f i) ∧ p.supBounds (contents H p i).site (contents H p i).support (f i) (g i)) :
    Collection.Local (Beam.marquee H p) p ⟨choir f ∘ pennant H, (plusone H X χ 0).hardRead⟩
      (turnFee p*K) (Cash.armK Q L μ s 0 ℓ) := by
  obtain ⟨h,hQ⟩:= spiral _ _ _ (fun i=> (hp i).1) (fun i=> (hp i).2) hb
  exact ⟨fun i=>(h (pennant H i)).1, qualified p H X χ _ _ hP,
    fun s t=> Beam.moves H p χ X s t _,⟨_,fun i=> (h (pennant H i)).2, fun o=> Cost.equiv (pennant H) (hQ o)⟩,
    chargesOut p H X χ hf ht (show p.supportExponent+1 ≤ a by unfold preExponent at hv; linarith)⟩

lemma filtered (h : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) (fun t=> if Z t then N.markΦ t n else 0) a K) :
    Collection.Local (Beam.marquee H p) p (serve H X χ (Z ∘ X.furrow))
      (turnFee p*K) (Cash.armK Q L μ s 0 ℓ) := by
  let A z:=if Z z then N.markΦ z n else 0
  let g := Sum.elim (A ∘ X.furrow) (fun _ : Songbook c => (0:ℝ))
  apply to_local H p χ X hP ht hv hf (skilled H X χ (Z ∘ X.furrow)) g
  · intro x
    nth_rw 1 [← add_zero K]
    apply Cost.sum (dash_hit H p X ht hv A h x)
    simp only [g,contents,Sum.elim, zero_mul, ite_self]
    simp only [SumBudget, le_refl, implies_true, summable_zero, tsum_zero, and_self]
  rintro (z|z)
  · dsimp only [g,A,contents,comp_apply,skilled,Sum.elim_inl]; split
    next => exact pocket_dash H p χ X N hP hj hw z
    next =>
      refine ⟨CouplingShape.reg_const _,?_⟩
      simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(dashboard H z).support) (o:=(dashboard H z).site) 0)
  dsimp only [g,contents,skilled,Sum.elim_inr]
  refine ⟨CouplingShape.reg_const _,?_⟩
  simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(strings T.down p z).support) (o:=(strings T.down p z).site) 0)

lemma full (lat : Armada Q L μ a s i B j k) (γ : ℝ) {σ C Λ : ℝ}
    (hx : T.down.Bounds T.low σ C Λ) (hd : WilsonStartup.Decent T.low p) (hp : preExponent p / p.B ≤ σ/2) :
    Collection.Local (Beam.marquee H p) p (Song.plusone H X χ γ)
      (turnFee p*((collars G i s j n*(salary Q L μ B s j k*(1-1/2)⁻¹)) + octaveNeed G p T.low σ C Λ R.beta γ)) (Cash.armK Q L μ s 0 ℓ) := by
  have hg:= lat.applies N n 0; simp only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] at hg
  obtain ⟨f,hF,hQ⟩:= stanzaReady (n:=c) T.down T.low p R.beta γ hx hd hp
  refine to_local H p χ X hP ht hv hf _ (Sum.elim ((fun t=> N.markΦ t n) ∘ X.furrow) f) ?_ ?_
  · intro x; exact Cost.sum (dash_hit H p X ht hv _ hg x) (hF x)
  intro z; rcases z with z|z; exact pocket_dash H p χ X N hP hj hw z
  exact hQ z

omit N hf hj hP hw ht hv
lemma unfiltered (Z : H.fragrances → Prop) {w : ℝ}
    (hr : Collection.Local (Beam.marquee H p) p (Song.plusone H X χ γ) K w) :
    Collection.Local (Beam.marquee H p) p (sleeping H X χ Z γ) K w := by
  let f := sleeping H X χ Z γ
  have h (n) := (bolted H X χ Z γ n).2
  refine ⟨fun n=>?_, ⟨hr.family.sym,hr.family.symtest,hr.family.meas,hr.family.meas_test,hr.family.reads,hr.family.reads_test,hr.family.permit⟩,
    fun s t=> Beam.moves H p χ X s t _,?_,hr.expensive⟩
  · rw [h]; split
    next => exact CouplingShape.reg_const _
    next => exact hr.smooth _
  obtain ⟨u,hu,hh⟩:= hr.cheap
  refine ⟨u,fun i=>?_,hh⟩; rw [h]; split
  next =>
    apply VerifiedReset.sup_le (by exact CouplingShape.sup_const 0)
    rw [abs_zero]; exact (hu _).1
  next => exact hu i

section generic
variable {A : Listing G c} {V P U : Collection.Source G c}

/-- Useful even when only keeping strong budgets. -/
lemma proper_caps {τ ε : ℝ} (h : Collection.Local A p V τ ε) : (A.read V).EBound p τ ∧ (A.read V).KBound p ε := by
  refine ⟨h.unweighted,?_⟩; obtain ⟨k,hk,hK⟩:= h.expensive
  exact ⟨k,hk,Progress.DirectedRecipe.Payments.drop_reserve p _ (fun i=> (hk i).1) hK⟩

lemma relax {τ ε γ ζ : ℝ} (h : Collection.Local A p V τ ε) (hr : τ ≤ γ) (he : ε ≤ ζ) : Collection.Local A p V γ ζ := by
  obtain ⟨u,hU,hu⟩:=h.cheap; obtain ⟨v,hV,hv⟩:=h.expensive
  exact ⟨h.smooth,h.family,h.transforms,⟨u,hU,fun i=>budget_loosen (hu i) hr⟩,⟨v,hV,fun i=>budget_loosen (hv i) he⟩⟩

/-- V = P plus an error U *in the log*. U's forced component, if present,
is a separate account; the hypothesis is P retains V's hard data. -/
theorem reassemble {w w' a a' : ℝ} {γ : ℝ}
    (h : Collection.Local A p P w a) (ht : Collection.Local A p U w' a') (he : V.logRead=P.logRead+U.logRead)
    (hk : V.hardRead=P.hardRead) (β τ : ℝ) (R : PathData G) (c' : Clip) (Y) :
    earlyValue A R c' p V β τ γ Y = earlyValue A R c' p P β τ γ Y * Real.exp (-(A.read U).additive p Y) := by
  have hY i : (A.read V).regularOccurrence p i Y=(A.read P).regularOccurrence p i Y+(A.read U).regularOccurrence p i Y := by
    unfold Activities.regularOccurrence; unfold Listing.read; dsimp only
    rw [he]; by_cases hx:Healthy p.threshold (A.reg i).support Y
    · simp only [hx,masked_eq p.threshold (A.reg i).support,Pi.add_apply]
    simp only [hx,not_false_eq_true,masked_ne p.threshold (A.reg i).support,add_zero]
  have hv:(A.read V).additive p Y=(A.read P).additive p Y+(A.read U).additive p Y := by
    unfold Activities.additive; simp_rw [hY]; exact Summable.tsum_add (Roof.Embrasure.series _ _ h _) (Roof.Embrasure.series _ _ ht _)
  have hG:(A.read V).gas p Y=(A.read P).gas p Y := by
    apply tsum_congr; intro i
    unfold Activities.gasOccurrence Activities.admissible; simp only [Listing.read,hk]
  unfold earlyValue Rep.eval Rep.exponent; simp only [Collection.frozen]
  rw [hG,hv,← sub_sub,sub_eq_add_neg (_-_ - _), Real.exp_add]; ring
end generic

lemma filter_identity (Z : J.fragrances → Prop) (γ : ℝ) :
    (Song.plusone H X χ γ).logRead = (sleeping H X χ (Z ∘ X.furrow) γ).logRead + (serve H X χ (Z ∘ X.furrow)).logRead := by
  ext i U; obtain ⟨h₁,h₂⟩:= bolted H X χ (Z ∘ X.furrow) γ i
  simp only [Pi.add_apply]; rw [h₁,h₂]; split <;> simp

-- already true definitionally that hardRead is unchanged in both.
end YM.RG01Estimate.VacuumListing
