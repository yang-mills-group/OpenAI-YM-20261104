import YM.RGComparison01.Beacon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir
import YM.Next.RANK.Patchable

/-!
# Keep exceptional unmarked-log bill in actual coordinates

These theorems split the actual representation, not a Fourier or tensor
approximation. Select count/seed/depth cuts (or any funded selection) and
long paths. Keep original receipt, coupling, and path channels and
**the original forced gas**. The small part is additive in the exponent;
its `Ebound`/`Budget` is not asserted to be a norm of the density, nor
that its affine projections are zero. This cut is *before* resetting.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open PhysicalNext PhysicalNext.Repeat Song
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

namespace LogSplit
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ}
    {k j n ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R}
variable (p : BudgetPoint) (X : Match.Alliance H J 1 0) (Sel : J.fragrances → Prop)
    (N : Captain J j C' d v Y A b r B q k χ)
local notation "gZ" => Height.grow G L s

theorem refund {price : ℝ} (hp : p.threshold = Pressure.temp s) (hd : p.B = radiusB s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hr : preExponent p ≤ a)
    (hQ : Ac.Hit Captain.reachability (radiusB s) (fun z => if Sel z then N.markΦ z n else 0) a price) :
    Meadow.Budget p (locate H) (fun i => if Sel (X.furrow i) then Song.sequence H X χ i else 0) price := by
  let V i := if Sel (X.furrow i) then Song.sequence H X χ i else 0
  let f i := if Sel (X.furrow i) then N.markΦ (X.furrow i) n else 0
  have hV i : p.Regular (locate H i).support (V i) ∧
      p.supBounds (locate H i).site (locate H i).support (V i) (f i) := by
    unfold V f; split
    next _ => exact pocketScore p H X χ N hp hj n hn i
    next => exact ⟨CouplingShape.reg_const _, sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  refine ⟨f, fun x => ?_, hV⟩
  have hv := budget_pull X.furrow X.furrow.injective (hQ x)
  refine budget_mono hv (fun z => ?_) (fun z => ?_)
  · split
    next => exact mul_nonneg ((hV z).2.1) (Real.exp_nonneg _)
    next => exact le_rfl
  dsimp only
  have he : (locate H z).support = Captain.reachability (X.furrow z) := reconnects H X z
  split
  next hx =>
    rw [if_pos (show x ∈ Captain.reachability (X.furrow z) from he ▸ (hx ▸ (locate H z).anchor)),he, hd]
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)))
      ((hV z).2.1)
  next => exact hv.1 _

/-- Internal-log mask on *addresses*, not field arguments. -/
def cut (k : ℕ) (i : Magazine H) : Prop :=
  i.elim (fun z => Sel (X.furrow z)) (fun i => k ≤ Meadow.arc T.down i)

def cutOpus (γ : ℝ) (χ : Chi) (k : ℕ) (i : Magazine H) :=
  if cut X Sel k i then opus H X χ γ i else 0

theorem combined {price σ C Λ : ℝ} (γ : ℝ) (K : ℕ)
    (hp : p.threshold = Pressure.temp s) (hd : p.B = radiusB s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hr : preExponent p ≤ a)
    (hQ : Ac.Hit Captain.reachability (radiusB s) (fun z => if Sel z then N.markΦ z n else 0) a price)
    (hbound : T.down.Bounds T.low σ C Λ) (hdec : WilsonStartup.Decent T.low p)
    (he : preExponent p / p.B ≤ σ/4) :
    Meadow.Budget p (scaleT p H) (cutOpus X Sel γ χ K)
      (price + Real.exp (-(σ/4)*K)*octaveNeed G p T.low σ C Λ R.beta γ) := by
  obtain ⟨f,hF,hV⟩ := refund p X Sel N hp hd hj hn hr hQ
  obtain ⟨g,hg,h⟩ := Meadow.lent (c:=c) p T.down T.low R.beta γ hbound hdec he
  let w t := if K ≤ Meadow.arc T.down t then g t else 0
  refine ⟨Sum.elim f w, fun i => ?_, ?_⟩
  · have hz := Meadow.arch_tail (strings T.down p) p _ hg
      (by have hw := hbound.width; positivity) (fun i => (h i).2.1) (k:=K) i
    exact Cost.sum (hF i) hz
  intro i; rcases i with i|i
  · change p.Regular (locate H i).support _ ∧ p.supBounds _ (locate H i).support _ _
    unfold cutOpus cut
    by_cases he : Sel (X.furrow i)
    · simpa only [Sum.elim_inl, he, ↓reduceIte, opus] using! hV i
    simpa only [Sum.elim_inl, he, ↓reduceIte] using! hV i
  have he : (p.Regular (scaleT p H (.inr i)).support (cutOpus X Sel γ χ K (.inr i)) ∧
      p.supBounds (scaleT p H (.inr i)).site (scaleT p H (.inr i)).support (cutOpus X Sel γ χ K (.inr i)) (w i)) := by
    unfold cutOpus w cut
    simp only [Sum.elim_inr]
    split_ifs with he
    · exact h i
    exact ⟨CouplingShape.reg_const _, sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  exact he

def selected (X : Match.Alliance H J 1 0) (Sel : J.fragrances → Prop) (χ : Chi) (γ : ℝ) (K : ℕ) :
    Collection.Source G c :=
  { (plusone H X χ γ) with logRead := choir (cutOpus X Sel γ χ K) ∘ Song.pennant H }

theorem selected_budget {price σ C Λ : ℝ} (γ : ℝ) (K : ℕ)
    (hp : p.threshold = Pressure.temp s) (hd : p.B = radiusB s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hr : preExponent p ≤ a)
    (hQ : Ac.Hit Captain.reachability (radiusB s) (fun z => if Sel z then N.markΦ z n else 0) a price)
    (hbound : T.down.Bounds T.low σ C Λ) (hdec : WilsonStartup.Decent T.low p)
    (he : preExponent p / p.B ≤ σ/4) :
    Meadow.Budget p (posting p H).reg (selected X Sel χ γ K).logRead
      (turnFee p * (price + Real.exp (-(σ/4)*K)*octaveNeed G p T.low σ C Λ R.beta γ)) := by
  obtain ⟨g,hg,h⟩ := combined p X Sel N γ K hp hd hj hn hr hQ hbound hdec he
  obtain ⟨hv,hV⟩ := Song.spiral _ _ _ (fun i => (h i).1) (fun i => (h i).2) hg
  exact ⟨_, fun i => Cost.equiv (Song.pennant H) (hV i), fun i => hv (Song.pennant H i)⟩

lemma unweighted {A : Listing G c} {t : Collection.Source G c} {price : ℝ}
    (h : Meadow.Budget p A.reg t.logRead price) : (A.read t).EBound p price := by
  obtain ⟨g,hg,h⟩ := h
  exact ⟨g,fun i => (h i).2, Quotes.segment _ (fun i => (h i).2.1) hg⟩

-- reset explicit types
lemma selector (χ : Chi) (γ : ℝ) (K : ℕ) (i : ℕ) :
    (selected X Sel χ γ K).logRead i =
      if cut X Sel K (Song.pennant H i).2 then (plusone H X χ γ).logRead i else 0 := by
  let y := Song.pennant H i
  by_cases he : cut X Sel K y.2
  · rw [if_pos he]
    change Rim c • (cutOpus X Sel γ χ K y.2 ∘ y.1.view) = _
    rw [cutOpus, if_pos he]; rfl
  rw [if_neg he]
  change Rim c • (cutOpus X Sel γ χ K y.2 ∘ y.1.view) = _
  rw [cutOpus, if_neg he]; ext; simp

def kept (X : Match.Alliance H J 1 0) (Sel : J.fragrances → Prop) (χ : Chi) (γ : ℝ) (K : ℕ) :
    Collection.Source G c :=
  { (plusone H X χ γ) with
    logRead := fun i => if cut X Sel K (Song.pennant H i).2 then 0 else (plusone H X χ γ).logRead i }

lemma kept_budget (χ : Chi) (γ : ℝ) (K : ℕ) {δ w : ℝ}
    (h : Collection.Local (posting p H) p (plusone H X χ γ) δ w) :
    Meadow.Budget p (posting p H).reg (kept X Sel χ γ K).logRead δ := by
  refine Meadow.emptyFree (posting p H).reg p
    (show Meadow.Budget p _ (plusone H X χ γ).logRead _ from ?_)
    (kept X Sel χ γ K).logRead ?_
  · obtain ⟨g,hg,hG⟩ := h.cheap
    exact ⟨g,hG,fun i => ⟨h.smooth i,hg i⟩⟩
  intro i
  unfold kept; dsimp only; split
  next => exact Or.inr rfl
  next => exact Or.inl rfl

-- avoid Rfl gas? depends activities.admissible uses K & regs? only K and forced.
theorem reconstruct (χ : Chi) (γ : ℝ) (K : ℕ) {δ w price : ℝ}
    (h : Collection.Local (posting p H) p (plusone H X χ γ) δ w)
    (hb : Meadow.Budget p (posting p H).reg (selected X Sel χ γ K).logRead price)
    (τ : ℝ) (V : Config G c) :
    earlyValue (posting p H) T.down T.low p (plusone H X χ γ) R.beta τ γ V =
      earlyValue (posting p H) T.down T.low p (kept X Sel χ γ K) R.beta τ γ V *
        Real.exp (- ((posting p H).read (selected X Sel χ γ K)).additive p V) := by
  let U := (posting p H).read (plusone H X χ γ)
  let U0 := (posting p H).read (kept X Sel χ γ K)
  let U1 := (posting p H).read (selected X Sel χ γ K)
  have h0 : U0.EBound p δ := unweighted p (kept_budget p X Sel χ γ K h)
  have h1 := unweighted p hb
  have ht : U.additive p V = U0.additive p V + U1.additive p V := by
    rw [Activities.additive,Activities.additive,Activities.additive,
      ← (Next.Rank.Alarm.ante p U0 h0 V).tsum_add (Next.Rank.Alarm.ante p U1 h1 V)]
    apply tsum_congr; intro i
    let s := (posting p H).reg i
    let v (f : Config G c → ℝ) := masked p.threshold s.support f V
    have he : v 0 = 0 := by
      by_cases ht : Healthy p.threshold s.support V
      · exact masked_eq _ _ _ _ ht
      exact masked_ne _ _ _ _ ht
    change v ((plusone H X χ γ).logRead i) = v ((kept X Sel χ γ K).logRead i) + v ((selected X Sel χ γ K).logRead i)
    rw [selector]; dsimp only [kept]; split <;> simp only [he,add_zero,zero_add]
  let b : ℝ := τ * Fintype.card (Site c) - T.down.inChannels T.low p R.beta V
  let t : ℝ := Real.exp (-γ*Collection.receipt T.down T.low p V)
  let r := U.gas p V
  -- gas of kept is same pointwise (uses only forced portion)
  have hg : U0.gas p V = U.gas p V := rfl
  change Real.exp (b-U.additive p V)* r * t = Real.exp (b-U0.additive p V)* U0.gas p V * t * Real.exp _
  rw [hg, ht, show b-(U0.additive p V + U1.additive p V)= b-U0.additive p V+(- U1.additive p V) by ring,
      Real.exp_add]; change _ = _*r*_ * Real.exp (-U1.additive p V); ring
end LogSplit
end YM.RGComparison01
