import YM.RG01.Cull
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Skills

/-! # Transport onto the assembly addresses of Song.forward
Keep an EARLY (+3 spare) exponent, cover of full recorded support, and all budget
derivatives on Healthy. Distinct addresses; never replace a represented estimate
by a supremum on log sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.List
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Greenbelt Match Song
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R R' : RG.Rep G f} {μ q C' d v Y A b r B s α a i C Λ δ e : ℝ} {k j : ℕ}
    {χ : Chi}

/-! Actual occurrence-component block of the EARLY Listing. This excludes the
path read and does NOT enter forced K: insert as **regular exponent** on the indicated
addresses and keep the complete existing K partners. -/
variable {H : Cash W s μ L Q o α T R} {J : Cash W s μ L Q o α T R'}
variable (X : Alliance H J 1 0)

/-- transport a real label reweighting θ (doesn't move with field) to the
actual early source addresses. θ=1 isolates the region to which our
artificial grading/Cauchy estimate will apply. -/
def song (θ : J.fragrances → ℝ) : Magazine H → Config G c → ℝ :=
    Sum.elim (fun z => θ (X.furrow z) • Song.sequence H X χ z) fun _=>0

def addresses (θ : J.fragrances → ℝ) : ℕ → Config G c → ℝ :=
    choir (song (χ:=χ) X θ) ∘ pennant H

def exFare (test : J.fragrances → Prop) : J.fragrances → ℝ := fun z=> if test z then 1 else 0

def tail (test : J.fragrances → Prop) : Collection.Source G c :=
    { (Song.plusone H X χ 0) with logRead := addresses (χ:=χ) X (exFare test) }

def front (test : J.fragrances → Prop) (γ : ℝ) : Collection.Source G c :=
    sleeping H X χ (test ∘ X.furrow) γ

lemma at_split (test : J.fragrances → Prop) (γ : ℝ) (l : ℕ) :
    let v:=plusone H X χ γ
    (tail (χ:=χ) X test).logRead l + (front (χ:=χ) X test γ).logRead l=v.logRead l := by
  intro v
  obtain ⟨he,hg⟩:= Height.bolted H X χ (test ∘ X.furrow) γ l
  have hv : song (χ:=χ) X (exFare test)=skilled H X χ (test ∘ X.furrow):= by
    funext i
    rcases i with i|i
    · dsimp only [skilled,song,exFare,Sum.elim,Function.comp_apply]
      split <;> simp
    rfl
  change (choir (song (χ:=χ) X (exFare test)) ∘ pennant H) l+_= _
  rw [hv,front,hg]
  change (serve H X χ (test ∘ X.furrow)).logRead l+_= _
  rw [he]; split <;> simp [v]

/-- p means the actual output budget. All p.order derivatives and p.power
position weights, irrespective of the truncation order. We keep Regular so
a bound on junk `deriv` in an unlicensed germ cannot qualify. -/
structure Budget (p : BudgetPoint) (X : ℕ → RegularAddress c) (f : ℕ → Config G c → ℝ) (b : ℝ) : Prop where
  purchased : ∃ m, Quotes.early p X m b ∧ ∀ z, p.Regular (X z).support (f z) ∧
    p.supBounds (X z).site (X z).support (f z) (m z)

lemma Budget.unweighted {p : BudgetPoint} {X : Listing G c} {F : Collection.Source G c}
    (h : Budget p X.reg F.logRead b) : (X.read F).EBound p b := by
  obtain ⟨m,h1,h2⟩:=h.purchased
  exact ⟨m,fun z=> (h2 z).2,Quotes.segment X.reg (fun i=> (h2 i).2.1) h1⟩

lemma Budget.regular {p : BudgetPoint} {X : Listing G c} {F : Collection.Source G c}
    (h : Budget p X.reg F.logRead b) (i) : p.Regular (X.reg i).support (F.logRead i) := by
  obtain ⟨m, _, h2⟩:=h.purchased
  exact (h2 i).1

lemma Budget.loosen {p : BudgetPoint} {X : ℕ → RegularAddress c} {F : ℕ → Config G c → ℝ}
    (h : Budget p X F b) (he : b ≤ a) : Budget p X F a := by
  obtain ⟨m,h1,h2⟩:=h.purchased
  exact ⟨m,fun i=> budget_loosen (h1 i) he,h2⟩

variable (N : Captain J j C' d v Y A b r B q k χ)

/-- Arbitrary real reweighting dominated by the hit receipt per fragrance
(or multiplying that receipt adapt it to either Re or Im of complex ζ-label,
even pointwise per address). Preserve rotation/translation averaging before
recording, so there's no volume factor for `pennant`. -/
lemma supplied (p : BudgetPoint) (n : ℕ) (hp : p.threshold=Pressure.temp s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hB : p.B=radiusB s) (ha : preExponent p ≤ a)
    (θ : J.fragrances → ℝ) (U : J.fragrances → ℝ)
    (hU : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) U a C)
    (hv : ∀ z, |θ z| * N.markΦ z n ≤ U z) :
    Budget p (posting p H).reg (addresses (χ:=χ) X θ) (turnFee p * C) := by
  let m (z : H.fragrances) := U (X.furrow z)
  let F (z:H.fragrances) := θ (X.furrow z) • Song.sequence H X χ z
  have hM : ∀ i, 0 ≤ m i := fun i=> le_trans (mul_nonneg (abs_nonneg _) (Beacon.money_nonneg N _ _)) (hv _)
  have hP : Quotes.early p (locate H) m C := by
    intro w
    have hh:= budget_pull X.furrow X.furrow.injective (hU w)
    refine budget_mono hh (fun z=>?_) (fun z=>?_)
    · dsimp only; split
      next => exact mul_nonneg (hM _) (Real.exp_pos _).le
      exact le_rfl
    dsimp only
    split
    next hx =>
      have hL:(locate H z).support = reachability (H:=J) (X.furrow z):= Song.reconnects H X z
      rw [if_pos (show w ∈ reachability (H:=J) (X.furrow z) from hL ▸ (hx ▸ (locate H z).anchor)),hL,hB]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (hM z)
    exact hh.1 _
  have hF i : p.Regular (locate H i).support (F i) ∧
      p.supBounds (locate H i).site (locate H i).support (F i) (m i):= by
    obtain ⟨he,hK⟩:= pocketScore p H X χ N hp hj n hn i
    exact ⟨CouplingShape.reg_scale _ he, VerifiedReset.sup_le (CouplingShape.sup_scale _ hK) (hv _)⟩
  let K : Magazine H → ℝ := Sum.elim m fun _ => 0
  have hK (z : Magazine H) : p.Regular (scaleT p H z).support (song (χ:=χ) X θ z) ∧
      p.supBounds (scaleT p H z).site (scaleT p H z).support (song (χ:=χ) X θ z) (K z):= by
    rcases z with i|i
    · exact hF _
    exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  have hf : Quotes.early p (scaleT p H) K C := by
    intro z
    let Y:= hP z
    rw [← add_zero C]
    apply Cost.sum Y
    apply budget_of_sum
    · intro i
      change 0 ≤ if (strings T.down p i).site=z then 0*_ else 0
      simp
    intro v
    apply Finset.sum_nonpos
    intro i _
    change (if (strings T.down p i).site=z then (0:ℝ)*_ else 0) ≤ 0
    simp
  obtain ⟨hc,he⟩ := spiral (scaleT p H) (song (χ:=χ) X θ) K (fun i=> (hK i).1) (fun i=> (hK i).2) hf
  exact ⟨_,fun i=> Cost.equiv (pennant H) (he i),fun i=> hc (pennant H i)⟩

/-- Culled addresses already satisfy pre-reset budget with a gain `K⁻¹`. -/
lemma license (p : BudgetPoint) (n : ℕ) (ht : p.threshold=Pressure.temp s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hB : p.B=radiusB s) (ha : preExponent p ≤ a)
    (hd : 1 ≤ grow G L s) (hw : Heavy N.conduit)
    (arm : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hSal : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)
    (test : J.fragrances → Prop) (K : ℝ) (hk : 0 < K)
    (gain : ∀ z, test z → K ≤ beacon J z) :
    Budget p (posting p H).reg ((tail (χ:=χ) X test).logRead)
      (turnFee p * (K⁻¹*(collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹)))) := by
  apply supplied X N p n ht hj hn hB ha _ _ (Beacon.select N hd hw n arm hs hSal test K hk gain)
  intro z
  unfold exFare
  split <;> simp

end YM.RG01.List
