import YM.Integration.WilsonCapturedPrimarySmooth
import YM.Push.LOCAL_SPLITTING.Atoms

/-! The low-order derivative wallet is purchased from the complete original
coefficient. The arbitrary flat deposit disappears before taking the bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryRough
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations Planned.AtomRegular WilsonCapturedPrimaryReading
open scoped Classical ContDiff Topology

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

def quadratic (P : BudgetPoint) : BudgetPoint := { P with power := 2, power_ge := le_rfl }

private theorem borrow {P : BudgetPoint} {o : Site n} {X : Support n} {f : Config G n → ℂ}
    {v : ℝ} (hf : P.supBounds o X f v) : (quadratic P).supBounds o X f v := by
  refine ⟨hf.1,fun U healthy l length bill => hf.2 U healthy l length ?_⟩
  intro D hd e
  have h := bill D hd e
  have one : 1 ≤ 1+(separation e.1 o:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one P.power_ge)
    P.threshold_pos.le)

def price (G : Gauge) (k : ℕ) (M : ℝ) := patterns k * (baseCost G k * M^k)

private theorem fee {P : BudgetPoint} {o : Site n} {J : Finset (Link n)}
    {X : Support n} {f : Config G n → ℂ} {v M : ℝ} {k : ℕ} (hk : k ≤ P.order)
    (good : P.Regular X f) (billed : P.supBounds o X f v)
    (u : ℝ → Directions G n) (t : ℝ) (smooth : ContDiffAt ℝ k u t) (one : 1 ≤ M)
    (derivs : ∀ i, 0 < i → i ≤ k → ‖iteratedFDeriv ℝ i u t‖ ≤ M)
    (healthy : Healthy P.threshold X (bone (quadratic P) o J (u t)))
    (small : ∀ e∈J, ‖limitAmp (quadratic P) o J (u t) e‖ ≤ 1)
    (weights : ∀ e∈J, weight (quadratic P) o e ≤ 1) :
    ContDiffAt ℝ k ((f ∘ bone (quadratic P) o J) ∘ u) t ∧ ∀ j≤k,
      ‖iteratedFDeriv ℝ j ((f ∘ bone (quadratic P) o J) ∘ u) t‖ ≤ price G k M*v := by
  have bounds := base_bound (B:=quadratic P) (J:=J) (w:=u t) (c:=v)
    (show (quadratic P).Regular X f from
      ⟨good.sites,good.borel,good.symmetry,good.smooth,good.hasDerivs⟩) (borrow billed) hk healthy small weights
  refine ⟨bounds.1.comp t smooth,fun j hj => ?_⟩
  exact (nest_bound smooth bounds.1 hj (mul_nonneg (baseCost_nonneg ..) billed.1)
    one derivs bounds.2).trans_eq (by unfold price; ring)

variable {A : Hol G} {B : SectionData F} {R : Rep G n} {o : Site n}

/-- On a genuine healthy real interval the normalized signed source has a
period-independent derivative bound from its native regular and section wallets.
The same assertion applies to the retained row via the original collar funding. -/
theorem original {w : ℝ} (read : Readable A B R.p n w) {q : Coefficient F n}
    (form : q.Format o A R) {κ s : ℝ} (paid : q.remBound o R κ s) {k : ℕ}
    (pos : 0<k) (order : k≤R.p.order) (J : Finset (Link n)) (u : ℝ → Directions G n)
    {M : ℝ} (one : 1 ≤ M) {I : Set ℝ} (opened : IsOpen I) (connected : IsPreconnected I)
    (smooth : ∀ t∈I, ContDiffAt ℝ k u t)
    (derivs : ∀ t∈I, ∀ i, 0 < i → i ≤ k → ‖iteratedFDeriv ℝ i u t‖ ≤ M)
    (weights : ∀ e∈J, weight (quadratic R.p) o e ≤ 1)
    (small : ∀ t∈I, ∀ e∈J, ‖limitAmp (quadratic R.p) o J (u t) e‖ ≤ 1)
    (clear : ∀ t∈I, flags R.p.threshold (bone (quadratic R.p) o J (u t)) = ∅) :
    let W := bone (quadratic R.p) o J ∘ u
    ∀ t∈I, ContDiffAt ℝ k (reading B R o q ∘ W) t ∧
      ‖iteratedDeriv k (reading B R o q ∘ W) t‖ ≤
        price G k M*(w*F.coeffSize (F.core q.x)+s) := by
  intro W
  obtain ⟨a,b,ha,hb,hs,_,⟨e,he,hc⟩,_⟩ := paid
  have clearW t (ht : t∈I) : flags R.p.threshold (W t)=∅ := clear t ht
  have healthy (X : Support n) t (ht : t∈I) : Healthy R.p.threshold X (W t) := by
    unfold Healthy; rw [clearW t ht]; simp
  let row i := q.regular i ∘ W
  let core := presented B o R.p.threshold (F.core q.x) ∘ W
  let C := price G k M
  have posC : 0≤C := mul_nonneg (patterns_nonneg _) (mul_nonneg (baseCost_nonneg ..)
    (pow_nonneg (zero_le_one.trans one) _))
  have budget := sumBudget_mono he (fun i => (hc i).1)
    (fun i => R.p.loMass _ _ (hc i).1) le_rfl
  have cap := sumBudget_mul_left budget posC
  have regular i t (ht : t∈I) : ContDiffAt ℝ k (row i) t ∧ ∀ j≤k,
      ‖iteratedFDeriv ℝ j (row i) t‖ ≤ C*e i :=
    fee order (form.smooth i) (hc i) u t (smooth t ht) one (derivs t ht)
      (healthy _ t ht) (small t ht) weights
  have native := presented_good o read (F.core q.x)
  have stage t (ht : t∈I) : ContDiffAt ℝ k core t ∧
      ‖iteratedFDeriv ℝ k core t‖ ≤ C*(w*F.coeffSize (F.core q.x)) := by
    have h := fee order native.1 native.2 u t (smooth t ht) one (derivs t ht)
      (healthy _ t ht) (small t ht) weights
    exact ⟨h.1,h.2 k le_rfl⟩
  have sums := WilsonCapturedPrimarySmooth.local_series opened connected k row (fun i => C*e i)
    cap.2.1 (fun i t ht => (regular i t ht).1) (fun j hj i t ht => (regular i t ht).2 j hj)
  intro t ht
  let r (t : ℝ) := ∑' i, row i t
  have sc : ContDiffAt ℝ k r t := sums.1.contDiffAt (opened.mem_nhds ht)
  have eqn : (reading B R o q ∘ W) =ᶠ[𝓝 t] fun t => q.x 0 + (core t+r t) := by
    filter_upwards [opened.mem_nhds ht] with t ht
    change reading B R o q (W t) = _
    rw [on_clear read.sound q (clearW t ht)]
    change presented B o R.p.threshold q.x (W t) + r t = _
    rw [←presented_primary o read.sound q.x (W t) (healthy _ t ht)]
    change (q.x 0 + masked R.p.threshold _ _ (W t)) + r t = _
    rw [masked_eq _ _ _ _ (healthy _ t ht),add_assoc]; rfl
  refine ⟨(contDiffAt_const.add ((stage t ht).1.add sc)).congr_of_eventuallyEq eqn,?_⟩
  rw [eqn.iteratedDeriv_eq k,iteratedDeriv_const_add pos,
    iteratedDeriv_fun_add (stage t ht).1 sc]
  have a0 := norm_add_le (iteratedDeriv k core t) (iteratedDeriv k r t)
  rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv,←norm_iteratedFDeriv_eq_norm_iteratedDeriv] at a0
  apply a0.trans
  have rest : ‖iteratedFDeriv ℝ k r t‖ ≤ C*s :=
    (sums.2 t ht).trans (cap.2.2.trans (mul_le_mul_of_nonneg_left (by linarith only [hs,hb]) posC))
  exact (add_le_add (stage t ht).2 rest).trans_eq (by unfold C; ring)

end YM.Integration.WilsonCapturedPrimaryRough
