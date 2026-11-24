import YangMills.WilsonProof.NativeSupport.MatchingNesting
import YM.Integration.WilsonCenteredNestedProducts

/-! Exact cancellation of the vertex engineering dimensions on the public
finite fusion tree.  A replacement at an edge spends the extra order only
against that edge's parent, with every sibling radius still independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeEdgePowers
open YangMills YangMills.Hierarchy Function
open WilsonCenteredNestedProducts
open scoped Classical BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (t : FusionTree)

def attachedBase (a : Fin t.leaves → T.Tag) (s : t.Vertex → ℝ) (m : ℕ) : ℝ :=
  s 0 ^ m / ∏ i, s (t.attachLeaf i) ^ (a i).1

def port (a : Fin t.leaves → T.Tag) {D : Fin t.branches → ℕ}
    (u : t.Selection T D) (m : ℕ) (c : T.Channel m) (s : t.Vertex → ℝ) (v : t.Vertex) : ℝ :=
  s v ^ (t.vertexChannel T u m c v).1 /
    ∏ p : t.Child v, s v ^ (t.childField T a u p).1

private lemma denominators (a : Fin t.leaves → T.Tag) {D : Fin t.branches → ℕ}
    (u : t.Selection T D) (s : t.Vertex → ℝ) :
    (∏ v : t.Vertex, ∏ p : t.Child v, s v ^ (t.childField T a u p).1) =
      (∏ i, s (t.attachLeaf i) ^ (a i).1) * ∏ j, s (t.parent j.succ) ^ (u j).1.val := by
  let parent : Fin t.leaves ⊕ Fin t.branches → t.Vertex :=
    Sum.elim t.attachLeaf (fun i => t.parent i.succ)
  let w : Fin t.leaves ⊕ Fin t.branches → ℕ := Sum.elim (fun i => (a i).1) (fun i => (u i).1.val)
  calc
    _ = ∏ p, s (parent p) ^ w p := by
      rw [← Fintype.prod_fiberwise parent (fun p => s (parent p) ^ w p)]
      apply Finset.prod_congr rfl
      intro v _
      apply Finset.prod_congr (by ext p; simp)
      intro p _
      have site : parent p.val = v := p.property
      rw [site]
      congr 1
      cases p with
      | mk p hp => cases p <;> rfl
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

theorem ports (a : Fin t.leaves → T.Tag) {D : Fin t.branches → ℕ}
    (u : t.Selection T D) (m : ℕ) (c : T.Channel m) (s : t.Vertex → ℝ) :
    (∏ v : t.Vertex, port T t a u m c s v) =
      attachedBase T t a s m * ∏ i, t.ratio s i ^ (u i).1.val := by
  unfold port
  rw [Finset.prod_div_distrib, denominators]
  rw [Fin.prod_univ_succ (fun v : t.Vertex => s v ^ (t.vertexChannel T u m c v).1)]
  change (s 0 ^ m * ∏ i, s i.succ ^ (u i).1.val) / _ = _
  unfold attachedBase FusionTree.ratio
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib]
  simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]

theorem scale_le_root {s : t.Vertex → ℝ} (sp : ∀ v, 0 < s v)
    (ratio_small : ∀ i, t.ratio s i ≤ 1) (v : t.Vertex) : s v ≤ s 0 := by
  have step (w : t.Vertex) : s w ≤ s (t.parent w) := by
    refine Fin.cases ?_ (fun i => ?_) w
    · rw [t.rootFixed]
    · exact (div_le_one (sp _)).mp (ratio_small i)
  have iter (n : ℕ) (w : t.Vertex) : s w ≤ s (t.parent^[n] w) := by
    induction n generalizing w with
    | zero => exact le_rfl
    | succ n ih => simpa only [Function.iterate_succ_apply] using (step w).trans (ih (t.parent w))
  obtain ⟨n,hn⟩ := t.reachesRoot v
  simpa only [hn] using iter n v

theorem retained_gain (s : t.Vertex → ℝ) (D d : Fin t.branches → ℕ)
    (hd : ∀ i, d i ≤ D i) (sp : ∀ v, 0 < s v) (small : s 0 ≤ 1)
    (ratio_small : ∀ i, t.ratio s i ≤ 1) (i : Fin t.branches) :
    (∏ j, t.ratio s j ^ d j) * s i.succ ^ (D i+1-d i) ≤ t.ratio s i ^ (D i+1) := by
  let q := t.ratio s
  have qp (j) : 0 ≤ q j := (div_pos (sp _) (sp _)).le
  have upper : s (t.parent i.succ) ≤ 1 := (scale_le_root t sp ratio_small _).trans small
  have other := Finset.prod_le_one (s := Finset.univ.erase i) (f := fun j => q j ^ d j)
    (fun j _ => pow_nonneg (qp j) _) (fun j _ => pow_le_one₀ (qp j) (ratio_small j))
  have own : q i ^ d i * s i.succ ^ (D i+1-d i) ≤ q i ^ (D i+1) := by
    have atParent : s i.succ = q i * s (t.parent i.succ) :=
      (div_mul_cancel₀ _ (sp _).ne').symm
    rw [atParent, mul_pow, ←mul_assoc, ←pow_add, Nat.add_sub_of_le ((hd i).trans (Nat.le_succ _))]
    exact mul_le_of_le_one_right (pow_nonneg (qp i) _) (pow_le_one₀ (sp _).le upper)
  change (∏ j, q j ^ d j) * _ ≤ _
  rw [←Finset.prod_erase_mul Finset.univ (fun j => q j ^ d j) (Finset.mem_univ i), mul_assoc]
  exact (mul_le_of_le_one_left (mul_nonneg (pow_nonneg (qp i) _) (pow_nonneg (sp _).le _)) other).trans own

/-- Keep the raw root factor in both products and telescope precisely the
actual nonroot factors. The product of all vertex prices cancels every
incoming retained grade before the error is charged to its own edge. -/
theorem product (a : Fin t.leaves → T.Tag) {D : Fin t.branches → ℕ}
    (u : t.Selection T D) (m : ℕ) (c : T.Channel m) (s L : t.Vertex → ℝ)
    (sp : ∀ v, 0 < s v) (small : s 0 ≤ 1) (ratio_small : ∀ i, t.ratio s i ≤ 1)
    (Ln : ∀ v, 0 ≤ L v) (root : ℂ) (X Y : Fin t.branches → ℂ)
    (head : ‖root‖ ≤ L 0 * port T t a u m c s 0)
    (rows : ∀ i, Priced (X i) (Y i) (L i.succ * port T t a u m c s i.succ)
      (s i.succ ^ (D i+1-(u i).1.val))) :
    ‖(∏ i, X i) * root - (∏ i, Y i) * root‖ ≤
      ((∏ v, L v) * attachedBase T t a s m) * t.cutoffGain D s := by
  let B (v) := L v * port T t a u m c s v
  let E (i : Fin t.branches) := s i.succ ^ (D i+1-(u i).1.val)
  have p := Priced.product Finset.univ X Y (fun i => B i.succ) E (fun i _ => rows i)
  let A := (∏ v, L v) * attachedBase T t a s m
  have An : 0 ≤ A := mul_nonneg (Finset.prod_nonneg (fun v _ => Ln v))
    (div_nonneg (pow_nonneg (sp 0).le _) (Finset.prod_nonneg (fun i _ => pow_nonneg (sp _).le _)))
  have normal : (∏ v, B v) = A * ∏ i, t.ratio s i ^ (u i).1.val := by
    simp only [B, Finset.prod_mul_distrib, ports, A, mul_assoc]
  calc
    _ = ‖(∏ i, X i)-(∏ i, Y i)‖ * ‖root‖ := by rw [←sub_mul, norm_mul]
    _ ≤ ((∏ i : Fin t.branches, B i.succ) * ∑ i, E i) * B 0 :=
      mul_le_mul p.change head (norm_nonneg _) ((norm_nonneg _).trans p.change)
    _ = (∏ v, B v) * ∑ i, E i := by rw [Fin.prod_univ_succ B]; ring
    _ = ∑ i, (∏ v, B v) * E i := Finset.mul_sum ..
    _ ≤ ∑ i, A * t.ratio s i ^ (D i+1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [normal,mul_assoc]
      apply mul_le_mul_of_nonneg_left _ An
      exact retained_gain t s D (fun j => (u j).1.val) (fun j => Nat.le_of_lt_succ (u j).1.isLt)
        sp small ratio_small i
    _ = _ := (Finset.mul_sum ..).symm

end YM.Integration.WilsonSharpPhysicalTreeEdgePowers
