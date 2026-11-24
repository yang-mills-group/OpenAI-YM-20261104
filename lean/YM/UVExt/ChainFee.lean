import YM.UVExt.RealProduct
/-! One rank gain when taking products of primitives after moving the root. Uses no cancellation
between orientations across a penalty. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Real
open scoped Classical BigOperators Topology InnerProductSpace ContDiff
variable {P Q D Y A : ℝ} {f g h : ℝ→ℝ} {m n k : ℕ}
abbrev tag (k : ℕ) (a : ℝ→ℝ) := iteratedDeriv k a 0

lemma bottom_comp (a : Bill P m f) (b : Bill Q n g) :
    tag (m+n) (f*g) = (m+n).choose m * tag  m f * tag  n g := by
  have hr (r) := iteratedDeriv_mul (𝕜:=ℝ) (𝔸:=ℝ) (n:=r) (a.smooth.of_le (by simp)) (b.smooth.of_le (by simp)) -- fix
  unfold tag
  rw [hr (m+n),Finset.sum_eq_single m]
  · simp
  · intro j hj hjm
    have hx := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hjm with hj|hj
    · simp [a.vanish _ hj]
    simp only [b.vanish (m+n-j) (by omega),mul_zero]
  simp

lemma one_more_comp (a : Bill P m f) (b : Bill Q n g) :
    tag (m+n+1) (f*g) = (m+n+1).choose m * tag  m f * tag  (n+1) g + (m+n+1).choose (m+1) * tag  (m+1) f * tag  n g := by
  have hr (r) := iteratedDeriv_mul (𝕜:=ℝ) (𝔸:=ℝ) (n:=r) (a.smooth.of_le (by simp)) (b.smooth.of_le (by simp))
  let T j := (((m+n+1).choose j):ℝ) * tag  j f * tag (m+n+1-j) g
  have hm : m ∈ Finset.range (m+n+1+1) := Finset.mem_range.mpr (by omega)
  calc
    _ = ∑ j∈ ({m,m+1} : Finset ℕ), T j := (hr _).trans (Finset.sum_subset (s₂:=Finset.range (m+n+1+1)) (f:=T) (s₁:={m,m+1}) (by intro j hj; simp_all; omega) fun j hJ hj => by
       simp only [Finset.mem_range] at hJ
       simp only [Finset.mem_insert, Finset.mem_singleton,not_or] at hj
       by_cases h:j<m
       · simp [T,tag, a.vanish _ h]
       unfold T tag; rw [b.vanish (m+n+1-j) (by omega),mul_zero]).symm
    _ = T m + T (m+1) := by rw [Finset.sum_insert (by simp),Finset.sum_singleton]
    _ = _ := by unfold T tag; rw [show m+n+1-m=n+1 by omega,show m+n+1-(m+1)=n by omega]

lemma triplePrice (a : Bill P 2 g) (b : Bill P 1 f) (hD : 0 ≤ D) (hY : D ≤ Y) (h : |tag 1 f| ≤ D) (hg : |tag 2 g| ≤ D^2) (bought : P ≤ Y) :
    |tag 3 (f*g)| ≤ 3*D^3 ∧ |tag 4 (f*g)| ≤ 10 * D * Y^3 := by
  have he : 0 ≤ Y := hD.trans hY
  rw [show (3:ℕ)=1+2 by decide, show (4:ℕ)=1+2+1 by decide, bottom_comp b a, one_more_comp b a]
  have h3 : ((↑(Nat.choose (1+2) 1)):ℝ)=3 := by norm_num
  have h6 : ((↑(Nat.choose (1+2+1) (1+1))):ℝ)=6 := by norm_num [Nat.choose]
  have h4 : ((↑(Nat.choose (1+2+1) 1)):ℝ)=4 := by norm_num
  rw [h3,h4,h6]; constructor
  · have h' : |3*tag 1 f| ≤ 3*D := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]; simpa using mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤3)
    rw [abs_mul]
    exact (mul_le_mul h' hg (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · have hb1 : |tag (2+1) g| ≤ Y^3 := (a.pay _).trans (by simpa using pow_le_pow_left₀ a.pos bought 3)
    have hb2 : |tag (1+1) f| ≤ Y^2 := (b.pay _).trans (by simpa using pow_le_pow_left₀ b.pos bought 2)
    have hb3 : |tag 2 g| ≤ D*Y := hg.trans (by rw [pow_two]; gcongr)
--   --rw [show ((↑((1+2+1).choose (1+1)):ℝ))=6 by norm_num [Nat.choose], show ((↑((1+2+1).choose 1)):ℝ)=4 by norm_num]-/
    apply (_root_.abs_add_le _ _).trans
    simp_rw [abs_mul]
    exact (add_le_add (mul_le_mul (mul_le_mul (le_of_eq rfl) h (abs_nonneg _) (by positivity)) hb1 (abs_nonneg _) (show 0 ≤ |(4:ℝ)| * D by positivity)) (mul_le_mul (mul_le_mul (le_of_eq rfl) hb2 (abs_nonneg _) (by positivity)) hb3 (abs_nonneg _) (show 0 ≤ |(6:ℝ)| * Y^2 by positivity))).trans_eq (by norm_num; ring)

lemma hrow (m) (s : Fin m → ℝ→ℝ) (b : ∀ i, Bill P 1 (s i)) : Bill ((m:ℝ)*P) m (∏ i, s i) := by
  induction m with
  | zero => simpa [iteratedDeriv_const] using (show Bill 0 0 1 by refine ⟨le_rfl, contDiffAt_const,fun i=> by change ‖iteratedDeriv _ (fun _ : ℝ=> (1:ℝ)) ..‖≤_; cases i <;> simp [iteratedDeriv_const],fun i hi=>by omega⟩)
  | succ m im => rw [Fin.prod_univ_succ]; convert (b 0).multiply (im _ (fun i => b (i.succ))) using 1 <;> simp [add_mul,add_comm]

lemma evenPrice {F : Fin m → ℝ→ℝ} (b : ∀ i : Fin m, Bill P 1 (F i)) (he : ∀ i, |tag 1 (F i)| ≤ D) :
    |tag m (∏ i : Fin m,F i)| ≤ (m.factorial:ℝ) * D ^ m := by
  induction m with
  | zero => simp [tag]
  | succ m ih =>
    have hD := abs_nonneg _ |>.trans (he 0)
    
    let s : Fin m → ℝ→ℝ := (fun i => F i.succ)
    have ht (i : Fin m) := b (i.succ)
    calc
      _ = |(1+m:ℕ) * tag 1 (F 0) * tag m (∏ j, s j)| := by
          congr 1; rw [Fin.prod_univ_succ]
          exact ((congr_arg (iteratedDeriv · (F 0 * ∏ j, s j) 0) (Nat.add_comm m 1)).trans (bottom_comp (b 0) (hrow m s ht))).trans (by simp)
      _ ≤ ((1+m:ℕ) * D) * (m.factorial * D^m) := by
          rw [abs_mul,abs_mul,abs_of_nonneg (by positivity)]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (he 0) (by positivity)) (ih (b:=ht) (fun i=>by exact he i.succ)) (abs_nonneg _) (by positivity)
      _ = _ := by rw [Nat.factorial_succ,pow_succ]; push_cast; ring

end YM.UVExt.Paths
