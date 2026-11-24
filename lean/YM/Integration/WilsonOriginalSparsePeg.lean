import YM.FormalBulk08.Lava.Ignis
import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import Mathlib.LinearAlgebra.Lagrange

/-! Finite held fields determining each ordered peg of a polynomial. The same slot
may occur more than once. All sampling costs depend only on the degree cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparsePeg
open Function Finset FormalBulk08 Tensor Planned.AtomRegular
open scoped Classical BigOperators

variable {I : Type*} [Fintype I] {d r : ℕ}

def node (d : ℕ) (j : Fin (d+1)) : ℝ := (j.val : ℝ) / (d+1:ℕ)

def direction (z : Fin r → I) (s : Finset (Fin r)) : I → ℝ :=
  ((r:ℝ)+1)⁻¹ • ∑ a ∈ s, (Pi.single (z a) (1:ℝ) : I → ℝ)

def probe (d : ℕ) (z : Fin r → I) (s : Finset (Fin r)) (j : Fin (d+1)) : I → ℝ :=
  node d j • direction z s

omit [Fintype I] in
theorem supported (z : Fin r → I) (s : Finset (Fin r)) (j : Fin (d+1))
    (i : I) (outside : ∀ a ∈ s, z a ≠ i) : probe d z s j i = 0 := by
  simp only [probe, direction, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [sum_eq_zero fun a ha => Pi.single_eq_of_ne (outside a ha).symm _]
  simp

theorem bounded (z : Fin r → I) (s : Finset (Fin r)) (j : Fin (d+1)) :
    ‖probe d z s j‖ ≤ 1 := by
  have hnode : |node d j| ≤ 1 := by
    rw [abs_of_nonneg (by unfold node; positivity)]
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast j.isLt.le)
  have sumNorm : ‖∑ a ∈ s, (Pi.single (z a) (1:ℝ) : I → ℝ)‖ ≤ (r:ℝ)+1 := calc
    _ ≤ ∑ a ∈ s, ‖(Pi.single (z a) (1:ℝ) : I → ℝ)‖ := norm_sum_le ..
    _ = (s.card:ℝ) := by simp [Pi.norm_single]
    _ ≤ r := by exact_mod_cast (s.card_le_univ.trans_eq (Fintype.card_fin r))
    _ ≤ (r:ℝ)+1 := by linarith
  have hd : ‖direction z s‖ ≤ 1 := by
    rw [direction,norm_smul_of_nonneg (by positivity)]
    exact (inv_mul_le_one₀ (by positivity)).mpr sumNorm
  rw [probe,norm_smul,Real.norm_eq_abs]
  exact mul_le_one₀ hnode (norm_nonneg _) hd

private def tensor (r : ℕ) (T : Lava.Tile I r) : Tensor.T (I → ℝ) ℝ r :=
  ∑ z, T z • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun a => ContinuousLinearMap.proj (z a))

private theorem value (T : Lava.Tile I r) (u : Fin r → I → ℝ) :
    tensor r T u = ∑ z, T z * ∏ a, u a (z a) := by
  simp [tensor]

private theorem symmetric (T : Lava.Tile I r) (h : Lava.Agate T) : Sym (tensor r T) := by
  intro u s
  rw [value,value]
  refine Fintype.sum_equiv (Equiv.arrowCongr s (Equiv.refl I)) _ _ fun z => ?_
  change T z * (∏ a, u (s a) (z a)) = T (z ∘ s.symm) * ∏ a, u a (z (s.symm a))
  rw [h]
  congr 1
  exact Fintype.prod_equiv s _ _ (fun a => by simp)

private theorem spikes (T : Lava.Tile I r) (z : Fin r → I) :
    tensor r T (fun a => Pi.single (z a) 1) = T z := by
  rw [value,Finset.sum_eq_single z]
  · simp
  · intro y _ hy
    obtain ⟨a,ne⟩ := Function.ne_iff.mp hy
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (Pi.single_eq_of_ne ne _),mul_zero]
  · simp

private theorem diagonal_read (p : MvPolynomial I ℝ) (k : ℕ) (u : I → ℝ) :
    diagonal (tensor k (Lava.marble k p)) u = MvPolynomial.eval u (MvPolynomial.homogeneousComponent k p) := by
  rw [←Lava.marble_grade,Lava.facade_eq,diagonal,value]
  simp [Lava.cards]

private def radial (p : MvPolynomial I ℝ) (d : ℕ) (y : I → ℝ) : Polynomial ℝ :=
  ∑ k ∈ range (d+1), Polynomial.monomial k (diagonal (tensor k (Lava.marble k p)) y)

private theorem radial_degree (p : MvPolynomial I ℝ) (y : I → ℝ) :
    (radial p d y).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  exact fun k hk => (Polynomial.natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hk))

private theorem radial_eval (p : MvPolynomial I ℝ) (hp : p.totalDegree ≤ d) (y : I → ℝ) (t : ℝ) :
    (radial p d y).eval t = MvPolynomial.eval (t • y) p := by
  conv_rhs => rw [← Lava.cemento p (d+1) (by omega),map_sum]
  rw [radial, Polynomial.eval_finsetSum]
  apply sum_congr rfl
  intro k _
  rw [Polynomial.eval_monomial,←diagonal_read,homogeneous,smul_eq_mul,mul_comm]

def radialCost (d : ℕ) : ℝ :=
  ∑ k ∈ range (d+1), ∑ j : Fin (d+1), |(Lagrange.basis univ (node d) j).coeff k|

private theorem radial_bound (p : MvPolynomial I ℝ) (hp : p.totalDegree ≤ d) (hr : r ≤ d)
    (y : I → ℝ) {E : ℝ} (nonneg : 0 ≤ E)
    (paid : ∀ j, |MvPolynomial.eval (node d j • y) p| ≤ E) :
    ‖diagonal (tensor r (Lava.marble r p)) y‖ ≤ radialCost d * E := by
  let q := radial p d y
  have hq : q.degree < ((@univ (Fin (d+1)) _).card : WithBot ℕ) :=
    q.degree_le_natDegree.trans_lt (by
      rw [card_univ,Fintype.card_fin]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (radial_degree p y)))
  have inj : Set.InjOn (node d) (univ : Finset (Fin (d+1))) := by
    intro a _ b _ h
    apply Fin.ext
    exact_mod_cast (div_left_inj' (by positivity : (d+1:ℕ) ≠ (0:ℝ))).mp h
  have coeff : q.coeff r = diagonal (tensor r (Lava.marble r p)) y := by
    simp [q,radial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,hr]
  rw [←coeff,Real.norm_eq_abs]
  conv_lhs => rw [Lagrange.eq_interpolate (f:=q) inj hq,Lagrange.interpolate_apply,Polynomial.finsetSum_coeff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ j : Fin (d+1), |(Lagrange.basis univ (node d) j).coeff r| * E := by
      apply sum_le_sum
      intro j _
      rw [Polynomial.coeff_C_mul, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (by simpa [q,radial_eval p hp] using paid j) (abs_nonneg _)
    _ = (∑ j : Fin (d+1), |(Lagrange.basis univ (node d) j).coeff r|)*E := (sum_mul ..).symm
    _ ≤ radialCost d * E := by
      apply mul_le_mul_of_nonneg_right _ nonneg
      unfold radialCost
      exact single_le_sum (f:=fun k => ∑ j : Fin (d+1), |(Lagrange.basis univ (node d) j).coeff k|)
        (fun k _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le hr))

/-- This constant is chosen before the slot space and its physical volume. -/
def cost (d : ℕ) : ℝ := (∑ k ∈ range (d+1), polarCost k) * radialCost d

theorem original (p : MvPolynomial I ℝ) (hp : p.totalDegree ≤ d) (hr : r ≤ d)
    (z : Fin r → I) {E : ℝ} (nonneg : 0 ≤ E)
    (paid : ∀ s j, |MvPolynomial.eval (probe d z s j) p| ≤ E) :
    |Lava.marble r p z| ≤ cost d * E := by
  let A := tensor r (Lava.marble r p)
  let w (a : Fin r) : I → ℝ := Pi.single (z a) 1
  let m := ((univ.filter (fun f : Fin r → Fin r => Surjective f)).card : ℝ)
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (Nat.succ_le_iff.mpr (perm_cost_pos r))
  have h := cross_effect A w
  rw [perm_effect A (symmetric _ (Lava.marble_agate _ _))] at h
  have hr1 : 0 < (r:ℝ)+1 := by positivity
  have part (s : Finset (Fin r)) : ‖diagonal A (∑ a ∈ s,w a)‖ ≤ ((r:ℝ)+1)^r*(radialCost d * E) := by
    have restore : ((r:ℝ)+1) • direction z s = ∑ a ∈ s,w a := by
      rw [direction,smul_smul,mul_inv_cancel₀ hr1.ne',one_smul]
    rw [←restore,homogeneous,norm_smul_of_nonneg (pow_nonneg hr1.le _)]
    exact mul_le_mul_of_nonneg_left (radial_bound p hp hr _ nonneg (paid s)) (pow_nonneg hr1.le _)
  have scale : polarCost r ≤ ∑ k ∈ range (d+1),polarCost k :=
    single_le_sum (fun k _ => zero_le_one.trans (polar_one k)) (mem_range.mpr (Nat.lt_succ_of_le hr))
  have money : 0 ≤ radialCost d * E := mul_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) nonneg
  change (∑ s : Finset (Fin r),_) = m • A w at h
  rw [←Real.norm_eq_abs,←spikes (Lava.marble r p) z]
  calc
    ‖A w‖ ≤ m * ‖A w‖ := le_mul_of_one_le_left (norm_nonneg _) hm
    _ ≤ ∑ _s : Finset (Fin r), ((r:ℝ)+1)^r*(radialCost d * E) := by
      rw [←norm_smul_of_nonneg (zero_le_one.trans hm),←h]
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro s _
      rw [norm_smul,norm_pow]
      simpa using part s
    _ = polarCost r * (radialCost d * E) := by simp [polarCost,mul_assoc]
    _ ≤ cost d * E := by
      rw [cost,mul_assoc]
      exact mul_le_mul_of_nonneg_right scale money

/-- Maximum over the finite signed hearings at the listed peg. -/
def measured (p : MvPolynomial I ℝ) (d : ℕ) (z : Fin r → I) : ℝ :=
  univ.sup' univ_nonempty (fun u : Finset (Fin r) × Fin (d+1) =>
    |MvPolynomial.eval (probe d z u.1 u.2) p|)

theorem maximum (p : MvPolynomial I ℝ) (hp : p.totalDegree ≤ d) (hr : r ≤ d)
    (z : Fin r → I) : |Lava.marble r p z| ≤ cost d * measured p d z := by
  have le (s : Finset (Fin r)) (j : Fin (d+1)) :
      |MvPolynomial.eval (probe d z s j) p| ≤ measured p d z :=
    le_sup' (fun u : Finset (Fin r) × Fin (d+1) =>
      |MvPolynomial.eval (probe d z u.1 u.2) p|) (mem_univ (s,j))
  exact original p hp hr z ((abs_nonneg _).trans (le ∅ 0)) le

omit [Fintype I] in
theorem zero_probe (z : Fin 0 → I) (s : Finset (Fin 0)) (j : Fin (d+1)) :
    probe d z s j = 0 := by
  funext i
  exact supported z s j i (fun a => Fin.elim0 a)

end YM.Integration.WilsonOriginalSparsePeg
end
