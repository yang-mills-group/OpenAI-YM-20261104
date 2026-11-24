import YM.Integration.FVA1Physical.Wilson.WickStencil

/-! A fixed polynomial on finitely many marked coordinates has a dimension-free
Gaussian stability price. Repeated and coincident placements are permitted. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open MvPolynomial Matrix MeasureTheory Finset Function MSbar.Cacao Further.GaussianScalar
open scoped Classical
variable {α σ ι ι' : Type}

private def BoxRead (p : Pot α) (C : ℝ) (d : ℕ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ (x y : α → ℝ), (∀ i, |x i| ≤ r) → (∀ i, |y i| ≤ r) →
    ∀ (ε : ℝ), 0 ≤ ε → (∀ i, |x i-y i| ≤ ε) →
    |eval x p| ≤ C*r^d ∧ |eval x p - eval y p| ≤ C*r^d*ε

private lemma box_weaken (p : Pot α) {C : ℝ} {d d' : ℕ} (hC : 0≤C) (hd : d≤d')
    (paid : BoxRead p C d) : BoxRead p C d' := by
  intro r hr x y hx hy ε hε hxy
  obtain ⟨a,b⟩:=paid r hr x y hx hy ε hε hxy
  have step:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hd) hC
  exact ⟨a.trans step,b.trans (mul_le_mul_of_nonneg_right step hε)⟩

private theorem box_read_paid (p : Pot α) : ∃ (C : ℝ) (d : ℕ), 0≤C ∧ BoxRead p C d := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨|a|,0,abs_nonneg _,?_⟩
    intro r hr x y hx hy ε hε hxy
    simp only [eval_C,pow_zero,mul_one,sub_self,abs_zero,le_refl,true_and]
    positivity
  | add p q hp hq =>
    obtain ⟨C,d,hC,g⟩:=hp
    obtain ⟨D,e,hD,k⟩:=hq
    let f:=max d e
    refine ⟨C+D,f,add_nonneg hC hD,?_⟩
    intro r hr x y hx hy ε hε hxy
    obtain ⟨u,v⟩:=box_weaken p hC (le_max_left d e) g r hr x y hx hy ε hε hxy
    obtain ⟨a,b⟩:=box_weaken q hD (le_max_right d e) k r hr x y hx hy ε hε hxy
    simp only [_root_.map_add]
    refine ⟨(abs_add_le ..).trans ((add_le_add u a).trans_eq (by dsimp only [f]; ring)),?_⟩
    rw [show eval x p+eval x q-(eval y p+eval y q)=(eval x p-eval y p)+(eval x q-eval y q) by ring]
    exact (abs_add_le ..).trans ((add_le_add v b).trans_eq (by dsimp only [f]; ring))
  | mul_X p i hp =>
    obtain ⟨C,d,hC,g⟩:=hp
    refine ⟨2*C,d+1,by positivity,?_⟩
    intro r hr x y hx hy ε hε hxy
    obtain ⟨u,v⟩:=g r hr x y hx hy ε hε hxy
    have a:|eval y p|≤C*r^d:=(g r hr y y hy hy 0 le_rfl (by simp)).1
    have hr0:0≤r:=by linarith
    have n:0≤C*r^d:=mul_nonneg hC (pow_nonneg hr0 _)
    have nε:0≤C*r^d*ε:=mul_nonneg n hε
    simp only [_root_.map_mul,eval_X]
    constructor
    · rw [abs_mul]; refine (mul_le_mul u (hx i) (abs_nonneg _) n).trans ?_
      rw [pow_succ]; nlinarith only [mul_nonneg n hr0]
    rw [show eval x p*x i-eval y p*y i=(eval x p-eval y p)*x i+eval y p*(x i-y i) by ring]
    refine (abs_add_le ..).trans ?_
    simp only [abs_mul]
    have l:=mul_le_mul v (hx i) (abs_nonneg _) nε
    have t:=mul_le_mul a (hxy i) (abs_nonneg _) n
    refine (add_le_add l t).trans ?_
    rw [pow_succ]; nlinarith only [mul_nonneg nε (sub_nonneg.mpr hr)]

theorem parameter_stencil_price (P : Pot (WickSlot σ)) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ (x y : σ→ℝ) (V W : σ→σ→ℝ)
    (R ε : ℝ), 1≤R → 0≤ε → (∀ i, |x i|≤R) → (∀ i, |y i|≤R) →
    (∀ i j, |V i j|≤R) → (∀ i j, |W i j|≤R) →
    (∀ i, |x i-y i|≤ε) → (∀ i j, |V i j-W i j|≤ε) →
    |eval (parameters x V) P-eval (parameters y W) P|≤C*R^d*ε := by
  obtain ⟨C,d,h,paid⟩:=box_read_paid P
  refine ⟨C,d,h,?_⟩
  intro x y V W R ε hR hε hx hy hv hw de dc
  exact (paid R hR _ _ (fun i=>by cases i with | inl j=> exact hx j | inr jk=>exact hv jk.1 jk.2)
    (fun i=>by cases i with | inl j=> exact hy j | inr jk=>exact hw jk.1 jk.2)
    ε hε (fun i=>by cases i with | inl j=> exact de j | inr jk=>exact dc jk.1 jk.2)).2

theorem wick_stencil_stability [Fintype σ] [DecidableEq σ] (P : Pot σ) :
    ∃ (A : ℝ) (d : ℕ), 0≤A ∧
    ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
      (v : Matrix σ ι ℝ) (w : Matrix σ ι' ℝ) (C : Matrix ι ι ℝ) (D : Matrix ι' ι' ℝ),
    C.PosDef → D.PosDef → ∀ (x y : View σ) (R ε : ℝ), 1≤R → 0≤ε →
    let first:=parameters x (v*C*v.transpose)
    let second:=parameters y (w*D*w.transpose)
    (∀ k, |first k| ≤ R) → (∀ k, |second k| ≤ R) → (∀ k, |first k-second k| ≤ ε) →
    |(∫ a, eval (x+v *ᵥ a) P ∂fieldLaw C) - ∫ b, eval (y+w *ᵥ b) P ∂fieldLaw D| ≤ A*R^d*ε := by
  obtain ⟨A,d,h,paid⟩:=box_read_paid (wickStencil P)
  refine ⟨A,d,h,?_⟩
  intro ι ι' _ _ _ _ v w C D c e x y R ε hR hε first second hf hs hg
  rw [←wickStencil_integral v x c P,←wickStencil_integral w y e P]
  exact (paid R hR first second hf hs ε hε hg).2
end YM.Integration.FVA1Physical.Wilson
