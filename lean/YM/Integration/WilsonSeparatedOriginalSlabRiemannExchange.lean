import YM.Integration.WilsonSeparatedOriginalSlabRiemann

/-! Uniform honest joint readings may be inserted into the signed physical quadrature using only its finite mass. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabRiemannExchange
open Function Filter Set Metric MeasureTheory Wilson Lattice Extraction WilsonSeparatedOriginalSlabRiemann
open scoped Topology BigOperators Classical
variable {n:ℕ}(S:Schedule)

theorem mass (f:Extraction.Order)(φ:Points n→ℂ)(cont:Continuous φ)(compact:HasCompactSupport φ):
    ∃M:ℝ,0≤M ∧ ∀ᶠ k:ℕ×ℕ in f.fuse,(S.a k.1)^(4*n)*∑x:Var S n k.1 k.2,‖φ (centre S x)‖≤M:=by
  let h (x:Points n):ℂ:=‖φ x‖
  let A:ℂ:=∫x,h x
  have current:=tested S f h (Complex.continuous_ofReal.comp cont.norm) (compact.norm.comp_left (g:=Complex.ofReal) Complex.ofReal_zero)
  refine ⟨‖A‖+1,by positivity,?_⟩
  filter_upwards [current.norm.eventually_lt_const (show ‖A‖<‖A‖+1 by linarith)] with k hk
  change ‖(S.a k.1:ℂ)^(4*n)*∑x:Var S n k.1 k.2,(‖φ (centre S x)‖:ℂ)‖<‖A‖+1 at hk
  rw [←Complex.ofReal_pow,←Complex.ofReal_sum,←Complex.ofReal_mul,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (pow_nonneg (S.a_pos _).le _) (Finset.sum_nonneg fun _ _=>norm_nonneg _))] at hk
  exact hk.le

theorem observed (f:Extraction.Order){l:Filter (ℕ×ℕ)}(law:l≤f.fuse)(φ F:Points n→ℂ)(cont:Continuous φ)(compact:HasCompactSupport φ)(joint:Continuous (fun x=>φ x*F x))
    (Z:(k:ℕ×ℕ)→Var S n k.1 k.2→ℂ)
    (uniform:∀δ:ℝ,0<δ→∀ᶠ k:ℕ×ℕ in l,∀x:Var S n k.1 k.2,φ (centre S x)≠0→‖Z k x-F (centre S x)‖≤δ):
    Tendsto (fun k:ℕ×ℕ=>(S.a k.1:ℂ)^(4*n)*∑x:Var S n k.1 k.2,φ (centre S x)*Z k x) l (𝓝 (∫x,φ x*F x)):=by
  obtain ⟨M,mp,bound⟩:=mass S f φ cont compact
  have small:Tendsto (fun k:ℕ×ℕ=>(S.a k.1:ℂ)^(4*n)*∑x:Var S n k.1 k.2,φ (centre S x)*(Z k x-F (centre S x))) l (𝓝 0):=by
    apply Metric.tendsto_nhds.mpr;intro ε ep
    let δ:=ε/(M+1)
    have dp:0<δ:=div_pos ep (by linarith only [mp])
    filter_upwards [bound.filter_mono law,uniform δ dp] with k cash price
    have pointwise (x:Var S n k.1 k.2):‖φ (centre S x)*(Z k x-F (centre S x))‖≤‖φ (centre S x)‖*δ:=by
      by_cases h:φ (centre S x)=0
      · simp [h]
      rw [norm_mul];gcongr;exact price x h
    rw [dist_zero_right,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (S.a_pos _).le]
    calc (S.a k.1)^(4*n)*‖∑x:Var S n k.1 k.2,φ (centre S x)*(Z k x-F (centre S x))‖
        ≤ (S.a k.1)^(4*n)*∑x:Var S n k.1 k.2,(‖φ (centre S x)‖*δ):=mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>pointwise i))) (pow_nonneg (S.a_pos _).le _)
      _ ≤ M*δ:=by rw [←Finset.sum_mul,←mul_assoc];gcongr
      _ < ε:=by dsimp [δ];rw [mul_div_assoc',div_lt_iff₀ (by linarith only [mp])];nlinarith
  have approx:=(tested S f (fun x=>φ x*F x) joint compact.mul_right).mono_left law
  simpa only [←mul_add,←Finset.sum_add_distrib,←mul_add,sub_add_cancel,zero_add] using small.add approx

end YM.Integration.WilsonSeparatedOriginalSlabRiemannExchange
