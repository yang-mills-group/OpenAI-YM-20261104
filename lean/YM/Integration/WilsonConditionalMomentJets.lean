import YM.Integration.WilsonConditionalMomentBrush
import YM.RG01.Kernel.Read

/-! All directed jets of the true one-step conditional expectation are
charged to its own conditional absolute moment, point by point in the
coarse field. The original angular tariff pays the field directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalMomentJets
open Function Filter Set MeasureTheory Complex Metric Topology Finset Lattice RG Wilson Matrix
open ConnectedActivityE6.Blaze Brush WardBin.Lies RG01.Kernel RG01.Kernel.Wheel
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} (H : History G) {N n m : ℕ} (selected : H.Selected)
    (V : Config G (H.S.side m n)) (hm : m < N)
variable {F : (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n) → ℂ} {b : ℝ}
    (bounded : RG01.Kernel.Bounded (prior G (H.S.side (m+1) n)) F b) (hb : 0 ≤ b)

def income (F : (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n) → ℂ) : ℝ :=
  WilsonConditionalMomentBrush.absolute (expense H N m n V) (prior G (H.S.side (m+1) n)) F

include selected V hm bounded hb in
private theorem price (k : ℕ) (e : Edge (Site (H.S.side m n)) → ℝ) (he : ∀i,0≤e i)
    (small : |H.β N n (m+1)*H.levels.clock.kernel.penalty| *tariff G*(∑i,e i)≤1) :
    Brush k (invoice k (income H (N:=N) (n:=n) (m:=m) V F)) 3
      (quota (expense H N m n V) (channel (H.levels.clock.op m n) (H.β N n (m+1)) e V) (prior G (H.S.side (m+1) n)) F) 0 := by
  let w:=expense H N m n V
  let Z:=channel (H.levels.clock.op m n) (H.β N n (m+1)) e V
  let μ:=prior G (H.S.side (m+1) n)
  let κ:=|H.β N n (m+1)*H.levels.clock.kernel.penalty| *tariff G*(∑i,e i)
  let budget:=invoice k (income H (N:=N) (n:=n) (m:=m) V F)
  have law : Caliber w μ := actual N H selected V hm
  have dep : Wheel μ Z κ := booked (H.levels.clock.op m n) (H.β N n (m+1)) e V (H.levels.blocks m n).branches he
  have signed : Brush k budget (κ+2*κ) (quota w Z μ F) 0 :=
    WilsonConditionalMomentBrush.normalized law dep bounded hb k
  exact signed.climb le_rfl (by dsimp [κ];linarith only [small])

include selected V hm bounded hb in
private theorem germ (l : List (Directions G (H.S.side m n))) (e : Edge (Site (H.S.side m n)) → ℝ)
    (he : ∀i,0≤e i) (hl : ∀a∈l,∀i,‖a i‖≤e i) :
    Germ l.length (fun U=>RG01.Kernel.conditional H N m n U F) V :=
  (RG01.Kernel.angular H selected V hm bounded hb l e he hl).1

include selected V hm bounded hb in
private theorem scaled (l : List (Directions G (H.S.side m n))) (e : Edge (Site (H.S.side m n)) → ℝ)
    (he : ∀ i,0 ≤ e i) (hu : ∀i,e i ≤ 1) (hl : ∀a∈l,∀i,‖a i‖ ≤ e i)
    (small : |H.β N n (m+1)*H.levels.clock.kernel.penalty| * tariff G*(∑i,e i) ≤ 1) :
    ‖leftDerivs (fun U=>conditional H N m n U F) l V‖ ≤
      compensation G l.length (invoice l.length (income H (N:=N) V F)) 3 := by
  let k:=l.length
  let f:=fun U=>conditional H N m n U F
  let w:=expense H N m n V
  let Z:=channel (H.levels.clock.op m n) (H.β N n (m+1)) e V
  let μ:=prior G (H.S.side (m+1) n)
  let W:=quota w Z μ F
  let Y:=fun t=>encoded e V (journey V k l.get t)
  let budget:=invoice k (income H (N:=N) (n:=n) (m:=m) V F)
  have paint : Brush k budget 3 W 0 := price H selected V hm bounded hb k e he small
  obtain ⟨chart,zero,hΛ⟩:=follow V l.get e he hu (fun a i=>hl _ (List.get_mem ..) i) k
  have smooth : Germ k f V := germ H selected V hm bounded hb l e he hl
  have link : f ∘ journey V k l.get = W ∘ Y := by
    funext t
    exact (quotaReal H selected V hm _ _ _ (hΛ t)).symm
  have moved:=chart.pine (g:=W) (x:=0) (show Brush k _ 1 W (Y 0) from zero ▸ paint.trim)
  have eq : leftDerivs f l V=iteratedFDeriv ℝ k (W ∘ Y) 0 cart := by
    rw [← link]
    simpa only [k,List.ofFn_get] using Germ.ordered l.get smooth
  change ‖leftDerivs f l V‖ ≤ _
  rw [eq]
  apply ((iteratedFDeriv ℝ k (W ∘ Y) 0).le_opNorm cart).trans
  have unit (j : Fin k) : ‖cart j‖=1 := by rw [cart,Pi.norm_single,norm_one]
  simp_rw [unit,Finset.prod_const_one,mul_one]
  unfold compensation
  simpa only [budget,mul_assoc] using! moved.order k le_rfl

private theorem scale {n' : Side} (f : Config G n' → ℂ) (l : List (Directions G n'))
    (c : ℝ) (V : Config G n') :
    leftDerivs f (l.map (c • ·)) V = c^l.length • leftDerivs f l V := by
  induction l generalizing V with
  | nil => simp [leftDerivs]
  | cons a l ih =>
    simp_rw [List.map_cons,leftDerivs,ih,smul_smul,mul_comm _ c]
    rw [deriv_fun_const_smul_field,show deriv (fun t=>leftDerivs f l (increment V ((c*t) • a))) 0 = _
      from deriv_comp_mul_left c (fun t=>leftDerivs f l (increment V (t•a))) 0,
      mul_zero,smul_smul,List.length_cons,pow_succ]

include selected V hm bounded hb in
theorem conditional (l : List (Directions G (H.S.side m n))) (e : Edge (Site (H.S.side m n)) → ℝ)
    (he : ∀i,0 ≤ e i) (hl : ∀a∈l,∀i,‖a i‖ ≤ e i) :
    let f:=fun U=>RG01.Kernel.conditional H N m n U F
    Germ l.length f V ∧ ‖leftDerivs f l V‖ ≤
      (bill H e N (m+1))^l.length*compensation G l.length (invoice l.length (income H (N:=N) V F)) 3 := by
  intro f
  refine ⟨germ H selected V hm bounded hb l e he hl,?_⟩
  let t:=bill H e N (m+1)
  let a:=|H.β N n (m+1)*H.levels.clock.kernel.penalty|
  have ha : 0 ≤ a := abs_nonneg _
  have hfee : 0 ≤ tariff G := zero_le_one.trans (fee G)
  have hsum : 0 ≤ ∑i,e i := Finset.sum_nonneg fun i _=>he i
  have h1 : 1 ≤ t := by
    change 1 ≤ (1+a*tariff G)*(1+∑i,e i)
    nlinarith only [ha,hfee,hsum,mul_nonneg ha hfee,mul_nonneg (mul_nonneg ha hfee) hsum]
  have positive := zero_lt_one.trans_le h1
  let v i:=e i/t
  have hv (i) : v i ≤ 1 := (div_le_one positive).2 ((Finset.single_le_sum (s:=univ)
    (f:=e) (fun i _=>he i) (mem_univ i)).trans (by
      change _ ≤ (1+a*tariff G)*(1+∑i,e i)
      nlinarith only [mul_nonneg ha hfee,mul_nonneg (mul_nonneg ha hfee) hsum]))
  have lifted : ∀x∈l.map (t⁻¹ • ·),∀i,‖x i‖ ≤ v i := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
    intro i
    change ‖(t⁻¹ • y) i‖ ≤ e i/t
    rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le),div_eq_mul_inv,mul_comm]
    exact mul_le_mul_of_nonneg_right (hl _ hy i) (inv_nonneg.mpr positive.le)
  have envelope : a*tariff G*(∑i,v i) ≤ 1 := by
    unfold v
    rw [← Finset.sum_div,← mul_div_assoc,div_le_one positive]
    change _ ≤ (1+a*tariff G)*(1+∑i,e i)
    nlinarith only [mul_nonneg ha hfee,hsum]
  have shrunk:=scaled H selected V hm bounded hb (l.map (t⁻¹ • ·)) v
    (fun i=>div_nonneg (he i) positive.le) hv lifted envelope
  rw [List.length_map,scale,norm_smul] at shrunk
  have clean : ‖(t⁻¹)^l.length‖=(t^l.length)⁻¹ := by rw [inv_pow,Real.norm_of_nonneg]; positivity
  rw [clean,inv_mul_le_iff₀ (pow_pos positive _)] at shrunk
  exact shrunk

end YM.Integration.WilsonConditionalMomentJets
end
