import YM.Pert.Kinetic.Wave
import YM.Push.ABSOLUTE_SUMS.Animals
/-! The E price of a slow transverse wave. Retains one anchored mass at its true site. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} (c : G.Color) (hc : ‖c‖=1) (b : Bool) {i j : Axis}
    {p : BudgetPoint} {δ : ℝ} {X : Support n} {f : Pot G n} {u : ℝ} (hG : G.Simple) (hf : p.Regular X f)
include hG hf
lemma polar_price (a d : Directions G n) {o : Site n} (ha : p.dirBound o a) (hd : p.dirBound o d)
     (h : p.supBounds o X f u) :
     |logHessian f a d| ≤ 3*u := by
   have k (v : Directions G n) (hv : p.dirBound o v) : |logHessian f v v| ≤ u := by rw [hessian_diag hG hf,←Real.norm_eq_abs]; exact h.2 1 (Next.Foundations.one_healthy _ _ p.threshold_pos.le) _ (by change 2≤p.order; linarith only [p.order_ge]) (by simp_all)
   have kb : p.dirBound o ((2:ℝ)⁻¹ • (a+d)) := fun e => by
      change ‖(2:ℝ)⁻¹ • (a e+d e)‖ ≤ _; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(2:ℝ)⁻¹)]; linarith only [norm_add_le (a e) (d e),ha e,hd e]
   have hh := k _ kb
   simp only [hessian_eq,map_smul, smul_apply,map_add,add_apply] at hh
   rw [←hessian_eq,←hessian_eq,←hessian_eq,← hessian_eq,hessian_symm hf d a] at hh
   simp only [smul_eq_mul] at hh
   exact abs_le.mpr ⟨by linarith only [(abs_le.mp hh).1,(abs_le.mp (k a ha)).2,(abs_le.mp (k d hd)).2],by linarith only [(abs_le.mp hh).2,(abs_le.mp (k a ha)).1,(abs_le.mp (k d hd)).1]⟩
omit hG hf in
lemma loose_dir (o : Site n) (a : Directions G n) {l : ℝ} (hl : 0<l) (k : ℕ) (hk : k≤p.power)
      (h : ∀ e : Edge (Site n), ‖a e‖ ≤ l*(1+(separation e.1 o:ℝ))^k) : p.dirBound o ((l/p.threshold)⁻¹ • a) := by
   intro e; change ‖(l/p.threshold)⁻¹ • a e‖ ≤ _
   have hp:=p.threshold_pos
   rw [norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<(l/p.threshold)⁻¹ from by positivity),← div_eq_inv_mul,div_div_eq_mul_div,div_le_iff₀ hl]
   calc _ ≤ l*(1+(separation e.1 o:ℝ))^k * p.threshold := by gcongr; exact h e
        _ ≤ l*(1+(separation e.1 o:ℝ))^p.power * p.threshold := by gcongr; change (1:ℝ) ≤ 1+(separation ..); exact le_add_of_nonneg_right (Nat.cast_nonneg _)
        _ = _ := by ring
lemma scaled_price {o : Site n} (h : p.supBounds o X f u) (a d : Directions G n) {r t : ℝ} (hr : 0<r) (ht : 0<t) (ha : p.dirBound o ((r/p.threshold)⁻¹ • a)) (hd : p.dirBound o ((t/p.threshold)⁻¹ • d)) :
    |logHessian f a d| ≤ r*t*(3*u)/p.threshold^2 := by
   have hh := polar_price hG hf _ _ ha hd h; have he := p.threshold_pos
   suffices k : |logHessian f a d| ≤ ((r/p.threshold) * (t/p.threshold))*(3*u) by convert k using 1; ring
   have hh := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ r/p.threshold * (t/p.threshold))
   rw [← abs_of_pos (show 0 < r/p.threshold * (t/p.threshold) by positivity), ← abs_mul,hessian_eq] at hh
   simp only [map_smul,smul_apply] at hh
   rw [← hessian_eq, smul_eq_mul,smul_eq_mul] at hh
   have e : ∀ x:ℝ, r / p.threshold * (t / p.threshold) * ((t / p.threshold)⁻¹ * ((r / p.threshold)⁻¹ * x))=x := fun x => by field_simp
   rwa [e, abs_of_pos (show 0 < r/p.threshold * (t/p.threshold) from by positivity)] at hh
omit hG hf in
lemma poly_gate {sval : ℝ} {orderM : ℕ} (hs : 0 ≤ sval) : Real.exp sval ≥ sval^orderM / (orderM.factorial : ℝ) := -- hm not needed
    (Finset.single_le_sum (f:=fun i=> sval^i / (Nat.factorial i:ℝ)) (fun _ _=>by positivity) (Finset.mem_range.mpr (show orderM<orderM+1 from by omega))).trans (Real.sum_le_exp_of_nonneg hs (orderM+1))

def geomE (p : BudgetPoint) := 1/p.threshold^2 * (((2*Real.pi)+2)*3 + (((100*(4*(p.B:ℝ)+2) / ((2*Real.pi)*p.supportExponent))^3)*18))
include hc
lemma sparse_fee (o : Site n) (a : Directions G n) (hn : 4 ≤ n.val) (hX : ¬Nonwrapping X o) (ho : o ∈ X) (h : p.supBounds o X f u) (hd : p.dirBound o (p.threshold • a)) :
 |logHessian f a a| ≤ (Full.mesh n)^3 * (100*(4*(p.B:ℝ)+2)/((2*Real.pi)*p.supportExponent))^3 *18 /p.threshold^2 * p.mass X u := by
    let cost : ℝ := coverNumber p.B X
    have ht : (n.val:ℝ) ≤ 100 * (4*(p.B:ℝ)+2)*cost := by
       obtain ⟨x,hx⟩ := Classical.not_forall.mp (show ¬∀ x∈X,10*separation x o<n.val from hX)
       obtain ⟨hx,h₂⟩:= not_forall.mp hx
       have he:= Corona.extent X p.B hx ho
       have hv : (n.val:ℝ) ≤ 10*(cost*(4*(p.B:ℝ)+2) + 2*(p.B:ℝ)) := by dsimp only [cost]; exact_mod_cast ((Nat.not_lt.mp h₂).trans (Nat.mul_le_mul_left _ he))
       have hp0 : 0 < coverNumber p.B X := (Push.AbsoluteSums.Animals.price_pos p.B X).2 ⟨o,ho⟩
       have he : 1 ≤ cost := by dsimp only [cost]; exact_mod_cast (show 1≤coverNumber p.B X from hp0)
       nlinarith only [hv,he, mul_le_mul_of_nonneg_left he (Nat.cast_nonneg p.B)]
    let t := p.supportExponent*cost
    have hL := p.threshold_pos; have hT : 0 < (2*Real.pi) := by positivity
    have hE:= poly_gate (sval:=t) (orderM:=3) (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg ..)) -- fix
    have h1 : 1 ≤ Full.mesh n * (100*(4*(p.B:ℝ)+2)/( (2*Real.pi)*p.supportExponent)) * t := by
       dsimp only [Full.mesh,t]
       have he := p.exponent_pos
       calc 1 ≤ (100*(4*(p.B:ℝ)+2)*cost)/(n.val:ℝ) := (le_div_iff₀ (Full.val_pos n)).2 (by simpa only [one_mul] using ht)
            _ = _ := by field_simp
    have h0 (v:ℝ)(hr:0<v): (1/v)⁻¹=v := by field_simp
    have hp := scaled_price hG hf h a a zero_lt_one zero_lt_one (h0 p.threshold hL |> fun he => he.symm ▸ hd) (h0 p.threshold hL |> fun he => he.symm ▸ hd)
    refine hp.trans ?_
    unfold BudgetPoint.mass; change _ ≤ _*(Real.exp t*u)
    have hf : 1 ≤ (Full.mesh n)^3 * (100*(4*(p.B:ℝ)+2)/((2*Real.pi)*p.supportExponent))^3*t^3:= by rw [←mul_pow,←mul_pow];dsimp only [t] at h1; dsimp only [t]; nlinarith only [(pow_le_pow_left₀ (by norm_num) h1 3)]
    have hh : t^3 ≤ 6*Real.exp t := by norm_num [Nat.factorial] at hE;linarith
    have hF : 1 ≤ (Full.mesh n)^3 * (100*(4*(p.B:ℝ)+2)/((2*Real.pi)*p.supportExponent))^3*(6*Real.exp t) := hf.trans (mul_le_mul_of_nonneg_left hh (by have hh2:=Full.mesh_pos (n:=n); have hep:=p.exponent_pos; positivity))
    have he := mul_le_mul_of_nonneg_left hF h.1
    conv_rhs => rw [div_mul_eq_mul_div]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith only [he] -- adjust
end YM.Pert.Kinetic
