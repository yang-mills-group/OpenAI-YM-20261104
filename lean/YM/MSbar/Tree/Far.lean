import YM.Next.RANK.Radian.Allowance

/-!
# An IR summation-by-parts estimate

The quadrature form of the periodic Fourier estimates in Radian/TK tolerates
length/n in its error. That is not enough for image lines with length
comparable to the size of the torus. We prove an estimate on the previous
sharp symbol domain (`Lip`, one pole at the origin in gradient bound)
that works also when the phase is such a fraction. Use the existing volume
normalization, compatible with lines reading the unsmoothed torus covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree.Far
open Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff NNReal RealInnerProductSpace FourierTransform
open Lattice Next.Rank Next.Rank.CellsInt Next.Rank.Radian

variable {n : Side} {k : ℕ}

def advance (n : Side) (i : Axis) := (n.val:ℝ)⁻¹ • basis i

lemma index_advance (i : Axis) (x : E4) : mark n (x+advance n i)= mark n x+step i := by
  funext j; unfold mark advance; let s := (n.val:ℝ)⁻¹; have hs : s≠0:= (positive n).ne'; by_cases h : j=i
  · subst j
    simp only [PiLp.add_apply,PiLp.smul_apply,basis_eq, ↓reduceIte,smul_eq_mul,mul_one,add_div]
    rw [div_self hs]; simp
  simp [h]

lemma follow (i : Axis) (x : E4) : addr n (mark n (x+advance n i)) = addr n (mark n x)+advance n i:= by
  rw [index_advance,addr,mapZ_step,smul_add]; rfl

private theorem integrated_price {F : E4→ℂ} {R s : ℝ} (h : Lip F k R) (hR : 0≤R) (hs : 0<s) (hs' : s≤1) (x y : E4) (hp : ‖y-x‖ ≤ 5*s) (hx : x≠0) :
    let W:ℝ := k+6; let B := Maxwell.normal⁻¹ * Real.exp (W^2)*W
    ‖F x - F y‖ ≤ 20*R* B * s * ‖liturgy 1 x‖ := by
  intro W B; by_cases he : ‖x‖ ≤ W
  · have ht : 0<W:= by unfold W; positivity
    refine (skin h hR _ _ _ (by positivity) hp (show x∈Maxwell.away from hx)).trans ?_
    have hB := fern x ht (norm_pos_iff.mpr hx) he
    nlinarith only [mul_le_mul_of_nonneg_right hB (mul_nonneg hR hs.le)] -- ring
  have hx' := norm_sub_norm_le x y; rw [norm_sub_rev] at hx'
  rw [h.event x (by unfold W at *; linarith), h.event y (by unfold W at *; linarith), sub_zero,norm_zero]; have := Maxwell.normal_pos; unfold B W; positivity

lemma bill (k : ℕ) : ∃ C : ℝ,0 ≤ C ∧ ∀ F B, 0≤B → Lip F k B → ∀ (z:E4) (n:Side) (i:Axis),
    ‖1-wave z (advance n i)‖ * ‖scansP n (fun x => wave z x * F x) k‖ ≤ C*B*(n.val:ℝ)⁻¹:= by
  let W:ℝ:= k+6; let K:= Maxwell.normal⁻¹ * Real.exp (W^2)*W
  have he:0≤K:= by unfold K W; have := Maxwell.normal_pos; positivity
  let J:=∫ x:E4, ‖liturgy 1 x‖
  have hJ:0 ≤ J := integral_nonneg fun x=> norm_nonneg _
  refine ⟨40*K*J,by positivity,fun F B hB h z n i=>?_⟩
  let y (x:E4):= addr n (mark n x); let Y (x:E4):= wave z (y x) * F (y x); let d:= advance n i; let r:=(n.val:ℝ)⁻¹; have hr:0<r:=positive n; let c:=wave z d
  have hTe : eventP k (fun x=> wave z x* F x):= fun i hi=> by dsimp only; rw [h.event i hi,mul_zero]
  obtain ⟨hi,hT⟩:= grid_born n (fun x=>wave z x* F x) k hTe; rw [← norm_mul,←hT]
  let T x:= Y (x+d)-c*Y x
  have h0 : Integrable (fun x=> Y (x+d)):= by
    exact (measurePreserving_add_right volume d).integrable_comp_of_integrable hi
  rw [show (1-c)*(∫ x,Y x)=∫ x,T x from ?_]; swap
  · unfold T; rw [integral_sub h0 (hi.const_mul c),integral_add_right_eq_self,integral_const_mul]; ring
  let g(x:E4):=40*B*K*r*‖liturgy 1 x‖
  have hh : Integrable g:=(liturgy_int (b:=1) (by norm_num)).norm.const_mul _
  refine (norm_integral_le_integral_norm ..).trans ((integral_mono_ae (h0.sub (hi.const_mul c)|>.norm) hh (lit_ae.mono fun x hx=>?_)).trans_eq ?_)
  · let v x:= y (x+d)
    have he': T x=c*wave z (y x)*(F (v x)-F (y x)):= by
      have hh : wave z (v x)=c*wave z (y x):= by
        rw [show v x= y x+d from follow _ _,wave]; simp [wave,c, inner_add_left, AddChar.map_add_eq_mul,mul_comm]
      change wave z (v x)*_ - _= _; rw [hh];unfold Y; ring
    have hs:r≤1:= inv_le_one_of_one_le₀ (by exact_mod_cast n.property)
    have hy(x:E4): ‖y x-x‖ ≤4*r:= by simpa only [← dist_eq_norm] using rock (c:=n) x
    have hp:‖v x-x‖≤5*r:=by
      rw [show v x=y x+d from follow _ _]; rw [show y x+d-x = (y x-x)+d from by abel]
      apply (norm_add_le ..).trans;change _+‖r • basis i‖ ≤_;rw [norm_smul,basis_norm,Real.norm_of_nonneg hr.le,mul_one]; linarith only [hy x]
    have hx1 := integrated_price h hB hr hs x (v x) hp hx
    have hx2 := integrated_price h hB hr hs x (y x) (le_trans (hy _) (by linarith only [hr])) hx
    change ‖T x‖ ≤ g x; rw [he',norm_mul,norm_mul,price_wave,price_wave,one_mul,one_mul]
    apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (F x) _); rw [norm_sub_rev (F (v x))]
    dsimp only [g]; linarith only [hx1,hx2]
  unfold g J; rw [integral_const_mul]; ring

-- phase-price domain for a coordinate between eighth and three quarters of a torus
-- (suffices for x_* in the sector used in T:kcert, with some margin).
private theorem phase_budget : ∃ L:ℝ,0<L ∧ ∀ x:ℝ, x∈ Icc (1/8:ℝ) (3/4) → L ≤ ‖(1:ℂ)- (Real.fourierChar x:ℂ)‖:= by
  let S:= Icc (1/8:ℝ) (3/4); let f(x:ℝ):= ‖(1:ℂ)- (Real.fourierChar x:ℂ)‖; have hf : Continuous f:=by unfold f; fun_prop
  obtain ⟨x,hx,h⟩:= isCompact_Icc.exists_isMinOn (show S.Nonempty from ⟨1/2,by constructor <;> norm_num⟩) hf.continuousOn
  refine ⟨_,norm_pos_iff.mpr ?_, fun _ hi=> h hi⟩; intro H
  obtain ⟨i,hi⟩ := Complex.exp_eq_one_iff.mp (show ((Real.fourierChar x):ℂ)=1 from (sub_eq_zero.mp H).symm)
  obtain ⟨ha,hb⟩:= hx
  rcases lt_or_ge i 1 with ht|ht
  all_goals
    have hi := congr_arg Complex.im hi; simp [Complex.mul_im, Complex.mul_re] at hi; first
    | nlinarith only [hi, Real.pi_pos, ha, (show (i:ℝ)≤0 from (by exact_mod_cast (show i ≤0 from (by omega))))]
    | nlinarith only [hi,Real.pi_pos,hb,(show (1:ℝ) ≤ i from by exact_mod_cast ht)]

theorem far_bound {k : ℕ} {F : E4→ℂ} {B : ℝ} (hB : 0≤B) (h : Lip F k B) :
    ∃ C:ℝ, 0≤C ∧ ∀ (z:E4) (i:Axis) (n:Side), z i / n.val ∈ Icc (1/8:ℝ) (3/4) →
      ‖scansP n (fun x => wave z x* F x) k‖ ≤ C/n.val:= by
  obtain ⟨L,hL,H⟩:= phase_budget; obtain ⟨A,ha,hA⟩:= bill k
  refine ⟨A*B/L, by positivity, fun z i n hz=>?_⟩; apply le_of_mul_le_mul_left (a:=L) _ hL
  specialize hA _ _ hB h z n i
  have hx : L ≤ ‖1-wave z (advance n i)‖:= by unfold wave advance; rw [real_inner_smul_left,inner_neg_right,basis_inner,mul_neg,neg_neg, ←div_eq_inv_mul]; exact H _ hz
  refine (le_trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) hA).trans_eq (by field_simp)
end YM.MSbar.Tree.Far
