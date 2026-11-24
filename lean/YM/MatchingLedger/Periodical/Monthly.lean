import YM.MatchingLedger.Periodical.Identity

/-!
# Local Taylor residual on SD integrand

At any unit lemma use size arguments, not a torus-dependent radius. Derivative horizon includes the
Taylor tail derivative itself. A new currency on the *local* stencils at the posterior.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric PertExtension.Series
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset

section rays
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable (k : ℕ)(x:E) {t:ℝ} (ht:0<t)
local notation "J" => Set.Icc 0 t
include ht
-- adapt radial deposition but no torus-cost selection so preserve its known degree. Also useful for
-- finite smooth stencils (any horizon carrying enough derivatives, no analytic closed patch needed).
lemma annual {f : E→ℝ}{u : ℝ}(h : ∀ r∈J, ContDiffAt ℝ (↑(k+1):ℕ∞ω) f (r • x))
    (hp : ∀ r∈J, ‖iteratedFDeriv ℝ (k+1) f (r • x)‖ ≤ u) :
    ‖f (t • x)- ∑ i∈ Finset.range (k+1), t^i*Radial.jet f i x‖ ≤ u* ‖x‖^(k+1)*t^(k+1):=by
  let N := k+1; let φ(r:ℝ):= f (r • x)
  have hf (i : ℕ) (hk : i≤N)(r)(hr:r∈J) : ContDiffAt ℝ i φ r := ((h r hr).of_le (show (↑i:ℕ∞ω) ≤ (↑N:ℕ∞ω) by exact_mod_cast hk)).comp (f:=fun t : ℝ=>t • x) r (contDiffAt_id.smul (contDiffAt_const (c:=x)))
  have hy (i : ℕ) (hk : i ≤ N) (r) (hr : r ∈ J) :
      iteratedDerivWithin i φ J r = iteratedFDeriv ℝ i f (r • x) (fun _=>x):=by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc ht) (hf i hk r hr) hr, ←iteratedDeriv_eq_iteratedFDeriv]; obtain ⟨V,hV,hs,he⟩:= (h r hr).contDiffOn' (m:=N) (by exact_mod_cast (le_rfl : (N:ℕ∞ω)≤ N)) (by simp); exact Radial.radial_iteratedDeriv x r i hV hs (by simpa using! he.of_le (show (↑i:ℕ∞ω) ≤ N by exact_mod_cast hk))
  have hv := taylor_mean_remainder_bound (n:=k) (x:=t) (C:=u*‖x‖^N) ht.le (f:=φ) (by intro x hx; simpa only [N,Nat.cast_add,Nat.cast_one] using! ((hf N le_rfl x hx).contDiffWithinAt (s:=J))) (right_mem_Icc.mpr ht.le) ?_; swap
  · intro r hr; rw [hy _ le_rfl r hr]; apply (ContinuousMultilinearMap.le_of_opNorm_le (hp r hr) _).trans_eq; simp [N]
  have hm : taylorWithinEval φ k J 0 t=∑ i∈ Finset.range (k+1),t^i * Radial.jet f i x := by
    rw [taylor_within_apply]; refine Finset.sum_congr rfl (fun i hi=>?_); rw [hy _ ((Finset.mem_range.mp hi).le) _ (left_mem_Icc.mpr ht.le),zero_smul,sub_zero]; change _ * _= _ * _; simp only [Radial.jet]; ring
  rw [hm,sub_zero] at hv; have hd : (1:ℝ) ≤ k.factorial:=by exact_mod_cast k.factorial_pos
  have hp: 0≤u := (norm_nonneg _).trans (hp _ (right_mem_Icc.mpr ht.le))
  exact hv.trans ((div_le_iff₀ (zero_lt_one.trans_le hd)).mpr (le_mul_of_one_le_right (by positivity) hd))
end rays

section bench

variable {ι : Type} [Fintype ι][DecidableEq ι]
variable {k n : ℕ}{f : Chip ι → ℝ}{x : Chip ι}{M r t : ℝ}
    (ht:0<t) (hpos:0≤r) (h:∀ x:Chip ι,‖x‖≤r → Allows n f x M) (hx:‖t • x‖≤r) (i : ι)

lemma compass {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {u r t : ℝ}{x:E}(h:‖t • x‖≤ r)(hu:u∈Set.Icc 0 t) : ‖u • x‖≤r:=by rw [norm_smul_of_nonneg (hu.1.trans hu.2)] at h; rw [norm_smul_of_nonneg hu.1]; exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)).trans h

include ht hx h
private lemma ear (hk:k+2 ≤ n) :
    ‖Books.derivative f i (t • x) - ∑ l∈ Finset.range (k+1), t^l * (read x) (pderiv i (packet f (l+1)))‖ ≤ M * ‖x‖^(k+1)*t^(k+1):=by
   have he : ContDiffAt ℝ ω f 0:= (h 0 (norm_zero.trans_le ((norm_nonneg _).trans hx))).analytic
   simp_rw [packet_gradient he, packet_read]; have hf (v) (hv:v∈Set.Icc 0 t) : Allows (k+1) (Books.derivative f i) (v • x) M:=highlighted ((h _ (compass hx hv)).order hk) i
   exact annual k x ht (fun v hv=>(hf v hv).analytic.of_le le_top) (fun v hv=>(hf v hv).norm_le _ le_rfl)

-- sum incl Hessian (k=0). hp required through n+3 for RHS slope small.
def sky (k : ℕ) (t : ℝ) (f : Chip ι → ℝ)(i : ι)(x : Chip ι) := ∑ l∈ Finset.range (k+1), t^l * (read x) (pderiv i (packet f (l+1+1)))
def hat (k : ℕ) (t : ℝ)(f : Chip ι → ℝ)(i : ι)(x : Chip ι) := ∑ l∈ Finset.range k, t^(l+1) * (read x) (pderiv i (packet f (l+1)))
lemma concern (hk:k+3 ≤ n)(hl:fderiv ℝ f 0=0) :
    ‖t⁻¹ * Books.derivative f i (t • x) - sky k t f i x‖ ≤ M* ‖x‖^(k+2) * t^(k+1):= by
  let g:= t⁻¹; let v:= Books.derivative f i (t • x); let p:= ∑ l∈Finset.range (k+1+1), t^l * (read x) (pderiv i (packet f (l+1)))
  have he := ear (k:=k+1) ht h hx i hk
  have hf : ContDiffAt ℝ ω f 0:= (h 0 (norm_zero.trans_le ((norm_nonneg _).trans hx))).analytic
  have hl' : p=t * sky k t f i x:=by
    unfold p; rw [Finset.sum_range_succ' _ (k+1),pow_zero,one_mul,packet_gradient hf,packet_read, Radial.jet_zero, Books.derivative,hl]; simp only [_root_.zero_apply, add_zero]; unfold sky; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [pow_succ']; ring
  rw [show t⁻¹ * Books.derivative _ _ _ - _= t⁻¹*(v-p) by rw [hl']; unfold v; field_simp]
  rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr ht).le]; refine (mul_le_mul_of_nonneg_left he (inv_pos.mpr ht).le).trans_eq ?_; rw [pow_succ (a:=t)]; field_simp
lemma concerns (hk:k+2 ≤ n):
    ‖t * Books.derivative f i (t • x) - hat k t f i x‖ ≤ M* ‖x‖^k *t^(k+1):= by
  cases k with
  | zero =>
    rw [hat,Finset.sum_range_zero,sub_zero,norm_mul,Real.norm_of_nonneg ht.le]; simp only [pow_zero,zero_add,pow_one,mul_one]; rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (highlighted (n:=0) ((h _ hx).order (by omega)) i).value ht.le
  | succ k=>
    let p:=∑ l∈ Finset.range (k+1), t^l * (read x) (pderiv i (packet f (l+1)))
    have hh : hat (k+1) t f i x= t*p:=by unfold p hat; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [pow_succ',mul_assoc]
    rw [hh,← mul_sub,norm_mul,Real.norm_of_nonneg ht.le]; refine (mul_le_mul_of_nonneg_left (ear (k:=k) ht h hx i (by omega)) ht.le).trans_eq ?_; rw [pow_succ t (k+1)]; ring

end bench

variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB:S.patch.Branches S.kernel G)
    {A : ChartRatio G} (i : Needle F G)(k : ℕ) {n : ℕ}(H : Budget G A n)(X:Chip (Meter F G)){t:ℝ}(ht:0<t)(hk:k+3≤n)
local notation "g" => t⁻¹
local notation "P" => S.patch
local notation "M" => H.income S.patch S.kernel
local notation "C" => H.space S.patch S.kernel
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)

-- unheld currents (formal order series, incl Hess term).

def lead (A : ChartRatio G)(u:ℝ) : Poly (Meter F G):= ∑ l∈ Finset.range (k+1), u^l • (pderiv I (wide F s A l))

omit H in
lemma shift (A : ChartRatio G)(t:ℝ): lead F s i k A t= (∑ z∈Finset.range (k+1),t^z • (pderiv I (tip F (G:=G) s (z+1+1)))) - ∑ z∈Finset.range k,t^(z+1) • (pderiv I (flow F A (z+1))):= by
  unfold lead; rw [Finset.sum_range_succ',Finset.sum_range_succ' (fun z : ℕ=> t^z • pderiv I (tip F s _))]; simp only [wide,pow_zero,one_smul]; simp_rw [_root_.map_sub,smul_sub,Finset.sum_sub_distrib]; abel

-- hk not needed for local from port book
include H hB
lemma sober (t:ℝ) : read X (lead F s i k A t)= (∑ z∈D, sky k t (dues S F G s z) I X)-(∑ z∈D, hat k t (salary F A z) I X):=by
  let p:= dues S F G s; let q:= salary F A
  have he (u : ℕ) : pderiv I (tip F s u)=∑ z∈D, pderiv I (packet (p z) u):= clip_indices F _ (dues_port S F hB s) (H.duty F (issued_script F H) s) I
  have hf (u : ℕ) : pderiv I (flow F A u)=∑ z∈D,pderiv I (packet (q z) u):= clip_indices F _ (salary_port F A) (H.issued F (issued_script F H)) I
  rw [shift]; unfold sky hat; simp_rw [he,hf,_root_.map_sub,_root_.map_sum,_root_.map_smul,smul_eq_mul,_root_.map_sum, Finset.mul_sum] -- double?
  congr 1 <;> exact Finset.sum_comm -- ?

include ht
-- post-L kernel, n includes derivative bills. uniform M used.
lemma ruling (hx:‖g • X‖≤C) (h : k+3 ≤ n) (Z : ℝ) (hZ:1≤Z) (hv:‖X‖≤ Z):
    ‖g*distill F s A t i (g • X) - read X (lead F s i k A g)‖ ≤ park (belt P) * (2*M* Z^(k+2)) * g^(k+1) := by
  let a:= t⁻¹; have ha : 0<a:= inv_pos.mpr ht
  have hp := zero_le_one.trans (H.income_one P S.kernel)
  let z:= a • X; let v:= dues S F G s; let w:= salary F A
  let f(x:Chip (Meter F G)):= ∑ j∈D,v j x; let q(x:Chip (Meter F G)):= ∑ j∈D,w j x
  have he : distill F s A t i z=t^2 * ∑ j∈D, Books.derivative (v j) I z - ∑ j∈D, Books.derivative (w j) I z := by
    have hF(j) : DifferentiableAt ℝ (v j) z := (H.duty F hx s j).analytic.differentiableAt (by simp)
    have hW(j) : DifferentiableAt ℝ (w j) z := (H.issued F hx j).analytic.differentiableAt (by simp)
    have hh : HasFDerivAt (sat F s A t i) _ z := ((HasFDerivAt.fun_sum fun j (_:j∈D)=> (hF j).hasFDerivAt).const_mul (t^2)).sub (HasFDerivAt.fun_sum (fun j (_:j∈D)=> (hW j).hasFDerivAt))
    unfold distill Books.derivative; rw [hh.fderiv]; simp
  let W:= M * Z^(k+2) * a^(k+1)
  let p(j):= a⁻¹ * Books.derivative (v j) I z - sky k a (v j) I X
  let b(j):= a * Books.derivative (w j) I z - hat k a (w j) I X
  have hD : a*t^2=a⁻¹:= by unfold a; field_simp
  have hz : a*distill F s A t i z - read X (lead F s i k A a)= (∑ j∈D,p j) - ∑ j∈D,b j:= by
    rw [he,mul_sub a,← mul_assoc,hD,sober F s hB i k H X]; unfold p b v w; rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum,Finset.mul_sum]; ring
  have hT(j) : ‖p j‖≤ W := (concern (k:=k) ha (fun _ hp=> H.duty F hp s j) hx I h (dues_still F s hB j)).trans (by unfold W a; gcongr)
  have hB(j) : ‖b j‖≤ W := (concerns (k:=k) ha (fun _ hp=> H.issued F hp j) hx I (by omega)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hv _).trans (pow_le_pow_right₀ hZ (by omega))) hp) (pow_nonneg ha.le _)) -- variable hB shadow
  have hW: 0≤ W:= by unfold W; positivity [zero_le_one.trans hZ]
  have hA(f:Site c→ℝ)(h:∀ j,‖f j‖≤W): ‖∑ j∈D,f j‖≤park (belt P)*W:= by
    apply (norm_sum_le ..).trans ((Finset.sum_le_sum («g»:=fun _=> W) (fun i _=> h i)).trans ?_); rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by unfold park; exact_mod_cast mag (atlas F I) (belt P)) hW
  change ‖a * distill F s A t i z- _‖≤ _; rw [hz]; apply (norm_sub_le ..).trans; exact (add_le_add (hA p hT) (hA b hB)).trans_eq (by unfold W a; ring)
end YM.MatchingLedger.Periodical
