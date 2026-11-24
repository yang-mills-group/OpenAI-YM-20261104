import YM.Contact.OrderLoss
import YM.Contact.Power

/-! Annular tests for the distributional root operation. These lemmas concern test geometry,
not diagrams/Wilson source estimates. `s` is the Taylor subtraction scale **in test units**
(i.e. physical subtraction-length divided by largest cluster test-length), `r` is band radius
in the same units. -/

noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
variable (E : Type*) [NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
set_option quotPrecheck false
local notation "V!"=>{x : E | (1/2:ℝ)≤‖x‖∧ ‖x‖≤2}
def filterU (x : E) : ℝ:=chi 1 x-chi 1 ((2:ℝ) • x)
omit [FiniteDimensional ℝ E] in
lemma filter_support(x:E)(hx:x∉V!):filterU E x=0:=by
     unfold filterU
     by_cases ht:2<‖x‖
     · rw [chi_lt_zero 1 (by norm_num) _ (by linarith),chi_lt_zero 1 (by norm_num) _ (by rw[norm_smul_of_nonneg zero_le_two]; linarith),sub_self]
     · have hh:¬ ((1/2:ℝ)≤‖x‖∧‖x‖≤2):=hx; have he:‖(2:ℝ) • x‖≤1:=by rw [norm_smul_of_nonneg zero_le_two]; by_cases h: (1/2:ℝ)≤‖x‖; exact (hh ⟨h,by linarith⟩).elim; linarith
       rw [chi_one (by norm_num) _ (by rw [norm_smul_of_nonneg zero_le_two] at he; linarith),chi_one (by norm_num) _ he,sub_self]
lemma filter_compact : HasCompactSupport (filterU E):= (isCompact_closedBall _ 2).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun x hx=> mem_closedBall_zero_iff.mpr (by by_contra h; exact hx (filter_support _ _ fun hs=> h hs.2))) Metric.isClosed_closedBall)
omit [FiniteDimensional ℝ E] in
lemma filter_near(x:E)(hx:‖x‖<1/2): filterU E x=0:= filter_support _ x fun hh=> hx.not_ge hh.1
omit [FiniteDimensional ℝ E] in
lemma filter_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) (filterU E):= (chi_smooth (V:=E) 1).sub ((chi_smooth 1).comp ((contDiff_const (c:=(2:ℝ))).smul contDiff_id))
omit [FiniteDimensional ℝ E] in
lemma remainder_smooth(r:ℝ)(φ:Trial E)(m:ℤ): ContDiff ℝ (⊤:ℕ∞) (remainder r m φ):= φ.contDiff.sub <| by
   unfold taylorCut; split_ifs
   · exact (chi_smooth (V:=E) r).smul ((polynomial_smooth ..).of_le le_top)
   exact contDiff_const

def packet (m:ℤ)(s r:ℝ)(φ:E→ℂ) (x:E) := filterU E x • remainder s m φ (r • x)

def packetize (m:ℤ)(s r:ℝ) : Trial E →ₗ[ℂ] Trial E where
  toFun φ:= ⟨packet E m s r φ,(filter_smooth _).smul ((remainder_smooth _ _ φ m).comp ((contDiff_const (c:=r)).smul contDiff_id)),(show HasCompactSupport (filterU E • fun x:E=>remainder s m ⇑φ (r•x)) from HasCompactSupport.smul_right (filter_compact E)),fun _ _=>trivial⟩
  map_add' φ ψ:=by ext1 x;change packet E m s r (φ+ψ) x=packet _ _ _ _ φ x+packet _ _ _ _ ψ x; unfold packet;rw [show remainder s m (⇑φ + ⇑ψ) = _ from rem_add s m φ ψ,Pi.add_apply,smul_add] -- fix
  map_smul' c φ:=by ext1; change packet E m s r (c • φ) _=c • packet E m s r φ _; unfold packet; rw [show remainder s m (c • ⇑φ) = _ from rem_smul s m φ c,Pi.smul_apply,smul_comm]
omit [FiniteDimensional ℝ E] in
@[simp] lemma packet_apply (m s r)(φ:E→ℂ)(x:E): packet E m s r φ x = filterU E x • remainder s m φ (r • x):=rfl
lemma packetize_apply (m s r)(φ:Trial E)(x:E):(packetize E m s r φ) x=packet E m s r φ x:=rfl

omit [FiniteDimensional ℝ E] in
private lemma cost_product {K:Type*}[NontriviallyNormedField K] [NormedAlgebra ℝ K][NormedSpace K ℂ][IsScalarTower ℝ K ℂ] {φ:E→K}{g:E→ℂ}{j:ℕ}{x:E}{a b:ℝ} (hg:∀ i ≤ j,‖iteratedFDeriv ℝ i g x‖≤a)(hχ:∀ i ≤ j,‖iteratedFDeriv ℝ i φ x‖≤ b)(h₁:ContDiff ℝ j φ)(h₂:ContDiff ℝ j g): ∀ i ≤ j,
     ‖iteratedFDeriv ℝ i (fun u=>φ u • g u) x‖ ≤ 2^j*b*a:=by
   intro i hi
   have hM l (hl:l∈Finset.range (i+1)):= Finset.mem_range_succ_iff.mp hl
   have h' := norm_iteratedFDeriv_smul_le h₁ h₂ x (mod_cast hi)
   refine LE.le.trans h' <| LE.le.trans (Finset.sum_le_sum fun l hl=> mul_le_mul (mul_le_mul_of_nonneg_left (hχ l ((hM l hl).trans hi)) (Nat.cast_nonneg (α:=ℝ) _)) (hg _ ((Nat.sub_le ..).trans hi)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg (iteratedFDeriv ℝ l φ x)).trans (hχ l ((hM l hl).trans hi))))) ?_
   simp only [← Finset.sum_mul,← Nat.cast_sum]; rw [Nat.sum_range_choose, Nat.cast_pow,Nat.cast_ofNat]
   apply mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hi) (le_trans (norm_nonneg _) (hχ _ hi))) le_rfl (le_trans (norm_nonneg _) (hg _ hi)) _
   exact mul_nonneg (by positivity) (le_trans (norm_nonneg _) (hχ _ hi))

lemma filter_mul {j:ℕ}: ∃ C>0,∀ {g:E→ℂ}{a:ℝ}, (∀ i ≤ j,∀ x∈V!,‖iteratedFDeriv ℝ i g x‖≤a)→ContDiff ℝ j g→0≤a→ Major j (fun y=>filterU E y • g y) (C*a) :=by
  choose c hc using fun i=> ((filter_smooth E).continuous_iteratedFDeriv (m:=i) (mod_cast le_top)).bounded_above_of_compact_support ((filter_compact E).iteratedFDeriv i)
  have h (l:ℕ):0≤c l:= le_trans (norm_nonneg _) (hc l 0)
  let b:=∑ i∈Finset.range (j+1),c i
  have hb i (hi:i ≤ j): ∀ x:E, ‖iteratedFDeriv ℝ i (filterU E) x‖≤b:=fun x=> (hc i x).trans (Finset.single_le_sum (fun l _=>h l) (Finset.mem_range_succ_iff.mpr hi))
  have hC':0≤b:=(norm_nonneg _).trans (hb 0 (Nat.zero_le _) 0)
  refine ⟨2^j*(b+1),mul_pos (by positivity) (by linarith),?_⟩
  intro g a hg hf ha i hi x
  let f0 (x:E):=filterU E x • g x
  by_cases hx:x∈V!
  · exact (cost_product E (g:=g) (fun i hi=> hg i hi x hx) (fun i hi=>hb i hi x) ((filter_smooth E).of_le (mod_cast le_top)) hf i hi).trans (by gcongr; apply le_add_of_nonneg_right zero_le_one)
  have he:f0 =ᶠ[𝓝 x] 0:= by
    filter_upwards [((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)).isOpen_compl.mem_nhds hx] with y hy; change filterU _ y • _=(0:ℂ); rw [filter_support E y hy,zero_smul]
  exact ((congr_arg norm (he.iteratedFDeriv ℝ i|>.eq_of_nhds)).trans_le (by simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]; positivity))

lemma small_packet (m:ℤ)(j:ℕ) : ∃ C>0,∀ {s r:ℝ}, 1 ≤ s → 0 < r → r ≤ 1/4 → ∀ {a:ℝ}{φ:Trial E}, Major (max j (m+1).toNat) φ a → Major j (packet E m s r φ) ((C*a)*r^(m+1).toNat) :=by
   obtain ⟨c',hc',hc⟩:= filter_mul (j:=j) E
   let k:ℕ:=(m+1).toNat; let M:= max j k
   have htt (m:ℤ)(s r:ℝ)(a L:ℝ)(hL:0<L)(φ : Trial E) (hφ:Major (max j (m+1).toNat) φ a)
       (H:∀ i ≤ j,∀ x:E, x∈V!→ ‖iteratedFDeriv ℝ i (fun y=> remainder s m φ (r • y)) x‖≤a*L): Major j (packet E m s r φ) (c'*a*L):=(mul_assoc c' a L).symm ▸ hc H (((remainder_smooth E _ φ m|>.comp ((contDiff_const (c:=r)).smul contDiff_id)).of_le (mod_cast le_top))) (mul_nonneg hφ.nonneg hL.le)
   rcases lt_or_ge m 0 with hm|hm
   · have hk:k=0:=by dsimp [k]; omega
     refine ⟨c',hc',fun {s r} hs hr hr' a φ hφ=>htt m _ _ _ _ (pow_pos hr _) _ hφ fun i hi x hx=>?_⟩
     rw [show (fun y=>remainder s m φ (r • y))=(fun y=>φ (r • y)) from funext fun y=>by rw [remainder,taylorCut,if_neg hm.not_ge,sub_zero],iteratedFDeriv_comp_const_smul _ (φ.orders i), show (m+1).toNat=0 from hk,pow_zero,mul_one, norm_smul,Real.norm_of_nonneg (by positivity)]; exact ((mul_le_of_le_one_left (norm_nonneg _)) (pow_le_one₀ hr.le (by linarith))).trans (hφ i (hi.trans (le_max_left ..)) _)
   have hm':k=m.toNat+1:=by dsimp only [k]; omega
   obtain ⟨c,hc,hb⟩:=poly_deriv_bound (E:=E) M m.toNat 1
   refine ⟨c'*((c+1)*2^k),by positivity,?_⟩
   intro s r hs hr hr' a φ hφ;let g(y:E):=remainder s m φ (r•y); let L(y:E):= φ y - polynomial m.toNat ⇑φ 0 y
   have hl:ContDiff ℝ (↑(⊤:ℕ∞):ℕ∞ω) L:= by apply φ.contDiff.sub ?_; exact (polynomial_smooth ..).of_le le_top
   suffices he:∀ i ≤ j,∀ x∈V!, ‖iteratedFDeriv ℝ i g x‖ ≤ a*(((c+1)*2^k)*r^k) from by dsimp only [k] at he; convert htt m s r a _ (by positivity) φ hφ he using 1; dsimp [k];ring
   intro i hi x hx
   have he:g=ᶠ[𝓝 x] fun y=>L (r • y):=by filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (show ‖x‖<4 from lt_of_le_of_lt hx.2 (by norm_num)))] with y hy; change remainder s m φ (r•y)=_; rw [remainder,taylorCut,if_pos hm,chi_one (lt_of_lt_of_le zero_lt_one hs),one_smul];rw [norm_smul_of_nonneg hr.le]; nlinarith only [mem_ball_zero_iff.mp hy,hr,hr',hs]
   rw [he.iteratedFDeriv ℝ i|>.eq_of_nhds,iteratedFDeriv_comp_const_smul _ (hl.of_le (by exact_mod_cast le_top))]; change ‖r^i • iteratedFDeriv ℝ i L (r • x)‖ ≤ _; rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr.le _)]
   have hL l (hl:l ≤ M)(y) (hy:‖y‖≤ ‖r • x‖): ‖iteratedFDeriv ℝ l L y‖ ≤ (1+c)*a:=by
     rw [show L=⇑φ-polynomial m.toNat ⇑φ 0 from funext fun _=>rfl,iteratedFDeriv_sub_apply (φ.orders _|>.contDiffAt) ((polynomial_smooth ..).of_le le_top |>.contDiffAt)]; apply (norm_sub_le ..).trans
     convert add_le_add (hφ l hl y) (hb (fun z hz=>(hφ z (by have hm':(m+1).toNat=m.toNat+1:=hm'; omega) _)) _ hl y (by rw [norm_smul_of_nonneg hr.le] at hy; nlinarith only [hr,hr',hx.2,hy,norm_nonneg x])) using 1; ring
   have ht:0≤a:=hφ.nonneg
   by_cases hi':i ≤ m.toNat
   · let b:=m.toNat - i
     have hK (i'):i' ≤ b→ i+i' ≤ m.toNat:=by dsimp [b]; omega
     calc
       r^i * ‖iteratedFDeriv ℝ i L (r • x)‖ ≤ r^i*(‖r • x‖^(b+1)*((1+c)*a)):= mul_le_mul_of_nonneg_left (norm_deriv_from_zero (x:=r•x) b i (by exact (φ.contDiff.sub ((polynomial_smooth ..).of_le le_top)).of_le (mod_cast (show (b+i+1: ℕ∞) ≤ ⊤ from le_top))) (fun i' hi'=>(flat_of_sub m.toNat _ _ φ.contDiff 0 (hK i' hi'))) (by positivity) (hL (b+i+1) (by dsimp only [M]; omega))) (pow_nonneg hr.le _)
       _ = (1+c)*a*r^k*‖x‖^(b+1):=by rw [norm_smul_of_nonneg hr.le,show k=i+(b+1) by dsimp [b]; omega,pow_add]; ring
       _ ≤ a*(((c+1)*2^k)*r^k) :=by
                             have ht0:0≤(c+1)*a*r^k:=by positivity
                             have hw: ‖x‖^(b+1) ≤ (2:ℝ)^k:= (pow_le_pow_left₀ (norm_nonneg _) hx.2 _).trans (pow_le_pow_right₀ one_le_two (by dsimp only [b];omega))
                             exact (mul_le_mul_of_nonneg_left hw (show 0 ≤ _ by positivity)).trans (le_of_eq (by ring))
   have ht':k ≤ i:=by omega
   calc
     _ ≤ r^i*((1+c)*a):=by gcongr; exact hL i (hi.trans (le_max_left ..)) _ le_rfl
     _ ≤ r^k*((1+c)*a):=by exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr.le (by linarith) ht') (by positivity)
     _ ≤ _:= by have hv:1≤(2:ℝ)^k := one_le_pow₀ one_le_two; have := pow_nonneg hr.le k; have ht0:0≤(c+1)*a*r^k:=by positivity
                nlinarith only [mul_le_mul_of_nonneg_left hv ht0]


private lemma chi_scaled_cost (j:ℕ) : ∃ c≥0,∀ s:ℝ,0<s→∀ r:ℝ,0<r→∀ i≤j,∀ x:E,x∈V!→‖iteratedFDeriv ℝ i (fun y:E=>chi s (r • y)) x‖≤c:=by
  let v:=chi (E:=E) 1
  choose c hc using fun i=> ((chi_smooth (V:=E) 1).continuous_iteratedFDeriv (m:=i) (mod_cast le_top)).bounded_above_of_compact_support ((chi_compact 1 zero_lt_one).iteratedFDeriv i)
  have hh i:0≤c i:= (norm_nonneg _).trans (hc i 0)
  let b:=∑ i∈ Finset.range (j+1),c i
  have h:b≥0:=Finset.sum_nonneg (fun i _=>hh i)
  refine ⟨4^j*b,by positivity,fun s hs r hr i hi x hx=>?_⟩
  let L:=s⁻¹*r
  rw [show (fun y:E=>chi s (r • y))=fun y=>v (L • y) from funext fun y=>by rw [chi_len,smul_smul],iteratedFDeriv_comp_const_smul _ ((chi_smooth 1).of_le (mod_cast le_top)),norm_smul, Real.norm_of_nonneg (show 0 ≤ L^i by dsimp [L]; positivity)]
  by_cases he:L≤4
  · exact mul_le_mul ((pow_le_pow_left₀ (by dsimp [L]; positivity) he i).trans (pow_le_pow_right₀ (by norm_num) hi)) ((hc ..).trans (Finset.single_le_sum (fun i _=>hh i) (Finset.mem_range_succ_iff.mpr hi))) (norm_nonneg _) (by positivity)
  have he':‖L • x‖>2:=by rw [norm_smul_of_nonneg (by dsimp [L]; positivity)]; nlinarith only [hx.1,he]
  have hz:v =ᶠ[𝓝 (L • x)] 0:= by filter_upwards [IsOpen.mem_nhds (isOpen_lt (continuous_const (y:=2)) continuous_norm) he'] with y hy; exact chi_lt_zero 1 zero_lt_one y (by linarith only [hy])
  rw [(hz.iteratedFDeriv ℝ i).eq_of_nhds]; simpa using mul_nonneg (show 0≤(4:ℝ)^j by positivity) h

private lemma polynomial_scaled_cost (j m:ℕ) : ∃ c≥0,∀ r:ℝ,0<r→∀ (φ:Trial E){B:ℝ}, Major m φ B→∀ i≤j,∀ x∈V!,
      ‖iteratedFDeriv ℝ i (fun y=>polynomial m φ 0 (r • y)) x‖≤ c*(max 1 r)^m*B:=by
   obtain ⟨c,hc,H⟩:=poly_deriv_bound (E:=E) (j:=m) (k:=j) 2
   refine ⟨c,hc,fun r hr φ a ha i hi x hx=> ?_⟩
   rw [mul_assoc c]
   let g(y:E):=φ (r • y)
   suffices hg:(fun y=>polynomial m φ 0 (r • y))=(fun y=> polynomial m g (0:E) y) from hg.symm ▸ H ?_ i hi x hx.2
   · intro l hl; unfold g; rw [iteratedFDeriv_comp_const_smul _ (φ.orders l),norm_smul,smul_zero, Real.norm_of_nonneg (pow_nonneg hr.le _)]
     apply mul_le_mul ((pow_le_pow_left₀ hr.le (le_max_right ..) _).trans (pow_le_pow_right₀ (le_max_left ..) hl)) (ha l hl 0) (norm_nonneg (iteratedFDeriv ℝ l (φ:E→ℂ) 0)) (pow_nonneg (zero_le_one.trans (le_max_left ..)) _)
   funext y'; have hj(i:ℕ): jet i φ 0 (r•y')=jet i g 0 y':=by
     unfold jet g; rw [iteratedFDeriv_comp_const_smul _ (φ.orders i)]
     simpa only [smul_zero,sub_zero,_root_.smul_apply, Finset.prod_const,Finset.card_univ,Fintype.card_fin] using congr_arg (((i.factorial:ℝ)⁻¹:ℝ) • ·) ((iteratedFDeriv ℝ i (φ:E→ℂ) 0).map_smul_univ (fun _=>r) (fun _=>y'))
   exact Finset.sum_congr rfl fun i _=>hj i
/-- Tail estimate on Taylor branches; uniform even if `s` (fixed physical subtraction length
in current test units) is arbitrarily large. This uses the inner bound on `V!` also on every
derivative of the band factor. -/
lemma large_packet (m:ℤ)(j:ℕ)(R:ℝ)(hR:1≤R): ∃ C>0,∀ s:ℝ, s>0 → ∀ r:ℝ,1/4≤r → ∀ {B:ℝ}{φ:Trial E}, support ⇑φ⊆Metric.closedBall 0 R→
        Major (max j (m+1).toNat) φ B → Major j (packet E m s r φ) (C*(r^(m:ℝ))*B):=by
  obtain ⟨K,hK,hf⟩:= filter_mul E (j:=j)
  let b:=2*R
  have hb:b≥1:=by dsimp [b]; linarith
  let u : ℝ:= Real.rpow 4 |(m:ℝ)| * b^j * Real.rpow b |(m:ℝ)|
  have hu:0≤u:=by dsimp [u]; positivity
  have plain (r:ℝ)(hr: 1/4≤r){B:ℝ}{φ:Trial E}(hφ:support ⇑φ⊆Metric.closedBall 0 R)(hφB:Major (max j (m+1).toNat) φ B)(i:ℕ)(hi:i≤j)(x:E)(hx:x ∈ V!):
          ‖iteratedFDeriv ℝ i (fun y=> φ (r • y)) x‖ ≤ u * r^(m:ℝ) * B:=by
      have hr':0<r:=by linarith
      have ha0:= hφB.nonneg
      by_cases hl:r≤b
      · rw [iteratedFDeriv_comp_const_smul _ (φ.orders _),norm_smul,Real.norm_of_nonneg (pow_nonneg hr'.le _)]
        apply mul_le_mul ?_ (hφB i (hi.trans (le_max_left ..)) _) (norm_nonneg _) (by positivity)
        have he:= (pow_le_pow_left₀ hr'.le hl i).trans (pow_le_pow_right₀ hb hi)
        refine he.trans (?_); dsimp only [u]
        have hv:=Real.one_le_rpow (show (1:ℝ)≤4 by norm_num) (abs_nonneg (m:ℝ))
        have _:=Real.one_le_rpow hb (abs_nonneg (m:ℝ))
        suffices ht:1 ≤ (4:ℝ)^ |(m:ℝ)| * r^ (m:ℝ) * b^|(m:ℝ)| by change _ ≤ (4:ℝ)^ |(m:ℝ)| * b^j * b^|(m:ℝ)| *r^(m:ℝ); have :=pow_nonneg (zero_le_one.trans hb) j; nlinarith only [mul_nonneg (sub_nonneg.mpr ht) this]
        by_cases hm:0 ≤ (m:ℝ)
        · rw [abs_of_nonneg hm,← Real.mul_rpow (by positivity) hr'.le]
          exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith only [hr]) hm) (Real.one_le_rpow hb hm)
        rw [show (m:ℝ)= -|(m:ℝ)| from (by rw [abs_of_neg (not_le.mp hm)]; simp)]
        rw [Real.rpow_neg hr'.le, mul_right_comm, abs_neg,abs_abs, ← div_eq_mul_inv]
        apply (one_le_div (Real.rpow_pos_of_pos hr' _)).mpr
        exact le_trans (Real.rpow_le_rpow hr'.le hl (abs_nonneg _)) (le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hb) _) hv)

      have hbad:‖r • x‖>R:=by rw[norm_smul_of_nonneg hr'.le];dsimp only [b] at hl;nlinarith only [hx.1,hl,hR]
      have hv:(fun y:E=>φ (r • y)) =ᶠ[𝓝 x] 0:= by filter_upwards [IsOpen.mem_nhds (isOpen_lt (continuous_const (y:=R)) (by fun_prop : Continuous fun y:E=>‖r • y‖)) hbad] with y hy; exact notMem_support.mp (fun hz=>hy.not_ge (mem_closedBall_zero_iff.mp (hφ hz)))
      rw [(hv.iteratedFDeriv ℝ i).eq_of_nhds]; simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]; exact mul_nonneg ((mul_nonneg hu (Real.rpow_pos_of_pos hr' _).le)) ha0
  suffices h' : ∃ C>0,∀ s:ℝ, s>0 → ∀ r:ℝ,1/4≤r → ∀ {B:ℝ}{φ:Trial E},support ⇑φ⊆Metric.closedBall 0 R→ Major (max j (m+1).toNat) φ B→ ∀ i≤j,∀ x∈ V!,‖iteratedFDeriv ℝ i (fun y=>remainder s m φ (r • y)) x‖ ≤ C*r^(m:ℝ)*B from by
      obtain ⟨c,hc,hc'⟩:= h'; refine ⟨_,mul_pos hK hc,?_⟩; intro s hs r hr B φ hφ hφB
      unfold packet
      rw [mul_assoc K, mul_assoc K]
      exact hf (hc' s hs r hr hφ hφB) (((remainder_smooth E _ φ m|>.comp ((contDiff_const (c:=r)).smul contDiff_id)).of_le (mod_cast le_top))) (mul_nonneg (mul_nonneg hc.le (Real.rpow_pos_of_pos (by linarith only [hr]) _).le) (hφB.nonneg))
  by_cases hm:m<0
  · refine ⟨u+1,by linarith,fun s hs r hr B φ hφ hφB i hi x hx=>?_⟩; simp only [remainder,taylorCut,if_neg hm.not_ge,sub_zero]; exact (plain r hr hφ hφB i hi x hx).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg (by linarith) _)) (Major.nonneg hφB)))
  have hv:0 ≤ m:=not_lt.mp hm
  obtain ⟨χ,hχ,F⟩ := chi_scaled_cost E j; obtain ⟨p,hp,hp'⟩:= polynomial_scaled_cost E j m.toNat
  let c:=2^j*χ*(p*4^m.toNat)
  refine ⟨u+c+1,by positivity,fun s hs r hr B φ hφ hφB i hi x hx=>?_⟩
  have ht: c≥0:=by dsimp [c]; positivity
  have hr':0<r:=by linarith
  have h': max 1 r ≤ 4*r:= max_le (by linarith only [hr]) (by linarith only [hr'])
  simp_rw [remainder]; simp_rw [taylorCut,if_pos hv]
  let g (y:E):= chi s (r • y) • polynomial m.toNat ⇑φ 0 (r • y)
  rw [show (fun y:E=> φ (r • y) - g y) = (fun y:E=> φ (r • y))-g from rfl,iteratedFDeriv_sub_apply (f:=fun y=>φ (r • y)) (g:=g) (by apply ((φ.orders _).contDiffAt.comp _ ?_); exact contDiffAt_const.smul contDiffAt_id) ((chi_smooth ..|>.of_le le_rfl).comp ((contDiff_const (c:=r)).smul contDiff_id)|>.smul ((polynomial_smooth _ φ 0|>.of_le le_top).comp ((contDiff_const (c:=r)).smul contDiff_id))|>.of_le (mod_cast le_top : (i:WithTop ℕ∞)≤ (⊤:ℕ∞))|>.contDiffAt) ]; apply (norm_sub_le ..).trans
  have hz:r^(m:ℝ)=r^m.toNat:=by nth_rw 1 [(Int.toNat_of_nonneg hv).symm];push_cast;exact Real.rpow_natCast ..
  have h'φ:Major m.toNat φ B:=hφB.weaken (by omega) le_rfl
  have hh := cost_product E (φ:= fun y:E=>chi s (r • y)) (g:=fun y:E=>polynomial m.toNat φ 0 (r • y)) (j:=j)
              (fun i hi=>hp' r hr' φ h'φ i hi x hx) (fun i hi=> F s hs r hr' i hi x hx)
              (((chi_smooth ..).comp ((contDiff_const (c:=r)).smul contDiff_id)).of_le (mod_cast le_top)) ((polynomial_smooth _ φ 0|>.of_le le_top).comp ((contDiff_const (c:=r)).smul contDiff_id)) i hi
  have hq : ‖iteratedFDeriv ℝ i g x‖ ≤ c*r^(m:ℝ)*B := by
     refine hh.trans ?_; dsimp only [c]; rw [hz];
     calc
          _ ≤ 2^j*χ*(p*(4*r)^m.toNat*B):= by exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) h' _) hp) hφB.nonneg) (mul_nonneg (pow_nonneg zero_le_two _) hχ)
          _ = _:=by rw [mul_pow];ring
  calc _ ≤ u*r^(m:ℝ)*B+c*r^(m:ℝ)*B:= add_le_add (plain r hr hφ hφB i hi x hx) hq
       _ ≤ _:=by have hz': 0 ≤ r^(m:ℝ)*B:=mul_nonneg (Real.rpow_pos_of_pos hr' ..).le hφB.nonneg; nlinarith only [hz']
end YM.Contacts
