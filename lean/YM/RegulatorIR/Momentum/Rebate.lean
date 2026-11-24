import YM.RegulatorIR.Momentum.Coin

/-! Pair with momentum projections at the input (actual moments or lower-
coupling corrections to null for physical packets). Gains after bending
paid by pre-L only. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X : Type} [Fintype J][DecidableEq J]
variable (U:Moves J → X→ℝ)(w:X→ℝ≥0∞)

def postage (u:ℕ)(v:Moves J):ℝ≥0∞:= (extent v+1)^u
omit [DecidableEq J] in
lemma duty_one (u:ℕ)(v:Moves J):1≤postage u v:=one_le_pow₀ le_add_self
-- Pre-factor encapsulates intrinsic price before any differences. only the specified derivative caps. L may be real/infinite past algebra lemma, but Width implies finite.
structure Controls (U:Moves J→ X→ℝ)(w:X→ℝ≥0∞)(L F:ℝ≥0∞) (u m:ℕ) : Prop where
 entries : 1 ≤ L
 finiteP : L≠⊤
 nearJ (i:ℕ)(h:i≤m) (l:List J)(_hl:l.length=i) (v:Moves J) : extent v ≤ L→ quota (journey U l v) w ≤ F*(L⁻¹)^i
 farJ (v:Moves J) : quota (U v) w ≤ F*(1+ L⁻¹ * extent v)^u

def limitedC (J:Type) [Fintype J](u m:ℕ):ℝ≥0∞:= 1+ (2:ℝ≥0∞)^u + ∑ i∈Finset.range m,feeP J i
omit [DecidableEq J] in
lemma limited_f (u m):limitedC J u m ≠⊤:=by
 unfold limitedC;exact ENNReal.add_ne_top.mpr ⟨by finiteness, ENNReal.sum_ne_top.mpr fun i _=>fee_f i⟩
variable {U w}{u m i:ℕ}{F L:ℝ≥0∞}(K:Controls U w L F u m)
include K
lemma all_rows (h:i≤m) (l:Sequence J i) : quota (journey U (stamps i l) 0) w ≤ F:= by
 apply (K.nearJ _ h _ (stamps_length i l) _ (by simp)).trans
 nth_rewrite 2 [← mul_one F]; gcongr; exact pow_le_one₀ bot_le (by simpa only [inv_one] using ENNReal.inv_le_inv.mpr K.entries)
lemma refund (h:m≤u) (v:Moves J) : quota (rest U m v) w ≤ F*limitedC J u m* (L⁻¹)^m * postage u v:=by
 let s:= extent v+1; have hs:1 ≤ s:=le_add_self
 let q:=L⁻¹; have hq : q≤1:=by simpa only [inv_one] using ENNReal.inv_le_inv.mpr K.entries
 let B:= ∑ i∈Finset.range m,feeP J i
 let C:= limitedC J u m
 have hc: C=1+ (2:ℝ≥0∞)^u+B:=rfl
 rcases le_total (extent v) L with hp|hp
 · apply (total_rest U m (fun t ht=> K.nearJ m le_rfl t ht) v hp).trans
   change s^m*(F*q^m) ≤ F*C*q^m*s^u; rw [mul_comm]; apply mul_le_mul' (mul_le_mul_left (le_mul_of_one_le_right (by simp) (show 1≤C from le_trans le_self_add le_self_add)) _) (pow_le_pow_right₀ hs h)
 have hz:q*L=1:= ENNReal.inv_mul_cancel (zero_lt_one.trans_le K.entries).ne' K.finiteP
 have ho : 1 ≤ q*s:= hz ▸ mul_le_mul_right (hp.trans le_self_add) _ -- maybe dependent issue
 have hp' : (1+L⁻¹ * extent v) ≤ 2 * (q*s):=by rw [two_mul];exact add_le_add ho (mul_le_mul_right le_self_add _)
 have hj t (ht:t ≤ m) : q^t*s^t ≤ q^m*s^u:=by rw [← mul_pow]; exact (pow_le_pow_right₀ ho ht).trans (by rw [mul_pow];gcongr)
 have he(v:ℝ≥0∞) : F * (2^u * v)≤ F*(1+2^u)*v:=by rw [← mul_assoc]; exact mul_le_mul_left (mul_le_mul_right le_add_self _) _
 have hd:quota (U v) w ≤ F*(1+(2:ℝ≥0∞)^u)*q^m*s^u:=by
    apply (K.farJ v).trans
    apply le_trans (b:=F*(2*(q*s))^u) (by gcongr)
    rw [mul_pow, mul_pow]; apply (he _).trans; rw [← mul_assoc]; exact mul_le_mul_left (mul_le_mul_right (pow_le_pow_of_le_one (by simp) hq h) _) _
 have hh:quota (deposit U m v) w ≤ F*B*q^m*s^u:=by
    rw [deposit, Finset.sum_apply]
    unfold B; rw [mul_sum,Finset.sum_mul,Finset.sum_mul]; refine le_trans (quota_sum ..) (sum_le_sum fun i hi=>?_)
    have ht:i≤m:= (mem_range.mp hi).le
    apply (portion_cost (U:=U) (W:=w) i (fun l=>K.nearJ i ht _ (stamps_length i l) _ (by simp)) v).trans
    change feeP J i * (s^i*(F*q^i)) ≤ F*feeP J i*q^m*s^u; rw [mul_left_comm (s^i) _,mul_comm (s^i),← mul_assoc _ F,mul_comm F,mul_assoc _ (q^m)]; exact mul_le_mul_right (hj i ht) _
 have he' : F*C*q^m*s^u=(F*(1+(2:ℝ≥0∞)^u)*q^m*s^u)+(F*B*q^m*s^u):=by rw [hc,mul_add,add_mul,add_mul]
 have h':= (quota_sub (U v) (deposit U m v) w).trans (add_le_add hd hh); exact h'.trans_eq he'.symm
-- input costs. momentum on positive input. pairing at all y
variable (f:Moves J→ℝ)

def fixed (U:Moves J→ X→ℝ) (T:Moves J→ℝ) (v:Moves J)(x:X):ℝ:= T v * U v x
def receive (U:Moves J→ X→ℝ) (T:Moves J→ℝ) (x:X):ℝ:=∑' v,fixed U T v x
omit K
omit [Fintype J][DecidableEq J] in
lemma lineage {U:Moves J→X→ℝ}(V:X→ℝ≥0∞) (T:Moves J→ℝ) {W:Moves J→ℝ≥0∞}{c:ℝ≥0∞}(h:∀ x,quota (U x) V ≤c*W x):quota (receive U T) V ≤ c*quota T W:=by
 apply (inside_quota ..).trans; unfold quota
 rw [ENNReal.tsum_comm]
 rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum
 intro v; change quota (fixed U T v) V ≤ _; unfold fixed; rw [quota_times]; exact (mul_le_mul_right (h v) _).trans_eq (mul_left_comm ..)
omit [Fintype J][DecidableEq J] in
lemma lineage_fin {U:Moves J→X→ℝ}(V:X→ℝ≥0∞) (T:Moves J→ℝ) {W:Moves J→ℝ≥0∞}{c:ℝ≥0∞}(h:∀ x, quota (U x) V ≤ c*W x)(ht:c≠⊤)(hp: quota T W≠⊤)(x:X)(hv:1≤V x): Summable (fun v=> fixed U T v x):=by
 apply quota_summable (w:=1) (fun _=>le_rfl)
 apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ht hp); rw [quota_base,quota, ← ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun i=>?_
 unfold fixed; rw [enorm_mul]; apply le_trans _ (show ‖T i‖ₑ * (c*W i) ≤ _ from le_of_eq (by ring)); apply mul_le_mul_right
 exact (le_mul_of_one_le_right (by simp) hv).trans ((term_le _ _ _).trans (h i))

def readsP (f:Moves J→ℝ)(n:ℕ)(T:Sequence J n):ℝ:=∑' v,f v * rateP n T v
include K
variable (hw:∀ x,1≤ w x)(h:m≤u) (hF:F≠⊤)(hb: quota f (postage u)≠⊤)
-- fixed projected polynomial exact
include hw h hF hb
omit K hw hF in
lemma forecast {t:ℕ}(hi:t≤m) (x:X) :
 Summable (fun v:Moves J=> fixed (portion t U) f v x) ∧ receive (portion t U) f x= (Nat.factorial t:ℝ)⁻¹*∑ i:Sequence J t,readsP f t i * journey U (stamps t i) 0 x:=by
 let G:=height t; have hz(v:Moves J)(i:Sequence J t) : ‖rateP t i v‖ₑ ≤ G*postage u v:= (particles_cost ..).trans (mul_le_mul_right (pow_le_pow_right₀ le_add_self (hi.trans h)) _)
 let g v i:= f v * rateP t i v; let p(i):= journey U (stamps t i) 0 x
 have hg i : Summable fun v=>g v i:=by
    apply quota_summable (w:=1) (fun _=>le_rfl); apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (height_f t) hb); rw [quota_base,quota,← ENNReal.tsum_mul_left]; exact ENNReal.tsum_le_tsum fun v=>by unfold g;rw [enorm_mul];exact (mul_le_mul_right (hz v i) ‖f v‖ₑ).trans_eq (mul_left_comm ..)
 let N:ℝ:= (Nat.factorial t:ℝ)⁻¹
 have he(v):fixed (portion t U) f v x=N*∑ i:Sequence J t,g v i * p i:=by unfold fixed; rw [particles,Pi.smul_apply,smul_eq_mul, mul_left_comm, Finset.sum_apply, mul_sum]; exact congr_arg _ (sum_congr rfl fun i _=> (mul_assoc ..).symm)
 simp_rw [receive,he]; refine ⟨(summable_sum (s:=Finset.univ) (fun i _=> (hg i).mul_right (p i))).mul_left _,?_⟩; rw [tsum_mul_left,Summable.tsum_finsetSum (s:=Finset.univ) (fun i _=>(hg i).mul_right (p i))]; simp_rw [tsum_mul_right]; rfl
include h hF hb
lemma collect_all (x:X):
 Summable (fun v:Moves J=> fixed U f v x)∧ receive U f x=receive (rest U m) f x+∑ i∈Finset.range m,receive (portion i U) f x:=by
 have hz:L⁻¹≠⊤:= ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le K.entries).ne'
 have hv:Summable (fun v=> fixed (rest U m) f v x):= lineage_fin w f (refund K h) (ENNReal.mul_ne_top (ENNReal.mul_ne_top hF (limited_f u m)) (ENNReal.pow_ne_top hz)) hb x (hw x)
 have hp(i:ℕ)(hi:i∈Finset.range m): Summable (fun v:Moves J=>fixed (portion i U) f v x):= (forecast (U:=U) f h hb (mem_range.mp hi).le x).1
 have he (v):fixed U f v x=fixed (rest U m) f v x+∑ i∈Finset.range m,fixed (portion i U) f v x:=by unfold fixed rest deposit; simp only [Pi.sub_apply,Finset.sum_apply, mul_sub,mul_sum];rw [sub_add_cancel]
 constructor
 · simp_rw [he]; exact hv.add (summable_sum hp)
 nth_rw 1 [receive]; rw [tsum_congr he, hv.tsum_add (summable_sum hp),Summable.tsum_finsetSum hp];rfl
-- display strength following actual geometry. Input moments ≤m tapped with no $L^m$ repeated factor; applies even Mark f=coeff(φ). Stop.
def displayC (J:Type)[Fintype J](m:ℕ):ℝ≥0∞ :=∑ i∈range m,(Fintype.card (Sequence J i):ℝ≥0∞)
omit K hw h hF hb [DecidableEq J] in
lemma display_f (m): displayC J m≠⊤:=by unfold displayC; exact ENNReal.sum_ne_top.mpr (fun _ _=>by finiteness)
lemma distilled {p:ℝ≥0∞}(Z:∀ i<m,∀ t, ‖readsP f i t‖ₑ ≤ p):
 quota (receive U f) w ≤ F * limitedC J u m * (L⁻¹)^m * quota f (postage u) + displayC J m * (p*F):=by
 rw [show receive U f=receive (rest U m) f+∑ i∈range m,receive (portion i U) f from funext fun y=> by simpa only [Pi.add_apply,Finset.sum_apply] using (collect_all K f hw h hF hb y).2]; apply (quota_add ..).trans; apply add_le_add (lineage w f (refund K h)); unfold displayC; rw [Finset.sum_mul]; apply (quota_sum ..).trans (sum_le_sum (fun i hi=>?_))
 have ht:= mem_range.mp hi;rw [show receive (portion i U) f=(Nat.factorial i:ℝ)⁻¹ • ∑ j:Sequence J i, readsP f i j • journey U (stamps i j) 0 from funext fun y=> by simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using (forecast (U:=U) f h hb ht.le y).2,show ∀ (U:X→ℝ)(z:ℝ),quota (z • U) w=‖z‖ₑ*quota U w from fun U z=>quota_times ..]
 apply le_trans (mul_le_mul' (inverse_f i) (quota_sum ..));rw [one_mul,← nsmul_eq_mul, ← card_univ,← sum_const]; apply sum_le_sum; intro t _; exact (quota_times _ w _).trans_le (mul_le_mul' (Z i ht t) (all_rows K ht.le t))
end YM.RegulatorIR.Momentum
