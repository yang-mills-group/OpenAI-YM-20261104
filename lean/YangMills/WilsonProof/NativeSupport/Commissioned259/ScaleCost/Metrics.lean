import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Final
/-!
# Sharp G.1 growing norms, also available after the all-orders T-payments

In a fixed basis with the grading at d. Normalize by LEFT division by the stretch. CheckB
has leading term I; one does *not* need to track norms close to 1 along every one of the
variable number of iterates. Inversion on that fixed-dimensional grade basis retains sharp costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Function Set Asymptotics Comparing Matrix PowerSeries
open MS.Book.Program XSpace XSpace.Normalize O.Score O.Enh Dframe FVA2.Scale
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ} {B : ℝ→Frames G} (H : Law V R B)
variable {d : ℕ} {D : Route G} (hG : G.Simple) {t : ℝ→ℝ} (ht : t=O[𝓝[>] 0] (g0 G))
    {a b : ℝ} (hb : 0 < b) (hD : Balances D) (S : StepCost G R B t D)
local notation "g" => g0 G
local notation "late" => 𝓝[>] (0:ℝ)

abbrev engine (G : Gauge) (d : ℕ) (t : ℝ) := columns (Level.Dial (G:=G) d t)
lemma forward (s t : ℝ) : engine G d s * engine G d t = engine G d (s+t) :=
  (composition' _ _).trans (congr_arg columns (Level.group (G:=G) s t))
lemma origin : engine G d 0=1 := Eq.trans (congr_arg columns Level.flat) one_matrix
lemma gear_cost (s : ℝ) (b c : Toon G d) :
    engine G d s b c= if c=b then ↑(Real.exp (-s)^c.size) else 0 := by
  unfold engine columns; rw [Level.exact₀, _root_.map_smul, pivotδ, Extent.token]
  by_cases c=b <;> simp [*,eq_comm]
set_option maxHeartbeats 600000 in
lemma remove (k : ℕ) (s t : ℝ) (ht : 0 < t) (b c : Toon G d) :
    (engine G d (Real.log t) * form B d t k s) b c = crop k s (prose (B (-Real.log t) d) b c) := by
  let D':=Level.Dial (G:=G) d (Real.log t); let Z:=conversion B (-Real.log t) d; let L:=B (-Real.log t) d
  have e : form B d t k s=columns (∑ i∈Finset.range (k+1), (s:ℂ)^i • coeff i Z) := by apply Matrix.ext; intro b c; exact Eq.symm (fee_matrix _ b c k s)
  have eq j : D'*coeff j Z=coeff j L := by unfold Z conversion D' L; rw [coeff_C_mul, ←mul_assoc, Level.autumn,one_mul]
  rw [e, composition']; change columns (D' * (∑ i∈Finset.range (k+1), (s:ℂ)^i • coeff i Z)) b c = _
  simp_rw [Finset.mul_sum,mul_smul_comm,eq,columns,LinearMap.sum_apply,map_sum,crop_apply, prose,coeff_mk,columns,LinearMap.smul_apply,_root_.map_smul,smul_eq_mul]; rfl

variable {I : Type*} {X : Filter I} {r T : I→ℝ}
    (hr : Tendsto r X late) (ha : ∀ᶠ i in X, 1 ≤ T i ∧ T i ≤ a*g0 G (r i)^(-b))
include H hG ht hb hr ha

-- Taylor through the clock at diverging log T. cost of dropping all above constant
-- in stability.
lemma steady (p : ℕ) : Tendsto (fun i=> engine G d (Real.log (T i)) * form B d (T i) p (t (r i))) X (𝓝 1) := by
  have hg := (pace hG).comp hr; have hi : ∀ᶠ i in X, 1 ≤ T i := ha.mono fun i h=>h.1
  have ht' := (ht.trans_tendsto (g0_zero hG)).comp hr
  have h : T=O[X] fun i=> g (r i)^(-b) := by
    refine IsBigO.of_bound a ?_
    filter_upwards [ha,now hg] with i ⟨q,h⟩ p
    rw [Real.norm_of_nonneg (zero_le_one.trans q),Real.norm_of_nonneg (Real.rpow_nonneg (show 0 ≤ g (r i) from p.le) _)]
    exact h
  refine tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mpr fun k=> ?_
  let F i:= prose (B (-Real.log (T i)) d) j k
  have u : Tunes T X (fun _=>1) F := by
    intro n
    have H:Rhythm (fun s=> coord j (coeff n (B (-s) d) (theory k))) := by simpa only [Polynomial.eval_neg,Polynomial.eval_X] using (H.proper d n _ (coord j)).pre (-(Polynomial.X : Polynomial ℝ))
    simp_rw [F,prose,coeff_mk]
    exact rhythm_log hi H
  have h0 (i:I) : crop 0 (t (r i)) (F i)=(1:Operator G d) j k := by
    simp only [crop_apply,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,one_mul,F, prose,coeff_mk,(H.paid ..).zero]; exact congr_arg (fun A:Operator G d=>A j k) one_matrix
  let y : I→ℝ:= g ∘ r
  obtain ⟨n,hp⟩:= (Tunes.excess hi (ht'.abs.eventually (ge_mem_nhds (by norm_num : |(0:ℝ)|<1)))
    (ht.comp_tendsto hr) p 0 (Nat.zero_le _) u).extend (v:=y) (Eventually.of_forall fun i=>by change y i ^ (0+1:ℕ)*1=y i; simp)
  have hE := log_any hb hg hi h n (1/2) (by norm_num)
  have b : (fun i=>y i^((1:ℝ)/2)) =ᶠ[X] fun i=>y i*y i^(-((1:ℝ)/2)) := by filter_upwards [now hg] with i h; rw [show ((1:ℝ)/2) = 1+ -(1/2) by norm_num,Real.rpow_add (show 0<y i from h),Real.rpow_one]; norm_num
  have hp' : Tendsto (fun i=> crop p (t (r i)) (F i)-crop 0 (t (r i)) (F i)) X (𝓝 0) := by
    apply IsBigO.trans_tendsto (hp.trans ((isBigO_refl y X).mul hE))
    apply Tendsto.congr' b
    simpa only [Real.zero_rpow (by norm_num : (1:ℝ)/2≠0)] using (( (g0_zero hG).comp hr ).rpow_const (Or.inr (show 0 ≤ (1:ℝ)/2 by norm_num)))
  simp_rw [h0] at hp'; apply Tendsto.congr' ?_ (by simpa only [zero_add] using hp'.add (tendsto_const_nhds (x:=(1:Operator G d) j k)))
  filter_upwards [hi] with i hi; change _-_+_=(engine G d (Real.log (T i))* form B d (T i) p (t (r i)) ) j k; rw [sub_add_cancel]; exact Eq.symm (remove p _ _ (zero_lt_one.trans_le hi) j k)

omit H ht hb ha hG hr
private lemma flowing {F D : I→ Operator G d} {f v:I→ℝ} (hn : (stiffness ∘ F) =O[X] f) (hm : (stiffness ∘ D) =O[X] v) :
    (fun i=>stiffness (F i * D i))=O[X] fun i=> f i*v i :=
  (IsBigO.of_bound' (Eventually.of_forall fun i=>(Real.norm_of_nonneg (stiffPos _)).trans_le ((stiffMul _ _).trans_eq
    (Real.norm_of_nonneg (mul_nonneg (stiffPos _) (stiffPos _))).symm))).trans (hn.mul hm)
private lemma pays (R : Operator G d) (F : I→Operator G d) (h : Tendsto F X (𝓝 R)) : (stiffness ∘ F)=O[X] fun i=> (1:ℝ) :=
  matrixPay.mpr fun i j=> isBigO_const_of_tendsto (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j) one_ne_zero
private lemma poles (hT : ∀ᶠ i in X,1 ≤ T i) : (fun i=>stiffness (engine G d (-Real.log (T i))))=O[X] (fun i=> T i ^ d) ∧
    (fun i=>stiffness (engine G d (Real.log (T i))))=O[X] fun i=>(1:ℝ) := by
  constructor <;> (refine matrixPay.mpr fun i j=> IsBigO.of_bound' ?_; filter_upwards [hT] with k h; have p := zero_lt_one.trans_le h)
  · change ‖engine G d _ i j‖ ≤ _; rw [gear_cost]; split_ifs
    · rw [neg_neg,Real.exp_log p, Complex.norm_real,norm_pow,norm_pow]; exact pow_le_pow_right₀ (h.trans (le_abs_self _)) (size_le _)
    exact norm_zero.trans_le (norm_nonneg _)
  change ‖engine G d _ i j‖ ≤ ‖(1:ℝ)‖; rw [gear_cost,norm_one]; split_ifs
  · rw [Real.exp_neg,Real.exp_log p,Complex.norm_real,norm_pow,norm_inv,Real.norm_of_nonneg p.le]; exact pow_le_one₀ (by positivity) ((inv_le_one₀ p).mpr h)
  rw [norm_zero]; norm_num
include H ht hb ha hG hr hD S
lemma actual_near : Tendsto (fun i=> engine G d (Real.log (T i)) * actual D d (r i) (T i)) X (𝓝 1) := by
  obtain ⟨p,M,hM,P⟩:= (movement (a:=a) H hG ht hb 1 hD S d).exists
  have hi := ha.mono fun i h=>h.1
  let f i:= form B d (T i) p (t (r i)); let A i:= actual D d (r i) (T i); let u i:= engine G d (Real.log (T i))
  have hp : (fun i=> stiffness (A i - f i))=O[X] (g ∘ r) := by
    apply IsBigO.of_bound M; filter_upwards [ha,hr.eventually P,now ((pace hG).comp hr)] with i ⟨a,b⟩ h l
    rw [Real.norm_of_nonneg (stiffPos _),Real.norm_of_nonneg l.le]; specialize h _ a b; unfold paired at h; rw [pow_one] at h; exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hu : Tendsto (fun i=> u i*f i) X (𝓝 1):= steady H hG ht hb hr ha p
  have z : (fun i=>stiffness (u i * A i - u i * f i))=O[X] (g ∘ r) := by
    simp_rw [ ←mul_sub ]; exact (flowing (F:=u) (poles hi).2 hp).congr_right (fun i=>one_mul _)
  refine tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>?_
  have hf : Tendsto (fun k=> (u k*A k) i j-(u k*f k) i j) X (𝓝 0) := (matrixPay.mp z i j).trans_tendsto ((g0_zero hG).comp hr)
  exact Tendsto.congr (fun k=>sub_add_cancel (_:ℂ) _) (by simpa only [zero_add] using hf.add (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hu i) j))

-- for starting route of genuine equivalence (fields)
def selfCharge (D : Route G) : Prop := ∀ s d,D s s d=LinearMap.id
lemma issued_norms (hD' : selfCharge D) :
    (fun i=> stiffness (actual D d (r i) (T i)))=O[X] (fun i=> T i ^ d) ∧
    (fun i=> stiffness (columns (D (r i*T i) (r i) d)))=O[X] fun i=>(1:ℝ) := by
  let f i:= engine G d (Real.log (T i))*actual D d (r i) (T i); have h : Tendsto f X (𝓝 1) := actual_near H hG ht hb hD S hr ha
  obtain ⟨i,j⟩ := poles (G:=G) (d:=d) (ha.mono fun i h=>h.1)
  have hf (s : ℝ) : engine G d (-s)*engine G d s=1:=by rw [forward,neg_add_cancel,origin]
  constructor
  · apply (flowing i (pays 1 f h)).congr (fun i=>by unfold f; rw [←mul_assoc, hf,one_mul]) (fun _=>mul_one _)
  let y i:=columns (D (r i*T i) (r i) d)
  have hv : Tendsto (fun i=>(f i)⁻¹) X (𝓝 1) := by
    have e : ContinuousAt Ring.inverse (1:Operator G d).det := by rw [Ring.inverse_eq_inv',det_one]; exact continuousAt_inv₀ one_ne_zero
    simpa [Function.comp_def] using (continuousAt_matrix_inv (1:Operator G d) e).tendsto.comp h
  refine (flowing (pays 1 _ hv) j).congr' ?_ (Eventually.of_forall fun _=>one_mul _)
  filter_upwards [(continuous_id.matrix_det.tendsto _ |>.comp h).eventually (eventually_ne_nhds (by simp : (1:Operator G d).det ≠ 0))] with i hi
  apply congr_arg stiffness
  change (f i)⁻¹* _=y i
  have u : f i*y i=engine G d (Real.log (T i)) := by
    unfold f y; rw [mul_assoc,actual, composition',show D (r i) _ d ∘ₗ _=D (r i) (r i) d from (hD _ _ _ _).symm,hD',one_matrix,mul_one]
  change (f i).det ≠ 0 at hi
  rw [ ← u, ← mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hi), one_mul]

omit ha hr
lemma budget (hD' : selfCharge D) (d : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ᶠ r in late, ∀ T ≥ 1, T ≤ a*g r^(-b) →
    stiffness (actual D d r T) ≤ C * T^d ∧ stiffness (columns (D (r*T) r d)) ≤ C := by
  let I:={i:ℝ×ℝ // 1 ≤ i.2 ∧ i.2 ≤ a*g i.1 ^ (-b)}
  let r(i:I):=i.val.1; let T (i:I):=i.val.2; let X:=comap r late
  have e: ∀ᶠ i in X,1 ≤ T i ∧ T i ≤ a*g (r i)^(-b) := Eventually.of_forall fun i=>i.property
  obtain ⟨h,k⟩:= issued_norms (d:=d) H hG ht hb hD S tendsto_comap e hD'
  obtain ⟨C,hC,h⟩:= h.exists_pos; obtain ⟨K,hK,k⟩:= k.exists_pos
  refine ⟨max C K,lt_max_of_lt_left hC,(eventually_comap.mp (h.bound.and k.bound)).mono ?_⟩
  intro r j T ht ha; have p := zero_lt_one.trans_le ht
  obtain ⟨x,y⟩:= j (⟨(r,T),ht,ha⟩:I) rfl; change ‖stiffness (actual D d r T)‖ ≤ C * ‖T^d‖ at x
  change ‖stiffness (columns (D (r*T) r d))‖ ≤ K * ‖(1:ℝ)‖ at y
  rw [Real.norm_of_nonneg (stiffPos _),Real.norm_of_nonneg (pow_nonneg p.le _)] at x; rw [Real.norm_of_nonneg (stiffPos _),norm_one,mul_one] at y
  exact ⟨x.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg p.le _)),y.trans (le_max_right ..)⟩

lemma mile {W : ℝ} (hW : 1 ≤ W) (hD' : selfCharge D) : Mileage G B t D a b W := by
  constructor
  · intro d u v; obtain ⟨C,hC,h⟩:= budget (a:=a) H hG ht hb hD S hD' d; refine ⟨C,hC.le,?_⟩
    exact h.mono fun i h T ht hv=> le_trans (leanFee (actual D d i T) v u) (h _ (hW.trans ht) hv).1
  intro p d; obtain ⟨q,hq,⟨C,hC,P⟩⟩:=( (eventually_ge_atTop (p+5)).and (movement (a:=a) H hG ht hb (p+2) hD S d) ).exists
  refine ⟨q,hq,fun i j=> ⟨C,hC.le,?_⟩⟩
  exact P.mono fun r h T hT e=> (leanFee (actual D d r T-form B d T q (t r)) j i).trans
    ((le_add_of_nonneg_left (norm_nonneg _)).trans (h _ (hW.trans hT) e))
end YM.FVA2.GradedFar259.ScaleCost
