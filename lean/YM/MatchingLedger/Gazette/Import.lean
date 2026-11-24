import YM.MatchingLedger.Gazette.Edition
import YM.Push.STATIONARY_UNIFORM.Resolvent

/-!
# Formal Wick prescription and rank/inverse pricing to solve all horizons

Extensive `V` with spatial measures on the native sides, costs arguments are determined without
any simulation of the posterior. Uncentered logs, so need the actual gap from coercivity, not
from ignoring the frame modes. Post-L prices. Struct simultaneously finances measures over the top transfer only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Gazette
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Metric Books MvPolynomial
open YM.PertExtension.Series PertExtension.GaussianScore Matrix
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio) (s : S.Choices)
    (hB : S.patch.Branches S.kernel G)(hs : InRange S) (A : ChartRatio G) (Y : Chip (Page G c))

section formal
variable {ι α : Type} [Fintype ι][Fintype α][DecidableEq ι][DecidableEq α]

-- sum_approx analytic partials
lemma packet_one (v : Chip ι→ℝ) (x:Chip ι) : read x (packet v 1)= fderiv ℝ v 0 x:= by
  rw [packet_read,Radial.jet]; simp [iteratedFDeriv_one_apply]
lemma slab_apply (v : Chip ι→ℝ) (i:ι) (h : ContDiffAt ℝ ω v 0)(x:Chip ι) : read x (pderiv i (packet v 2)) = slab v x (axis i):=by
  rw [packet_gradient h i 1, packet_one]
  let L: (Chip ι →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (axis i)
  unfold derivative; change fderiv ℝ (L ∘ fderiv ℝ v) 0 x=_
  rw [fderiv_comp _ L.differentiableAt ((h.fderiv_right (m:=ω) le_top).differentiableAt (by simp)), ContinuousLinearMap.fderiv]; rfl

omit [Fintype ι] [Fintype α] in
lemma climb_axis (i:ι) : climb (α:=α) (axis i) = axis (.inl i) := by
  ext j; cases j; change axis i _=_; rw [axis_part,axis_part]; simp
  change 0= axis (.inl i : ι ⊕ α) _; rw [axis_part]; simp
omit [DecidableEq ι] in
lemma pay_pi (x : Chip ι): ‖x‖^2≤∑ i,x i^2 := by
  let a := ∑ i,x i^2; have he:0≤a:= Finset.sum_nonneg fun _ _=>sq_nonneg _
  refine (pow_le_pow_left₀ (norm_nonneg _) ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg a)).mpr (fun i=>?_)) 2).trans_eq (Real.sq_sqrt he)
  rw [Real.norm_eq_abs]; apply Real.le_sqrt_of_sq_le; rw [sq_abs]; exact Finset.single_le_sum (fun i _=>sq_nonneg (x i)) (Finset.mem_univ _)

omit [Fintype ι][DecidableEq ι] in
lemma read_only {x y:Chip ι}{p : Poly ι} (h : Set.EqOn x y p.vars) : read x p= read y p:= by
  change eval₂Hom (algebraMap ℝ ℝ) x p=eval₂Hom (algebraMap ℝ ℝ) y p
  exact eval₂Hom_congr' rfl (fun i _ hI=> h hI) rfl
end formal

local notation "V" => edition F s A Y
local notation "m" => (lowerCost G S.patch S.kernel)
lemma mass_pos : 0 < m:= zero_lt_one.trans_le (Action.lower_pos G S.patch S.kernel)
-- dot Hessian, cross term. external B does not change precision

lemma needle_axis (i:Needle F G) : climb (α:=Page G c) (axis i)=axis (.inl i) := by convert! climb_axis (α:=Page G c) i using 2 -- compare subsingleton?

def grade := ((slab (estate (G:=G) F s) (descend Y)).comp climb).toLinearMap
lemma origin (i : Needle F G)(x : Chip (Needle F G)) : read x (pderiv i (V 0))=
    basisLaw F s G x (axis i)+ grade F s Y (axis i):= by
  rw [edition_zero,install_gradient,install_read,pieces]
  apply (slab_apply (estate F (G:=G) s) (.inl i) (estate_analytic F (G:=G) s) (climb x + descend Y)).trans
  erw [← needle_axis F i,_root_.map_add]; rfl

def crystal : Law (Chip (Needle F G)) where
  P := (basisLaw F s G).toLinearMap₁₂
  turns := fun x y=> slab_score (estate F s) ((estate_analytic F (G:=G) s).of_le le_top) (climb x) (climb y)
  slope := ⟨m⁻¹,inv_pos.mpr (mass_pos (S:=S)),fun x=> (mul_le_mul_of_nonneg_left (pay_pi x) (inv_pos.mpr (mass_pos (S:=S))).le).trans (gold F s hB hs x)⟩
  smooth := (basisLaw F s G).continuous.clm_apply continuous_id

-- grade here output logs real vertical variables, nothing to do with final composite grading

def stamp : Fountain (V 0):= by
  let T:= crystal F s hB hs; let v:=grade F s Y; let b:= -T.inverse v
  refine ⟨T,b,fun i x=>?_⟩
  rw [origin]; change T.P _ _ + v _= T.P (axis i) x
  rw [_root_.map_add, show T.P b= -v by unfold b; rw [_root_.map_neg,T.applies], T.turns (axis i) x]
  simp

def columns : Matrix (Needle F G) (Needle F G) ℝ := shaft (crystal F s hB hs)
lemma columns_law (i j:Needle F G) : columns F s hB hs i j=basisLaw F s G (axis i) (axis j):= rfl
lemma ticket_axis (i j:Needle F G) : read (axis (.inl j) : Chip (Meter F G)) (pderiv (.inl i) (tip F s 2))= columns F s hB hs j i:= by
  rw [← tip_expr]; apply (slab_apply (estate F (G:=G) s) (.inl i) (estate_analytic ..) (axis (.inl j))).trans; erw [← needle_axis F j, ← needle_axis F i]; rfl
lemma ticket_axis_zero (i:Needle F G) : read 0 (pderiv (.inl i) (tip (G:=G) F s 2))=0:= by rw [← tip_expr]; apply (slab_apply (estate F (G:=G) s) (.inl i) (estate_analytic ..) 0).trans; simp
lemma laws (x : Chip (Needle F G)) : basisLaw F s G x x=x ⬝ᵥ (columns F s hB hs *ᵥ x):= by
  let T:= crystal F s hB hs; change T.P x x=_; nth_rw 1 [← sum_basis x]; simp_rw [_root_.map_sum, LinearMap.sum_apply, _root_.map_smul, LinearMap.smul_apply]
  simp_rw [applied]; rfl
lemma symmetric_column (i j:Needle F G) : columns F s hB hs i j= columns F s hB hs j i := (crystal F s hB hs).turns _ _
lemma row_gap : Charge (columns F s hB hs) (2*m⁻¹) := by intro v; rw [← laws]; have he:=gold F s hB hs v; linarith only [he]
lemma uses_width : IsUnit (columns F s hB hs).det := by
  apply (isUnit_iff_isUnit_det _).mp
  apply ((row_gap F s hB hs).positive _ (mul_pos (by norm_num) (inv_pos.mpr mass_pos))).isUnit
  ext i j; change star ((columns F s hB hs) j i)=_; exact symmetric_column F s hB hs j i -- maybe symmetry reversed

-- use funds of `n`. Hessian finite range point charge suffices for Sealed.
variable {A} {n : ℕ}(H : Budget G A n)
local notation "M" => H.income S.patch S.kernel
local notation "billH" => gradientBill G S.patch M

def quota (G : Gauge)(P : Patch)(v : ℝ) := Real.exp (stretch P) * gradientBill G P v 2
lemma nonneg_bill (G : Gauge)(P : Patch){v : ℝ}(h : 0 ≤ v)(k : ℕ) : 0≤gradientBill G P v k:=by unfold gradientBill placeFare; positivity [Action.park_nn (belt P)]
lemma nonneg_quota (G : Gauge)(P : Patch){v : ℝ}(h : 0 ≤ v) : 0≤quota G P v:=mul_nonneg (Real.exp_pos _).le (nonneg_bill G P h _)
lemma sealed : Sealed (nest F) 1 (columns F s hB hs) (quota G S.patch M):= by
  intro i j; rw [symmetric_column F s hB hs i j, ← ticket_axis]
  let q := quota G S.patch M
  let u:= stretch S.patch
  let I:= (Sum.inl i : Meter F G); let J:=(Sum.inl j : Meter F G); let p:= tip F (G:=G) s 2; let k:= pderiv I p
  have hk := tip_paid F s H hB H.nn I
  have hp : 0≤ M:=zero_le_one.trans (H.income_one ..)
  have hA : atlas F J= nest F j:= rfl; have hI : atlas F I= nest F i:= rfl
  rw [show pderiv (Sum.inl i) (tip F (G:=G) s 2)=k from rfl]; by_cases h : u<separation (nest F i) (nest F j)
  · have hm : read (axis J) k = read 0 k:=by
      apply read_only; intro j hj; rw [axis_part]; apply if_neg
      intro hE; have hm:= hk.port (show J∈k.vars from hE ▸ hj); rw [ports, loc, arc,near_root] at hm; rw [hA,hI] at hm; exact h.not_ge hm
    rw [hm,show read 0 k=0 from ticket_axis_zero F s i,abs_zero]; exact mul_nonneg (nonneg_quota G S.patch hp) (decay_pos ..).le
  have hp' := not_lt.mp h
  have hm : 1 ≤ Real.exp (stretch S.patch)* Decay 1 (nest F i) (nest F j) := by
    unfold Decay; rw [← Real.exp_add]; apply Real.one_le_exp; change 0≤ (u:ℝ)+ -(1:ℝ)* _; have hp': (separation (nest F i) (nest F j):ℝ) ≤ u := by exact_mod_cast hp'
    linarith
  have ht:= read_bounded (s:=k.vars) hk.degree (Finset.Subset.refl _) («M»:=1) le_rfl (axis J) (fun i _=> (norm_le_pi_norm _ _).trans (norm_axis J))
  rw [one_pow,mul_one] at ht
  apply (le_trans (show |read (axis J) k|≤fare k from ht) hk.receipt).trans
  unfold quota; rw [mul_comm (Real.exp _), mul_assoc]; exact le_mul_of_one_le_right (nonneg_bill G S.patch hp _) hm
lemma multiplicity : Multiplicity (nest (G:=G) F) (nestCost G S.patch):=by
  intro i; simpa only [located,Finset.mem_singleton,Finset.card_singleton,Nat.mul_one] using nest_size (G:=G) F {i}

def reachRate (G : Gauge)(P : Patch)(K : KernelChoices)(v : ℝ) := tiltWidth (nestCost G P) (2*(lowerCost G P K)⁻¹) 1 (quota G P v)
def reachCost (G : Gauge)(P : Patch)(K : KernelChoices)(v:ℝ) := lowerCost G P K * ((nestCost G P : ℝ)*countCost (reachRate G P K v))
local notation "R" => reachCost G S.patch S.kernel M
lemma reach_pos : 0 < reachRate G S.patch S.kernel M := tiltWidth_pos _ (mul_pos (by norm_num) (inv_pos.mpr (mass_pos (S:=S)))) (by norm_num) (nonneg_quota G _ (zero_le_one.trans (H.income_one ..))) -- args
lemma settle_reach : Sealed (nest F) (reachRate G S.patch S.kernel M) (columns F s hB hs)⁻¹ m:= by
  let v:= lowerCost G S.patch S.kernel
  have h0 := nonneg_quota G S.patch (show _ from (zero_le_one.trans (H.income_one S.patch S.kernel)))
  have h1 := inv_pos.mpr (mass_pos (G:=G) (S:=S)); change 0 < v⁻¹ at h1
  have hx:= inverse_sealed (sealed F s hB hs H) («M»:=2*v⁻¹) (by positivity) (by norm_num) (row_gap F s hB hs) h0 (multiplicity F) (uses_width F s hB hs); rw [show 2*v⁻¹/2=v⁻¹ by ring, inv_inv] at hx; exact hx
lemma reach_row (i:Needle F G): (∑ j, ‖(columns F s hB hs)⁻¹ i j‖)≤ R :=
  (settle_reach F s hB hs H).row (reach_pos (S:=S) H) (mass_pos (S:=S)).le (multiplicity F) i

-- solver inputs
local notation "H'" => stamp F s hB hs A Y
lemma tip_salary (j : Needle F G) {Z : ℝ} (hz : 1 ≤ Z) (he:‖Y‖≤ Z): ‖(H').subsidy j‖ ≤ billH 2*Z:=by
  have ht : read 0 (pderiv j (V 0))=(H').subsidy j := by rw [(H').basis_test,_root_.map_add,_root_.map_sum]; simp_rw [read_mul,read_C,read_X]; simp
  rw [← ht]; have hk := Ticket F H Y j (tip_paid F s H hB H.nn _) hz he
  have hx := read_bounded hk.degree (Finset.Subset.refl _) («M»:=1) le_rfl 0 (fun i _=> by simp)
  apply hx.trans; rw [one_pow,mul_one]; exact hk.limit.trans_eq (by norm_num)

variable {t : ℕ} (hh:t+2 ≤ n)
include hh hB
lemma slope_ticket (j : Needle F G) (ht:0<t) (Z : ℝ)(hZ : 1 ≤ Z)(hY : ‖Y‖ ≤ Z) :
    Value F j (Books.FPS.slope V j t) (t+1) ((billH (t+2) + billH t)* Z^(t+1)):= by
  have hp : Books.FPS.slope V j t=pderiv j (install Y (tip F s (t+2))) - pderiv j (install Y (flow F A t)):= by
    cases t with
    | zero => omega
    | succ t=> simp only [FPS.slope,FPS.higher,edition,wide,_root_.map_sub]
  rw [hp]
  have hm : t+2-1=t+1:=by omega
  have hv := Ticket F H Y j (tip_paid F s H hB hh _) hZ hY
  rw [hm] at hv
  have ht' : t-1≤t+1:=by omega
  have hw := Ticket F H Y j (flow_paid F H (show t≤ n from by omega) _) hZ hY
  refine ⟨(totalDegree_sub ..).trans (sup_le hv.degree (hw.degree.trans ht')),?_,?_⟩
  · rw [add_mul]; apply (fare_sub ..).trans; exact add_le_add hv.limit (hw.limit.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ ht') (nonneg_bill G S.patch (zero_le_one.trans (H.income_one ..)) _)))
  intro i hi; rw [sub_eq_add_neg] at hi; have he:= vars_add_subset _ _ hi; rw [vars_neg] at he; exact (Finset.mem_union.mp he).elim (hv.port i) (hw.port i)

omit hB hh
def tableFare (G:Gauge)(P : Patch)(K : KernelChoices)(v : ℝ)(d : ℕ) := 1+|reachCost G P K v| + ∑ t∈ Finset.range (d+1),(gradientBill G P v (t+2)+gradientBill G P v t)
lemma baseFare_one (G : Gauge)(P : Patch)(K : KernelChoices)(v : ℝ)(h:0≤v)(k:ℕ): 1 ≤ tableFare G P K v k:= le_trans (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=> add_nonneg (nonneg_bill G P h _) (nonneg_bill G P h _)))
include hB
lemma license_earn (d : ℕ) (hn : d+2 ≤ n) (Z:ℝ)(hZ:1≤Z)(hY:‖Y‖≤ Z){M' :ℝ}(hM : tableFare G S.patch S.kernel M d * Z^(d+1) ≤ M') :
    Books.FPS.License V H' M' d:= by
  let B := tableFare G S.patch S.kernel M d; let a (t:ℕ) := billH (t+2)+billH t; let v:= H.income S.patch S.kernel
  have h :1≤ v:= H.income_one ..; have hp : 1≤B:= baseFare_one _ _ _ v (zero_le_one.trans h) d
  have he (i:ℕ) : 0 ≤ billH i:= nonneg_bill G S.patch (zero_le_one.trans h) i
  have hk : B ≤ M':=(le_mul_of_one_le_right (zero_le_one.trans hp) (one_le_pow₀ hZ)).trans hM
  have ha (t:ℕ) : 0≤a t := add_nonneg (he _) (he _)
  have hm : 0≤∑ i∈Finset.range (d+1), a i:= Finset.sum_nonneg fun _ _=> ha _
  have hv (t:ℕ) (hh:t≤d) : a t ≤ B:= le_trans (Finset.single_le_sum (f:=a) (fun i _=> ha i) (Finset.mem_range.mpr (show t<d+1 from Nat.lt_succ_of_le hh))) (le_add_of_nonneg_left (by positivity))
  refine ⟨hp.trans hk, ⟨(columns F s hB hs)⁻¹, Matrix.nonsing_inv_mul _ (uses_width F s hB hs),?_⟩, ?_,?_⟩
  · intro i; apply (reach_row F s hB hs H i).trans; exact le_trans ((le_abs_self _).trans (le_trans (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_right hm))) hk
  · intro i; exact (tip_salary F s hB hs Y H i hZ hY).trans ((mul_le_mul (le_trans (le_add_of_nonneg_right (he 0)) (hv 0 (Nat.zero_le _))) (le_self_pow₀ hZ (by omega)) (zero_le_one.trans hZ) (zero_le_one.trans hp)).trans hM)
  intro i hi j; rcases Nat.eq_zero_or_pos i with h0|h0
  · subst i; rw [show Books.FPS.slope V j 0=0 by simp [Books.FPS.slope, Books.FPS.higher]]; simp only [fare_zero,totalDegree_zero]; exact ⟨by norm_num,zero_le_one.trans (hp.trans hk)⟩
  have hK:= slope_ticket F s hB Y H (show i+2≤n from by omega) j h0 Z hZ hY
  exact ⟨hK.degree,hK.limit.trans ((mul_le_mul (hv i hi) (pow_le_pow_right₀ hZ (by omega)) (pow_nonneg (zero_le_one.trans hZ) _) (zero_le_one.trans hp)).trans hM)⟩
end YM.MatchingLedger.Gazette
