import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Columns
/-! # T-power scale permit. These real-scale arguments range over the WHOLE interval,
with an allowance for any subinterval when iterating a step argument. Basic log & coupling
units on the interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Asymptotics Function Set Comparing
open scoped BigOperators Topology
variable {G : Gauge} {I : Type*} {X : Filter I}
    (hG : G.Simple) {r s s' T T' g t f : I → ℝ} {a b : ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
local notation "unitₛ" => g0 G

def permit (G : Gauge) (a b r s T : ℝ) : Prop := r ≤ s ∧ 1 ≤ T ∧ s*T ≤ r * (a * g0 G r ^ (-b))
-- for doubling from s
lemma splits {r s T : ℝ} (h : permit G a b r s T) (hr : 0 < r) (ht : 2≤T) :
    permit G a b r s 2 ∧ permit G a b r (s*2) (T/2) := by
  obtain ⟨e,i,j⟩:= h; have hh := hr.trans_le e; constructor
  · exact ⟨e,by norm_num,(mul_le_mul_of_nonneg_left ht hh.le).trans j⟩
  exact ⟨e.trans (by linarith),by linarith,(by convert j using 1 <;> ring)⟩

variable (hr : Tendsto r X late) (h : ∀ᶠ i in X, permit G a b (r i) (s i) (T i))
section Fees
variable (ha : 0 < a) (hb : 0 < b)
include h hr hG
lemma limit : T =O[X] fun i => unitₛ (r i) ^ (-b) := by
  refine IsBigO.of_bound a ?_
  filter_upwards [h,hr.eventually self_mem_nhdsWithin,now ((pace hG).comp hr)] with i h e j
  obtain ⟨l,g,k⟩:= h; have p := (zero_lt_one.trans_le g); change 0 < r i at e
  rw [Real.norm_of_nonneg p.le,Real.norm_of_nonneg (Real.rpow_nonneg (show 0 ≤ g0 G (r i) from j.le) _)]
  exact le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_right l p.le).trans k) e
lemma corridor : Tendsto s X late ∧
    (g0 G ∘ s) =O[X] (g0 G ∘ r) ∧ (g0 G ∘ r)=O[X] (g0 G ∘ s) := by
  -- s ≤ sqrt r uniformly. no need to sharpen sqrt const in analytically adequate budget.
  have hg := (pace hG).comp hr; have gr := now hg; have hR := hr.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))
  have hu : ∀ᶠ r:ℝ in late, r * (a * unitₛ r ^ (-b)) ≤ Real.sqrt r := by
    have H : Tendsto (fun r : ℝ=>Real.sqrt r * (a*unitₛ r ^ (-b))) late (𝓝 0) := by
      -- from r=O(any g power) using square root
      have hk : Real.sqrt =O[late] fun r=> (unitₛ r) ^ (1+b) := by
        apply IsBigO.of_pow (n:=2) (by norm_num)
        apply (length hG (2*(1+b))).congr'
        · exact (show ∀ᶠ r in late, 0 < r from self_mem_nhdsWithin).mono fun i hi=> (Real.sq_sqrt hi.le).symm
        refine (g0_pos hG).mono fun i hi=>?_
        change unitₛ i ^ (2*(1+b)) = (unitₛ i ^ (1+b)) ^ (2:ℕ); rw [mul_comm (2:ℝ), Real.rpow_mul hi.le, Real.rpow_two]
      refine Tendsto.congr (fun i=> show a*(Real.sqrt i*unitₛ i ^ (-b))=Real.sqrt i*(a*unitₛ i ^ (-b)) by ring) ?_
      nth_rw 3 [← mul_zero a]
      apply Tendsto.const_mul
      apply IsBigO.trans_tendsto _ (g0_zero hG)
      exact (hk.mul (isBigO_refl (fun i=> unitₛ i ^ (-b)) _)).congr' (EventuallyEq.refl ..)
        ((g0_pos hG).mono fun i hi=>by dsimp only; rw [ ← Real.rpow_add hi, show (1+b+-b)=(1:ℝ) by ring, Real.rpow_one ])
    filter_upwards [H.eventually_lt_const zero_lt_one,self_mem_nhdsWithin] with i h hi
    change 0 < i at hi
    nth_rw 1 [← Real.sq_sqrt hi.le]
    rw [pow_two,mul_assoc]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg i) h.le
  have hi : ∀ᶠ i in X, 0 < r i ∧ r i ≤ s i ∧ s i ≤ Real.sqrt (r i) := by
    filter_upwards [hr.eventually hu,h,hR] with i hi ⟨m,n,b⟩ p
    change 0 < r i at p
    exact ⟨p,m,(le_mul_of_one_le_right (p.le.trans m) n).trans (b.trans hi) ⟩
  have hs : Tendsto s X late := by
    refine tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (hi.mono fun i h=>h.1.le.trans h.2.1) (hi.mono fun i h=>h.2.2) ?_,hi.mono fun i h=>h.1.trans_le h.2.1⟩
    simpa only [Real.sqrt_zero] using (tendsto_nhdsWithin_iff.mp hr).1.sqrt
  refine ⟨hs,?_⟩
  have hp : ∀ᶠ i in X, unitₛ (r i) ≤ unitₛ (s i) ∧ unitₛ (s i) ≤ Real.sqrt 2*unitₛ (r i) := by
    filter_upwards [hi,(Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hs)).eventually_gt_atTop 0] with i ⟨j,k,m⟩ h'
    let u := G.slopeConstant; let Y(z:ℝ):=u * Real.log z⁻¹
    have p : 0 < u := Gauge.slopeConstant_pos hG
    have y : 0 < Y (s i) := mul_pos p h'
    have j' := j.trans_le k
    have w : Y (s i) ≤ Y (r i) := mul_le_mul_of_nonneg_left
      (Real.log_le_log (inv_pos.mpr j') (inv_anti₀ j k)) p.le
    have x : 0 < Y (r i) := y.trans_le w
    have v : Y (r i) ≤ 2*Y (s i) := by
      unfold Y
      have z : s i ^2 ≤ r i := (pow_le_pow_left₀ j'.le m 2).trans_eq (Real.sq_sqrt j.le)
      have e := Real.log_le_log (inv_pos.mpr j) (inv_anti₀ (pow_pos j' 2) z)
      rw [ ← inv_pow, Real.log_pow ] at e
      push_cast at e
      exact (mul_le_mul_of_nonneg_left e p.le).trans_eq (mul_left_comm ..)
    have a : 0 < Real.sqrt (Y (s i)) := Real.sqrt_pos.mpr y
    have b : 0 < Real.sqrt (Y (r i)) := Real.sqrt_pos.mpr x
    refine ⟨inv_anti₀ a (Real.sqrt_le_sqrt w),?_⟩
    change (Real.sqrt (Y (s i)))⁻¹ ≤ Real.sqrt 2 * (Real.sqrt (Y (r i)))⁻¹
    rw [←div_eq_mul_inv, le_div_iff₀ b, ←div_eq_inv_mul, div_le_iff₀ a, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt v
  constructor
  · refine IsBigO.of_bound (Real.sqrt 2) ?_; filter_upwards [gr, now ((pace hG).comp hs), hp] with i hi hj k
    rw [Real.norm_of_nonneg hj.le,Real.norm_of_nonneg hi.le]; exact k.2
  refine IsBigO.of_bound' ?_; filter_upwards [gr, now ((pace hG).comp hs), hp] with i hi hj k
  rw [Real.norm_of_nonneg hj.le,Real.norm_of_nonneg hi.le]; exact k.1
omit h hG hr
variable (hg : Tendsto g X late) (hT : ∀ᶠ i in X,1 ≤ T i) (ht : T=O[X] fun i=> g i ^ (-b))
include ht hT hg hb
lemma log_any (k : ℕ) (d : ℝ) (hd : 0<d) : (fun i=>logs T i ^ k)=O[X] fun i=> g i ^ (-d) := by
  -- buy (1+log T)^k by T^α for any positive α even with T bounded.
  let α := d / b
  have hh : 0<α := div_pos hd hb
  have hu : ∃ C:ℝ, ∀ x ≥ (1:ℝ), ‖(1+Real.log x)^k‖ ≤ C*x^α := by
    have hs : (fun x:ℝ=>1+Real.log x)=O[atTop] Real.log := by
      refine IsBigO.of_bound 2 ?_
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with i hi; rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (by linarith)]; linarith
    obtain ⟨C,hC,H⟩:= ((hs.pow k).trans
      (show (fun x:ℝ=>Real.log x^k) =O[atTop] (fun x=> x^α) by simpa only [Real.rpow_natCast] using (isLittleO_log_rpow_rpow_atTop (k:ℝ) hh).isBigO)).exists_pos
    obtain ⟨L,hL⟩:= eventually_atTop.mp H.bound
    obtain ⟨K,hK⟩:= (isCompact_Icc (α:=ℝ) (a:=1) (b:=L)).exists_bound_of_continuousOn (f:=fun x=> (1+Real.log x)^k) ( (continuousOn_const.add (Real.continuousOn_log.mono fun i hi=> (zero_lt_one.trans_le hi.1).ne')).pow _ )
    refine ⟨max |K| C,fun i hi=>?_⟩
    have V := zero_lt_one.trans_le hi
    rcases le_total i L with h|h
    · exact (hK i ⟨hi,h⟩).trans ((le_abs_self _).trans ((le_max_left ..).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hi hh.le))))
    exact (hL i h).trans (by rw [Real.norm_of_nonneg (by positivity : 0 ≤ i^α)]; gcongr; exact le_max_right ..)
  obtain ⟨C,hC⟩:= hu; refine (IsBigO.of_bound C (g:=fun i=> T i ^ α) (hT.mono fun i hi=> (hC (T i) hi).trans_eq (by rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) α)]))).trans ?_
  exact (ht.rpow hh.le (now hg |>.mono fun i h=>show 0 ≤ g i ^ (-b) from by positivity)).congr' (EventuallyEq.refl ..) ((now hg).mono fun i hi=> by dsimp only; rw [ ← Real.rpow_mul hi.le, show -b*α= -d from by unfold α; field_simp ])

omit hb
lemma account (p : ℕ) (k : ℝ) : (fun i=>g i ^ k*T i^p)=O[X] fun i=>g i ^ (k - b*p) :=
  ((isBigO_refl (fun i=>g i ^ k) X).mul (ht.pow p)).congr' (EventuallyEq.refl ..)
    ((now hg).mono fun i hi=>by dsimp only; rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ g i from hi.le), ← Real.rpow_add hi, sub_eq_add_neg,neg_mul ])
include hb
lemma permit_price {E : Type*} [Norm E] {U : I→E} (u v w : ℕ) (hp : (u:ℝ)-b*v-1 ≥ w)
    (sale : Fare T X (fun i=> g i^u*T i^v) U) : U =O[X] fun i=> g i^w := by
  obtain ⟨p,S⟩:= sale; apply S.trans
  simp_rw [← Real.rpow_natCast (n:=u),←Real.rpow_natCast (n:=w)]
  refine ((account hg hT ht v (u:ℝ)).mul (log_any hb hg hT ht p 1 (by norm_num))).trans ?_
  exact (smaller hg hp).congr' ((now hg).mono fun i h=> Real.rpow_add h _ _) (EventuallyEq.refl ..)
end Fees
end YM.FVA2.GradedFar259.ScaleCost
