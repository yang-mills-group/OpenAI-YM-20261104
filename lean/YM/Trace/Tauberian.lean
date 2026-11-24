import YM.Trace.EnergyScale
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
Weak asymptotic inversion using positivity. No spectral error estimates at the light-cone
boundary are assumed; all arrays in this module are nonnegative measures. One exponential
weight renders the determining portion finite. Not convergence in strong dual topology.
-/
noncomputable section
namespace YM.Trace
open Mink Boundary Function Filter MeasureTheory Set Real
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ENNReal Pointwise
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {α : Type*} {l : Filter α} {μ : Measure E4} {M : α → Measure E4}

abbrev supportC : Set (Axis→ℝ) := Icc (fun _=>0) (fun _=>1)
abbrev cuboid := {x : Axis→ℝ // x∈supportC}
noncomputable def lens (i : Axis) : E4 := basis timeAxis + if i=timeAxis then 0 else basis i
lemma lens_cone (i : Axis) : lens i ∈ cone := by
  have he (i : Axis) (hi : i≠timeAxis) : time (basis i)=0 := by simp [time,Ne.symm hi]
  have hx (i : Axis) : ‖spatial (basis i)‖ ≤ 1 := by have := Mink.squares (basis i); rw [basis_norm] at this; nlinarith [norm_nonneg (spatial (basis i))]
  show ‖spatial _‖ ≤ time _
  rw [lens]; split_ifs with ht <;> simp_all
lemma lens_value (p : E4) (i : Axis) : inner ℝ p (lens i)=if i=timeAxis then time p else time p+p i := by
  simp only [lens,inner_add_right]
  split_ifs <;> simp [basis,time,EuclideanSpace.inner_single_right]
lemma lens_bound (i : Axis) : ‖lens i‖≤3 := by rw [lens]; refine (norm_add_le ..).trans ?_; split_ifs <;> norm_num

abbrev exponential (p x : E4) := Real.exp (-inner ℝ p x)
@[fun_prop] lemma continuous_exp_abbrev (x : E4) : Continuous (fun p=> exponential p x) := by unfold exponential; fun_prop
lemma exponential_sub_one {p u : E4} (hp : p∈cone) (hu : u∈cone) : exponential p u ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (self_pair hp hu))
lemma exponential_express (p : E4) (r : Axis → ℕ) : exponential p (∑ i : Axis, (r i:ℝ) • lens i)=
    ∏ i, exponential p (lens i)^r i := by
  rw [exponential,inner_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _; rw [inner_smul_right, ← mul_neg, Real.exp_nat_mul] -- ]]

abbrev gen (p : E4) (i : Axis) := exponential p (lens i)
lemma box_mem {p : E4} (hp : p∈cone) : gen p ∈ supportC :=
   ⟨fun _ => (Real.exp_pos _).le,fun _ => exponential_sub_one hp (lens_cone _)⟩
lemma box_time (p : E4) : gen p timeAxis = Real.exp (-(time p)) := by unfold gen exponential; rw [lens_value,if_pos rfl]

def decode (q : Axis→ℝ) : E4 := WithLp.toLp 2 fun i =>
   -Real.log (q i) + if i=timeAxis then 0 else Real.log (q timeAxis)
lemma decode_gen {q : Axis → ℝ} (hq : ∀ i, 0<q i) i : gen (decode q) i = q i := by
  rw [gen,exponential,lens_value,decode]
  have h : time (decode q)= -Real.log (q timeAxis) := by unfold time decode; simp
  change Real.exp (-(if i=timeAxis then time (decode q) else time (decode q)+decode q i))=_
  rw [h]; split_ifs with hi <;> simp [*,decode,Real.exp_log (hq _)]
lemma gen_decode (p : E4) : decode (gen p)=p := by
  ext1 i; unfold decode gen; dsimp only; simp only [exponential,Real.log_exp,lens_value];
  split_ifs <;> simp_all [time,add_comm]
noncomputable instance : CompactSpace cuboid := isCompact_iff_compactSpace.mp isCompact_Icc

noncomputable def monom4 (r : Axis→ℕ) : C(cuboid,ℝ) := ⟨(fun u => ∏ i : Axis, u.val i ^ r i),
  continuous_finsetProd _ (fun i _ => ((continuous_apply (A:=fun _:Axis => ℝ) i).comp continuous_subtype_val).pow _)⟩
@[simp] lemma monom_eval (r) (u : cuboid) : monom4 r u = ∏ i,u.val i^r i := rfl
lemma monom_mul (r t : Axis→ℕ) : monom4 r*monom4 t = monom4 (r+t) := by
  ext1 x; dsimp only [ContinuousMap.mul_apply,monom_eval,Pi.add_apply]
  simp_rw [pow_add,Finset.prod_mul_distrib]

def Alc : Subalgebra ℝ C(cuboid,ℝ) where
   carrier := (Submodule.span ℝ (Set.range monom4)).carrier
   add_mem' := (Submodule.span ..).add_mem
   algebraMap_mem' x := by
     let p := Submodule.span ℝ (Set.range monom4)
     change _ ∈ p
     have hv : algebraMap ℝ C(cuboid,ℝ) x=x • 1 := ContinuousMap.ext (fun _ => by change _ = x*1; rw [mul_one]; rfl)
     rw [hv]
     apply p.smul_mem
     exact Submodule.subset_span ⟨(0 : Axis→ℕ), ContinuousMap.ext (fun _ => by simp [monom_eval])⟩
   mul_mem' hx hy := by
     refine Submodule.span_induction₂ (p:=fun x y _ _=> x*y∈ Submodule.span ℝ (Set.range monom4))
       (s:=Set.range monom4) (t:=Set.range monom4)
       (fun a b (h1 : a∈ range monom4) (h2 : b∈range monom4) => ?_)
       (fun x _=> (zero_mul x).symm ▸ Submodule.zero_mem (_)) (fun y _=>(mul_zero y).symm ▸ Submodule.zero_mem _)
       (fun x y z _ _ _ hx hy=> (add_mul x y z).symm ▸ Submodule.add_mem _ hx hy)
       (fun x y z _ _ _ hx hy=> (mul_add x y z).symm ▸ Submodule.add_mem _ hx hy)
       (fun r x y _ _ hxy => (smul_mul_assoc r x y).symm ▸ (Submodule.span ..).smul_mem r hxy)
       (fun r x y _ _ hxy => (mul_smul_comm r x y).symm ▸ (Submodule.span ..).smul_mem r hxy)
       hx hy
     obtain ⟨i,hi⟩ := h1; obtain ⟨j,hj⟩:= h2
     rw [← hi,← hj,monom_mul]; exact Submodule.subset_span (Set.mem_range_self (f:=monom4) (i+j))
lemma alc_separates : Alc.SeparatesPoints := fun x y hxy => by
   have ⟨i,hi⟩ : ∃ i : Axis, x.val i≠y.val i := not_forall.mp (fun h => hxy (Subtype.ext (funext h)))
   let r (j) : ℕ := if j=i then 1 else 0
   refine ⟨monom4 r, ?_,?_⟩
   · exact ⟨monom4 r,(by change _∈Submodule.span _ _; exact Submodule.subset_span (Set.mem_range_self _) : monom4 r ∈ Alc),rfl⟩
   have he (x : cuboid) : monom4 r x=x.val i := by
     classical
     rw [monom_eval, Finset.prod_eq_single i] <;> simp [r]
     exact fun b hb he => False.elim (hb he)
   rw [he,he]; exact hi

noncomputable def lightMark (p : E4) : cuboid := ⟨fun i => min 1 (gen p i),⟨fun _ => le_min zero_le_one (Real.exp_pos _).le,fun _ => min_le_left ..⟩⟩
lemma mark_on {p : E4} (hp : p∈cone) i : (lightMark p).val i=gen p i := by unfold lightMark; exact min_eq_right ((box_mem hp).2 i)
lemma mark_open (q) : (lightMark q).val timeAxis>0 := lt_min zero_lt_one (Real.exp_pos _)
@[fun_prop] lemma continuous_mark : Continuous lightMark := by refine Continuous.subtype_mk (continuous_pi fun i => Continuous.min ?_ ?_) _ <;> fun_prop
@[fun_prop] lemma continuous_weight (q : C(cuboid,ℝ)) : Continuous (fun p => Real.exp (-(time p)) * q (lightMark p)) := by fun_prop

noncomputable def budget (M : Measure E4) (q : C(cuboid,ℝ)) : ℝ := ∫ p, exponential p (basis timeAxis) * q (lightMark p) ∂M

structure Shadow (M : Measure E4) : Prop where
   future : ∀ᵐ x∂M, x∈cone
   energy (p : E4) (hp : p∈inside) : Integrable (fun x : E4 => exponential x p) M

lemma time_inside : basis timeAxis∈inside := by simp [inside]
lemma inner_time (x : E4) : inner ℝ x (basis timeAxis)=time x := by simp [Mink.pairing,Mink.roll_clock,Mink.roll_space]

lemma Shadow.affords (h : Shadow μ) (q : C(cuboid,ℝ)) : Integrable (fun p : E4 => exponential p (basis timeAxis) * q (lightMark p)) μ := by
  refine ((h.energy _ time_inside).mul_const ‖q‖).mono' ((continuous_exp_abbrev _ |>.mul (q.continuous.comp continuous_mark)).aestronglyMeasurable)
     (ae_of_all _ fun p => ?_)
  rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; gcongr; exact ContinuousMap.norm_coe_le_norm ..
lemma Shadow.plus (h : Shadow μ) (x y : C(cuboid,ℝ)) : budget μ (x+y)=budget μ x+budget μ y := by
  simp [budget,mul_add,MeasureTheory.integral_add (h.affords x) (h.affords y)]
lemma Shadow.times (_h : Shadow μ) (x : C(cuboid,ℝ)) (r : ℝ) : budget μ (r • x)=r*budget μ x := by
  simp [budget, mul_left_comm (exponential _ _), MeasureTheory.integral_const_mul]

lemma budget_monom (h : Shadow μ) (r : Axis→ℕ) :
   let v := (basis timeAxis)+∑ j : Axis, (r j : ℝ) • lens j
   v∈inside ∧ budget μ (monom4 r)=∫ q, exponential q v ∂μ := by
   refine ⟨?_,integral_congr_ae (h.future.mono fun p hp=> ?_)⟩
   · unfold inside
     simp only [mem_setOf_eq,Mink.clock_add,Mink.roll_clock,Mink.rest_add,Mink.roll_space,zero_add]
     have he : ∀ j, 0 ≤ (r j:ℝ) := by intro; positivity
     suffices H : ∀ q : Finset Axis, ‖spatial (∑ j∈q, (r j:ℝ) • lens j)‖ ≤ time (∑ j∈q, (r j:ℝ) • lens j) by
          linarith [H Finset.univ]
     classical
     intro q
     induction q using Finset.induction_on with
     | empty => simp
     | insert i q hi hq =>
       rw [Finset.sum_insert hi,Mink.clock_add,Mink.rest_add,Mink.rest_mul,Mink.clock_mul]
       apply (norm_add_le ..).trans
       rw [norm_smul,Real.norm_of_nonneg (he _)]
       have hi := lens_cone i; exact add_le_add (mul_le_mul_of_nonneg_left hi (he i)) hq
   dsimp only [monom_eval]
   simp_rw [mark_on hp]
   unfold exponential gen
   rw [inner_add_right,neg_add,Real.exp_add]
   exact congr_arg (rexp (-⟪p,basis _⟫_ℝ) * ·) (exponential_express p r).symm


lemma budget_le (h : Shadow μ) (q : C(cuboid,ℝ)) : |budget μ q| ≤ budget μ 1 * ‖q‖ := by
   rw [budget, budget]
   simp_rw [ContinuousMap.one_apply,mul_one]
   refine abs_integral_le_integral_abs.trans ?_
   rw [← MeasureTheory.integral_mul_const]
   apply MeasureTheory.integral_mono (h.affords q).norm (MeasureTheory.Integrable.mul_const (h.energy _ time_inside) _)
      (fun x => ?_)
   dsimp only; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm ..) (Real.exp_pos _).le

structure Match (M : α → Measure E4) (μ : Measure E4) (l : Filter α) : Prop where
    first : Shadow μ
    after : ∀ᶠ v in l, Shadow (M v)
    tends (p) : p∈inside → Tendsto (fun i => ∫ x, exponential x p ∂M i) l (𝓝 (∫ x, exponential x p ∂μ))
lemma Match.coords (h : Match M μ l) {q} (hq : q∈Alc) : Tendsto (fun i => budget (M i) q) l (𝓝 (budget μ q)) := by
   induction hq using Submodule.span_induction with -- non-matching?
   | mem q hq =>
        obtain ⟨r,rfl⟩ := hq; have hv := budget_monom h.first r
        rw [hv.2]
        exact (h.tends _ hv.1).congr' (h.after.mono (fun i hi=>(budget_monom hi r).2.symm))
   | zero => simpa [budget] using tendsto_const_nhds
   | add x y hx hy a b =>
      rw [h.first.plus]; exact (a.add b).congr' (h.after.mono fun i hy => (hy.plus ..).symm)
   | smul r x hx t =>
      rw [h.first.times]; exact (t.const_mul _).congr' (h.after.mono fun i hy => (hy.times ..).symm)
lemma Match.compactBox (h : Match M μ l) (q) : Tendsto (fun i => budget (M i) q) l (𝓝 (budget μ q)) := by
   rw [Metric.tendsto_nhds]
   intro ε hε
   let K := budget μ 1 + 1
   have Kpos : 0<K := by dsimp [K,budget]; positivity
   let e := ε/(4*K)
   have he : 0<e := div_pos hε (by linarith)
   obtain ⟨p,hp⟩ := @ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints cuboid _ instCompactSpaceCuboid Alc alc_separates q e he
   filter_upwards [h.after, h.coords Alc.one_mem|>.eventually (gt_mem_nhds (show budget μ 1 < K by unfold K; linarith)),
       h.coords p.property |>.eventually (Metric.ball_mem_nhds _ (by linarith : 0<ε/2))] with i hi hh hδ
   rw [Real.dist_eq]
   have hu (Y) (hf : Shadow Y) (hb : budget Y 1 ≤ K): |budget Y q - budget Y (↑p)| ≤ K*e := by
      rw [← Real.norm_eq_abs, norm_sub_rev, Real.norm_eq_abs, ← show budget Y ((p:C(cuboid,ℝ)) - q) = budget Y (p:C(cuboid,ℝ)) - budget Y q from by
            rw [sub_eq_add_neg, hf.plus, ← neg_one_smul ℝ q,hf.times]; ring]
      exact (budget_le hf _).trans (mul_le_mul hb hp.le (by positivity) Kpos.le)
   calc _ = |(budget (M i) q-budget (M i) (p:C(cuboid,ℝ)))+(budget (M i) p-budget μ p)+(budget μ p-budget μ q)| := congrArg _ (by ring)
        _ ≤ _ := abs_add_le ..
        _ ≤ |budget (M i) q-budget (M i) p|+|budget (M i) p-budget μ p|+|budget μ q-budget μ p| :=
             add_le_add (abs_add_le ..) (le_of_eq (abs_sub_comm ..))
        _ < K*e + ε/2 + K*e := add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt (hu _ hi (by exact LT.lt.le hh))
               (by simpa [Real.dist_eq] using hδ)) (hu _ h.first (by dsimp [K]; linarith))
        _ = ε := by dsimp [e]; field_simp; ring



noncomputable def restoreRaw (φ : E4→ℝ) (x : Axis → ℝ) := if ∀ i, 0<x i then
    φ (decode x)*(x timeAxis)⁻¹ else 0
lemma restore_continuous (φ : E4→ℝ) (hc : Continuous φ) (ht : HasCompactSupport φ) : Continuous (restoreRaw φ) := by
   let s := {x : Axis→ℝ| ∀ i, x i∈Ioi (0:ℝ)}
   have hS : IsOpen s := by
      simp_rw [s, setOf_forall]; exact isOpen_iInter_of_finite (fun i=> isOpen_Ioi.preimage (continuous_apply i)) -- fix
   let D x := φ (decode x)*(x timeAxis)⁻¹
   obtain ⟨r,hr⟩ := ht.isCompact.isBounded.subset_ball 0
   have hz (x) (k : Axis) (x1 : x∈s) (hx : x k < Real.exp (-(r*3))) : D x=0 := by
       suffices hq : φ (decode x)=0 by simp only [D,hq,zero_mul]
       apply image_eq_zero_of_notMem_tsupport
       intro hp
       let y := decode x
       have he : rexp (-inner ℝ y (lens k)) < rexp (-(r*3)) := (by rw [show rexp _= x k from decode_gen x1 k]; exact hx)
       have he := Real.exp_lt_exp.mp he
       have hr := Metric.mem_ball.mp (hr hp); rw [dist_zero_right] at hr
       change ‖y‖<r at hr
       have hlen := calc ⟪y, lens k⟫_ℝ ≤ _ := real_inner_le_norm y (lens k)
                        _ ≤ ‖y‖*3 := mul_le_mul_of_nonneg_left (lens_bound k) (norm_nonneg _)
                        _ ≤ r*3 := mul_le_mul_of_nonneg_right hr.le (by norm_num)
       linarith
   refine continuous_iff_continuousAt.mpr fun q=> ?_
   by_cases h : q∈s
   swap; · obtain ⟨i,hi⟩ := not_forall.mp h
           apply ContinuousAt.congr_of_eventuallyEq (f:=fun _ : Axis→ℝ => (0:ℝ)) continuousAt_const
             (((continuous_apply (A:=fun _ => ℝ) i).tendsto q).eventually (gt_mem_nhds (a:=rexp (-(r*3))) ?_) |>.mono fun w hw => ?_)
           · exact le_of_not_gt hi |>.trans_lt (Real.exp_pos _)
           by_cases hq : w∈s
           · change ∀ i, 0<w i at hq; rw [restoreRaw,if_pos hq]
             exact hz _ i hq hw
           change ¬∀ i, 0<w i at hq
           simp only [restoreRaw,if_neg hq]
   have hm : ContinuousAt decode q := by
       unfold decode
       refine (PiLp.continuous_toLp 2 (fun _ : Axis => ℝ)).continuousAt.comp (continuousAt_pi.mpr fun i=> ?_)
       have HC (k : Axis) := (Real.continuousAt_log (h k).ne').comp (f:=fun u : Axis→ℝ => u k) ((continuous_apply (A:=fun _:Axis=>ℝ) k).continuousAt (x:=q))
       by_cases hi : i=timeAxis
       · simp only [if_pos hi,add_zero]; exact (HC i).neg
       exact (by simp only [if_neg hi]; exact (HC _).neg.add (HC _))
   exact ContinuousAt.congr_of_eventuallyEq ((hc.continuousAt.comp hm).mul ((continuous_apply timeAxis).continuousAt.inv₀ (h _).ne'))
      (Filter.Eventually.mono (hS.mem_nhds h) (fun q hv => by change ∀ i, 0<q i at hv; rw [restoreRaw,if_pos hv]; rfl))

def restore (φ : E4→ℝ) (hc : Continuous φ) (ht : HasCompactSupport φ) : C(cuboid,ℝ) := ⟨restoreRaw φ ∘ Subtype.val,
    (restore_continuous φ hc ht).comp continuous_subtype_val⟩
lemma restores (φ : E4→ℝ) (hc : Continuous φ) (ht : HasCompactSupport φ) (p : E4) (hp : p∈cone) :
    exponential p (basis timeAxis) * restore φ hc ht (lightMark p)=φ p := by
   have h : (lightMark p).val=gen p := funext (mark_on hp)
   change exponential .. * restoreRaw .. = _
   simp only [h,restoreRaw,gen_decode,box_time,exponential,inner_time p, if_pos (show ∀ i, 0< gen p i from fun _=>Real.exp_pos _)] -- may struggle
   field_simp

lemma Match.vague (h : Match M μ l) (f : E4 → ℝ) (hs : HasCompactSupport f) (hc : Continuous f) :
    Tendsto (fun i => ∫ p,f p ∂M i) l (𝓝 (∫ p,f p ∂μ)) := by
   let t := restore f hc hs
   have hh (μ : Measure E4) (h : Shadow μ) : ∫ p, f p ∂μ=budget μ t := integral_congr_ae (h.future.mono
        fun p hp=> (restores f hc hs p hp).symm)
   rw [hh μ h.first]
   exact Tendsto.congr' (h.after.mono fun i hi => (hh _ hi).symm) (h.compactBox _)
lemma Measure.integrable_cpt (μ : Measure E4) [IsFiniteMeasureOnCompacts μ] {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (f : E4→E) (hf : Continuous f) (hc : HasCompactSupport f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport hc
lemma Shadow.tempered_budget (_h : Shadow μ) (hv : IsFiniteMeasureOnCompacts μ) (f : E4→ℂ) (hc : Continuous f)
    (hs : HasCompactSupport f) :
    (∫ p,f p ∂μ) = (∫ p, (f p).re ∂μ) + (∫ p, (f p).im ∂μ) * Complex.I := by
   letI := hv
   have hi := hc.integrable_of_hasCompactSupport hs (μ:=μ)
   rw [← Complex.re_add_im (∫x,f x∂μ), ← RCLike.re_to_complex, ← RCLike.im_to_complex, ← _root_.integral_re hi, ← _root_.integral_im hi]
   rfl
lemma Match.vagueC (h : Match M μ l) (hρ : ∀ᶠ i in l, IsFiniteMeasureOnCompacts (M i))
    (hc' : IsFiniteMeasureOnCompacts μ) (f : E4→ℂ) (hc : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun i => ∫ p,f p ∂M i) l (𝓝 (∫ p, f p∂μ)) := by
    classical
    have H (g : ℂ → ℝ) (hh : Continuous g) (hv : g 0=0) : Tendsto (fun i=>((↑(∫x, g (f x)∂M i)) : ℂ)) l (𝓝 ((↑(∫x,g (f x)∂μ)):ℂ)) :=
       Complex.continuous_ofReal.continuousAt.tendsto.comp (h.vague (g ∘ f) (hs.comp_left hv) (hh.comp hc))
    rw [h.first.tempered_budget hc' f hc hs]
    refine Tendsto.congr' ?_ ((H _ Complex.continuous_re rfl).add ((H _ Complex.continuous_im rfl).mul_const Complex.I))
    filter_upwards [hρ,h.after] with i hi hS
    exact (hS.tempered_budget hi f hc hs).symm

lemma Growth.shadow {A : ℝ≥0∞} {n} (h : Growth μ A n) (ha : A<⊤) (he : ∀ᵐ x∂μ,x∈cone) : Shadow μ where
   future := he
   energy x hx := by
      have hb : 0<time x-‖spatial x‖ := sub_pos.mpr hx
      have ht : Tempered μ := ⟨n,A.toReal,by rw [ENNReal.ofReal_toReal ha.ne]; exact h⟩
      have HC : μ coneᶜ = 0 := ae_iff.mp he
      refine Tempered.integrable_exp μ ht HC hb |>.mono' (by unfold exponential; fun_prop) (he.mono fun p hp => ?_)
      dsimp only [exponential]; rw [Real.norm_of_nonneg ((Real.exp_pos _).le)]
      apply exp_le_exp.mpr
      rw [Mink.pairing]
      have ht := (abs_le.mp (abs_real_inner_le_norm (spatial p) (spatial x))).1
      have he := mul_le_mul_of_nonneg_right (show _≤_ from hp) (norm_nonneg (spatial x)) -- deduction
      linarith
lemma Thermal.matches {A : ℝ} (h : Thermal μ A) {ν} (hx : Shadow ν)
     (hh : ∀ x∈inside, (∫ p, exponential p x∂ν) = A / (Mink.m x)^4) : Match (rescaled μ) ν atTop := by
   obtain ⟨C,hC,hG⟩:=h.growth_bound
   refine ⟨hx, ((eventually_gt_atTop (0:ℝ)).and hG).mono fun i hi => hi.2.shadow hC (h.cones hi.1),fun x hx => ?_⟩
   rw [hh x hx]; exact h.timelike x hx

lemma Growth.test_abs {n A} (h : Growth μ A n) (ha : A < ⊤) (f : Probe E4) : ‖∫ p, f p∂μ‖ ≤
    (orderCost f (n+1)*2^(n+1)) * (A.toReal * 2^(n+1)) := by
   refine norm_integral_le_integral_norm f |>.trans (le_trans (b:=∫ x:E4,_∂μ) (integral_mono
     (h.integrable_schwartz ha f |>.norm) ((h.integrable_weight μ ha).const_mul _) (weighted_test f (n+1))) ?_)
   rw [MeasureTheory.integral_const_mul]
   apply mul_le_mul_of_nonneg_left _ (mul_nonneg (orderCost_nonneg f _) (by positivity))
   have ht : ∀ᵐ p∂μ, 0≤ (weight (n+1) p)⁻¹ := ae_of_all _ fun p => (inv_pos.mpr (weight_pos _ _) |>.le)
   rw [integral_eq_lintegral_of_nonneg_ae ht (by unfold weight; fun_prop)]
   exact ENNReal.toReal_mono (by finiteness : 2^(n+1)*A ≠ ⊤) (h.total_weight μ A n) |>.trans_eq (by simp [ENNReal.toReal_mul,ENNReal.toReal_pow,mul_comm])

lemma Match.schwartz (h : Match M μ l) {A B : ℝ≥0∞} {n m} (ha : A<⊤) (hb : B<⊤) (hn : ∀ᶠ i in l, Growth (M i) A n)
    (hs : Growth μ B m) (f : Probe E4) : Tendsto (fun i => ∫ p,f p∂M i) l (𝓝 (∫ p, f p∂μ)) := by
   rw [Metric.tendsto_nhds]; intro e he
   let D (k : ℕ) (X : ℝ≥0∞) := ((2:ℝ)^(k+1))*(X.toReal * ((2:ℝ)^(k+1))) + 1
   let C := max (D n A) (D m B)
   have hC : 0<C := lt_of_lt_of_le (by dsimp [D]; positivity) (le_max_left (D n A) (D m B))
   have hu := ((cutTest_limit f).sub (tendsto_const_nhds (x:=f)))
   simp_rw [sub_self] at hu
   have hl k := (continuous_orderCost (V:=E4) k).continuousAt.tendsto.comp hu |>.eventually (gt_mem_nhds (a:=e/(4*C)) (by
      change orderCost 0 k < _; rw [orderCost]; simp only [Probe.size,map_zero,zero_add]; positivity))
   obtain ⟨s,hv₁,hv₂⟩ := ((hl (n+1)).and (hl (m+1))).exists
   let g := cutTest f s
   have hg (μ : Measure E4) (k X) (hx : Growth μ X k ∧ X < ⊤) (hx' : (2:ℝ)^(k+1)*(X.toReal * 2^(k+1)) ≤ C) (hg : orderCost (g-f) (k+1) ≤ e/(4*C)) :
       ‖(∫ p,f p∂μ)-(∫ p,g p∂μ)‖ ≤ e/(4:ℝ) := by
       rw [norm_sub_rev,← MeasureTheory.integral_sub (hx.1.integrable_schwartz hx.2 _) (hx.1.integrable_schwartz hx.2 _)]
       exact (hx.1.test_abs hx.2 (g-f)).trans (by
          rw [mul_assoc]
          calc _ ≤ (e/(4*C))*C := mul_le_mul hg hx' (by positivity) (by positivity)
               _ = _ := by field_simp)
   have hR := h.vagueC (hn.mono (fun i hi=> hi.finite_compacts ha.ne)) (hs.finite_compacts hb.ne) g g.continuous (cutTest_CC ..)
   filter_upwards [hn,hR.eventually (Metric.ball_mem_nhds _ (ε:=e/2) (half_pos he))] with i hi hx -- arg name ε?
   rw [dist_eq_norm_sub] at hx
   rw [dist_eq_norm_sub]
   have he1 := hg _ _ _ ⟨hi,ha⟩ ((lt_add_one _).le.trans (le_max_left (D n A) _)) hv₁.le
   have he2 := hg _ _ _ ⟨hs,hb⟩ ((lt_add_one _).le.trans (le_max_right _ (D m B))) hv₂.le
   rw [norm_sub_rev] at he2
   calc _ = ‖((∫ p,f p ∂M i)-(∫ p,g p ∂M i)) + ((∫ p,g p∂M i)-(∫ p,g p∂μ)) + ((∫ p,g p∂μ)-(∫ p,f p∂μ))‖ := by congr 1 <;> abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) he2
        _ < e/4+ e/2+e/4 := add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt he1 hx) le_rfl
        _ = e := by ring
end YM.Trace
