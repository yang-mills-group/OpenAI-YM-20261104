import YM.Next.RANK.Exponential
import YM.Pert.Attach.Fusion
/-! # Marked prices for mask-change attachments

Use componentwise upper envelopes, so sums of suprema are controlled,
not just a supremum of the marker polynomial norm. Work in the same
marker algebra. Continuity/norm comparison at fixed finite marker set
elsewhere never affects these prices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Markers
open Function Lattice RG Wilson MeasureTheory Filter Marker Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V : Type} [DecidableEq V] {R : Census V} {n : Side}

def embedded (R : Census V) (z : ℝ) : Poly R:= Poly.bead R (z:ℂ)
attribute [local simp] Poly.product_bead Next.Rank.Exponential.part_sub

@[simp] lemma embedded_zero : embedded R 0=0 := by simp [embedded]
@[simp] lemma embedded_one : embedded R 1=1 := by simp [embedded]
lemma embedded_neg (s : ℝ) : embedded R (-s) = -embedded R s := by simp [embedded]
lemma embedded_mul (s t : ℝ) : embedded R (s*t)=embedded R s*embedded R t := by simp only [embedded,Complex.ofReal_mul,map_mul]
lemma embedded_sub (s t : ℝ) : embedded R (s-t)=embedded R s-embedded R t := by simp only [embedded,Complex.ofReal_sub,map_sub]
@[simp] lemma embedded_part (s : ℝ) (i : R.Mode) : (embedded R s).part i= if i=R.quiet then (s:ℂ) else 0 := Poly.part_send ..
lemma embedded_price (w : V→ℝ) (s : ℝ) : Poly.price w (embedded R s)=|s| := by
  unfold embedded; change Poly.price w (Poly.send _ _)= _
  simp [Poly.quiet_toll]

lemma embedded_cont : Continuous (embedded R) := by
  change Continuous (fun t : ℝ => ((Poly.bead R (t:ℂ):Poly R).part))
  apply continuous_pi; intro i; simp only [show ∀ t,Poly.part (Poly.bead R (t:ℂ)) i=if i=R.quiet then t else 0 from fun t=> Poly.part_send ..]; split; fun_prop; fun_prop

/-- Componentwise POSITIVE majorants in the same algebra, no cancellation. -/
structure Over (a b : Poly R) : Prop where
  upper (i) : ‖a.part i‖ ≤ (b.part i).re
  genuine (i) : (b.part i).im=0

lemma Over.nneg {x y : Poly R} (h : Over x y) (i) : 0≤(y.part i).re := (norm_nonneg _).trans (h.upper i)
lemma Over.norm_eq {x y : Poly R} (h : Over x y) (i) : ‖y.part i‖= (y.part i).re:= by
  have he: ((y.part i).re:ℂ)=y.part i:=Complex.ext rfl (h.genuine i).symm
  rw [← he,Complex.norm_real,Real.norm_of_nonneg (h.nneg _), Complex.ofReal_re]
lemma Over.norm {x y : Poly R} (h : Over x y) (i) : ‖x.part i‖ ≤ ‖y.part i‖ := (h.upper i).trans_eq (h.norm_eq i).symm
lemma Over.zeroLeft {x y : Poly R} (h : Over x y) : Over 0 y:= ⟨fun i => by simp only [Poly.part_nil,norm_zero]; exact h.nneg i,h.genuine⟩

lemma Over.add {a b c d : Poly R} (h : Over a b) (hp : Over c d) : Over (a+c) (b+d) := by
  refine ⟨fun i=>?_,fun i=>by rw [Poly.part_plus,Complex.add_im,h.genuine,hp.genuine,add_zero]⟩
  rw [Poly.part_plus,Poly.part_plus,Complex.add_re]; exact (norm_add_le ..).trans (add_le_add (h.upper _) (hp.upper _))

private lemma positiveSum {ι : Type} (s : Finset ι) (a b : ι → ℂ)
    (hh : ∀ i∈s,(b i).im=0 ∧ ‖a i‖ ≤ (b i).re) :
    (∑ i∈s,b i).im=0 ∧ ‖∑ i∈s, a i‖ ≤ (∑ i∈s,b i).re := by
  simp only [Complex.im_sum,Complex.re_sum]
  exact ⟨sum_eq_zero (fun i hi=>(hh i hi).1),(norm_sum_le ..).trans (sum_le_sum fun i hi=>(hh i hi).2)⟩

lemma Over.mul {a b c d : Poly R} (h : Over a b) (hp : Over c d) : Over (a*c) (b*d) := by
  have he i : ((b*d).part i).im=0∧ ‖(a*c).part i‖≤ ((b*d).part i).re:= by
    rw [Poly.part_mul,Poly.part_mul]; apply positiveSum; intro y _; apply positiveSum; intro z _; split_ifs
    · simp only [Complex.mul_im,h.genuine,hp.genuine,mul_zero,zero_mul,add_zero,Complex.mul_re,sub_zero,norm_mul]
      exact ⟨trivial,mul_le_mul (h.upper _) (hp.upper _) (norm_nonneg _) (h.nneg _)⟩
    simp
  exact ⟨fun i=>(he i).2,fun i=>(he i).1⟩
lemma Over.embed {s t : ℝ} (h : |s| ≤ t) : Over (embedded R s) (embedded R t) := by
  refine ⟨fun i=>?_,fun i=>?_⟩ <;> by_cases he:i=R.quiet <;> simp [he,h]
lemma Over.scale {s t : ℝ} {a b : Poly R} (he : Over a b) (h : |s| ≤ t) : Over ((s:ℂ) • a) ((t:ℂ) • b) := by
  rw [← Poly.product_bead,← Poly.product_bead]; exact (Over.embed h).mul he
lemma over_unit : Over (1:Poly R) 1 := by simpa using Over.embed (R:=R) (s:=1) (t:=1) (by simp)
lemma Over.sum {ι : Type} (s : Finset ι) {a b : ι → Poly R} (h : ∀ i∈s,Over (a i) (b i)) :
    Over (∑ i∈s,a i) (∑ i∈s,b i) := by
  induction s using Finset.induction_on with
  | empty=>
    simp only [sum_empty]; exact ⟨fun _=>by simp,fun _=>by simp⟩
  | insert i s he ih=> rw [sum_insert he,sum_insert he]; exact (h i (mem_insert_self ..)).add (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma Over.prod {ι : Type} (s : Finset ι) {a b : ι→ Poly R} (h : ∀ i∈s,Over (a i) (b i)) :
    Over (∏ i∈s,a i) (∏ i∈s,b i) := by
  induction s using Finset.induction_on with
  | empty=> simp only [prod_empty]; exact over_unit
  | insert i s he ih=> rw [prod_insert he,prod_insert he]; exact (h i (mem_insert_self ..)).mul (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma Over.pow {a b : Poly R} (h : Over a b) (k : ℕ) : Over (a^k) (b^k) := by
  induction k with
  | zero=> simpa only [pow_zero] using! over_unit
  | succ i ih=> rw [pow_succ,pow_succ]; exact ih.mul h
lemma Over.price {a b : Poly R} (h : Over a b) {w : V→ℝ} (hw : ∀ i,0<w i) : Poly.price w a ≤ Poly.price w b := by
  unfold Poly.price; exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (h.norm _) (Poly.worth hw i).le

variable (O : V → Support n)

def Carries (X : Support n) (a : Poly R) := ∀ i (j:V), j∈i.val → ¬(O j ⊆ X) → a.part i = 0

section
variable {O} {a b : Poly R} {X Y:Support n}
lemma Carries.more (h : Carries O X a) (ht : X⊆Y) : Carries O Y a:= fun i j hv hc=> h i j hv (fun H=> hc (H.trans ht))
lemma Carries.plus (h : Carries O X a) (hf : Carries O X b) : Carries O X (a+b) := by
  intro i j he hv; rw [Poly.part_plus,h i j he hv,hf i j he hv,zero_add]
lemma Carries.sub (h : Carries O X a) (hf : Carries O X b) : Carries O X (a-b) := by
  intro i j he hv; rw [Next.Rank.Exponential.part_sub,h i j he hv,hf i j he hv,sub_self]
lemma carry_embed (z : ℝ) : Carries O X (embedded R z) := by
  intro i j hj _; have he:i≠R.quiet := fun h=> notMem_empty j (show j∈R.quiet.val from h ▸ hj)
  rw [embedded_part,if_neg he]
lemma carry_unit : Carries O X (1:Poly R) := by simpa only [embedded_one] using (carry_embed (O:=O) (X:=X) 1)
lemma carry_zero : Carries O X (0:Poly R) := by simpa only [embedded_zero] using (carry_embed (O:=O) (X:=X) 0)
lemma Carries.smul (h : Carries O X a) (s : ℂ) : Carries O X (s • a) := by
  intro i j he hv; rw [Poly.part_smul,h i j he hv,mul_zero]
lemma Carries.mul (h : Carries O X a) (hf : Carries O X b) : Carries O X (a*b) := by
  intro i j hj hp; rw [Poly.part_mul]; refine Finset.sum_eq_zero fun k _=>Finset.sum_eq_zero fun v _=>?_
  split
  next hs=> rw [← hs.2] at hj; rcases mem_union.mp hj with hh|hh; rw [h k j hh hp,zero_mul]; rw [hf v j hh hp,mul_zero]
  rfl
lemma Carries.sum {ι: Type*} (s : Finset ι) {A : ι→ Poly R} (h : ∀ i∈s,Carries O X (A i)) : Carries O X (∑ i∈s,A i) := by
  intro j k hk hK; simp only [Poly.part_sum]; exact sum_eq_zero fun i hi=>h i hi j k hk hK
lemma Carries.pow (h : Carries O X a) (s : ℕ) : Carries O X (a^s) := by
  induction s with
  | zero=>rw [pow_zero]; exact carry_unit
  | succ i ih=> rw [pow_succ]; exact ih.mul h
lemma Carries.prod {ι: Type*} (s : Finset ι) {A : ι→ Poly R} (h : ∀ i∈s,Carries O X (A i)) : Carries O X (∏ i∈s,A i) := by
  induction s using Finset.induction_on with
  | empty=> simp only [prod_empty]; exact carry_unit
  | insert i s he ih=> rw [prod_insert he]; exact (h i (mem_insert_self ..)).mul (ih fun i hi=>h i (mem_insert_of_mem hi))
end
variable [Fintype V]
lemma Over.pass {a b : Poly R} (h : Over a b) : Over (Poly.pass a) (Poly.pass b) := by
  apply Over.sum; intro i _; convert (h.pow i).scale (show |(i.factorial:ℝ)⁻¹| ≤ (i.factorial:ℝ)⁻¹ by rw [abs_of_nonneg (by positivity)]) using 1 <;> simp
lemma Over.passing {a b : Poly R} (ha : a.part R.quiet=0) (hb : b.part R.quiet=0) (h : Over a b) :
    Over (Poly.pass a-1) (Poly.pass b-1) := by
  refine ⟨fun i=>?_,fun i=>?_⟩ <;> by_cases hk:i=R.quiet
  · simp [hk,Poly.pass_part a ha,Poly.pass_part b hb]
  · simpa [hk] using (h.pass.upper i)
  · simp [hk,Poly.pass_part b hb]
  simpa [hk] using (h.pass.genuine i)
lemma Carries.pass (X) (a : Poly R) (h : Carries O X a) : Carries O X (Poly.pass a) :=
  Carries.sum _ fun i _=> (h.pow i).smul _

def magnify (s : ℝ) (a : Poly R) : Poly R := embedded R (Real.exp s) * Poly.pass a
def companion (s : ℝ) (a : Poly R) : Poly R := magnify s a-1

def stipend (c : ℝ) (a : Poly R) := embedded R (Real.exp c-1)+embedded R (Real.exp c)*(Poly.pass a-1)
lemma stipend_eq (c : ℝ) (a : Poly R) : stipend c a= companion c a:= by unfold stipend companion magnify; rw [embedded_sub,embedded_one]; ring

private lemma exp_abs {s d : ℝ} (h : |s| ≤ d) : |Real.exp s-1| ≤ Real.exp d-1 := by
  obtain ⟨hr,hp⟩:= abs_le.mp h
  apply abs_le.mpr
  have he := Real.exp_le_exp.mpr hr
  have ht : 1 ≤ Real.exp d := Real.one_le_exp (by linarith)
  constructor
  · rw [Real.exp_neg] at he
    suffices 2 - Real.exp d ≤ (Real.exp d)⁻¹ by linarith
    calc 2-Real.exp d ≤ 1/Real.exp d := (le_div_iff₀ (Real.exp_pos _)).2 (by nlinarith only [sq_nonneg (Real.exp d-1)])
         _ = _:= one_div ..
  linarith [Real.exp_le_exp.mpr hp]

@[simp] lemma quiet_companion {a : Poly R} (s : ℝ) (h : a.part R.quiet=0) : (companion s a).part R.quiet= ↑(Real.exp s-1) := by
  simp only [companion,magnify,Next.Rank.Exponential.part_sub, Poly.quiet_mul,Poly.pass_part a h,embedded_part,Poly.one_part]; simp

lemma Over.companion {a b : Poly R} {s t : ℝ} (hs : |s| ≤ t) (h : Over a b) (hf : a.part R.quiet=0) (hg : b.part R.quiet=0) :
    Over (Markers.companion s a) (Markers.companion t b) := by
  rw [← stipend_eq,← stipend_eq]; apply add (embed (exp_abs hs))
  exact (embed (show |Real.exp s| ≤ Real.exp t from by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_monotone ((le_abs_self s).trans hs))).mul (h.passing hf hg)

lemma Carries.companion {a : Poly R} {s : ℝ} {X : Support n} (h : Carries O X a) : Carries O X (Markers.companion s a) :=
  (Carries.mul (carry_embed _) (h.pass _ _)).sub carry_unit

lemma companion_bound {w : V→ℝ} {a : Poly R} (hw : ∀ i,0<w i) (h : a.part R.quiet=0) {t : ℝ} (ht : 0≤ t) :
    Poly.price w (companion t a) ≤ Real.exp (t+Poly.price w a)-1 := by
  let P:= Poly.pass a
  have hz : Poly.price w (P-1)+1=Poly.price w P := by
    unfold Poly.price; rw [← add_sum_erase _ _ (mem_univ R.quiet)]; conv_rhs => rw [← add_sum_erase _ _ (mem_univ R.quiet)]
    rw [sum_congr rfl (g:=fun i=>Poly.toll w i * ‖P.part i‖) (fun i hi=> by simp [(mem_erase.mp hi).1])]
    simp only [P,Next.Rank.Exponential.part_sub,Poly.pass_part a h]; simp [add_comm]
  have he:= Poly.pass_budget hw a
  rw [← stipend_eq]; refine (Poly.addition hw ..).trans ((add_le_add le_rfl (Poly.multiplication hw ..)).trans ?_)
  rw [embedded_price,embedded_price,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht)),abs_of_pos (Real.exp_pos _),Real.exp_add]; change Real.exp t-1+Real.exp t * Poly.price w (P-1)≤ _
  change Poly.price w P≤_ at he; rw [←hz] at he
  nlinarith only [mul_le_mul_of_nonneg_left he (Real.exp_pos t).le]
end YM.Comparison.Density.Markers
