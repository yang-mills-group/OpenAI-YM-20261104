import YM.RG11Proof.Rate.Finite
/-!
# Errors attached to still unbounded coefficients

Raw cover-stencil solves can cost POWER-divergent ratios as the regulator
is removed. They may not be treated as polylog bounds multiplying a nominal
remainder. `Carry k weigh` means a defect paid at cost (1+weigh(current-order
coefficients)) times k.E, with no uniform bound whatever implicit on `weigh`.
At each transition use the free detector to attach the still unknown
coefficient cost to the left and absorb it before passing to higher orders.
See `absorb` for a reusable finite-field l1 implementation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rate
open Filter
open scoped Topology BigOperators Classical

variable {α I : Type*} {k : Budget α} {w : α→ℝ} {f g p q : α→ℝ}

-- Use absolute values to make monotonicity independent of any cone convention.
def Carry (k : Budget α) (w f g : α→ℝ) :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in k.along, |f a-g a| ≤ C*k.E a * (1+|w a|)

/-- Growth allowed at unknown coefficient. -/
def Burden (k : Budget α) (w f : α→ℝ) := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in k.along, |f a| ≤ C * (1+|w a|)

theorem NearFn.carry (h : NearFn k f g) (w : α→ℝ) : Carry k w f g := by
  obtain ⟨C,hc,H⟩:=h; refine ⟨C,hc,?_⟩
  filter_upwards [H,k.currency] with a h ha
  exact h.trans (le_mul_of_one_le_right (mul_nonneg hc ha) (by linarith [abs_nonneg (w a)]))

namespace Burden

theorem of_bounded (h : Bounded k f) : Burden k w f := by
  obtain ⟨C,hc,H⟩:=h; exact ⟨C,hc,H.mono fun a hi=> hi.trans (le_mul_of_one_le_right hc (by linarith [abs_nonneg (w a)]))⟩

theorem dominated (h : Burden k w f) (H : ∀ᶠ a in k.along, |g a| ≤ |f a|) : Burden k w g := by
  obtain ⟨L,hL,h⟩:=h; exact ⟨L,hL,(H.and h).mono fun _ ⟨he,hj⟩=> he.trans hj⟩

theorem self (k : Budget α) (w:α→ℝ) : Burden k w w :=⟨1,by norm_num,Eventually.of_forall (fun _=>by linarith)⟩

theorem mult_right (h : Burden k w f) (hh : Bounded k g) : Burden k w (fun a=>f a*g a) := by
  obtain ⟨C,hc,h⟩:=h; obtain ⟨D,hd,H⟩:=hh
  refine ⟨C*D,by positivity,?_⟩; filter_upwards [h,H] with a he hj
  rw [abs_mul,mul_right_comm C]
  exact mul_le_mul he hj (abs_nonneg _) (by positivity)

theorem mult_left (h : Burden k w g) (hh : Bounded k f) : Burden k w (fun a=>f a*g a) := by
  simpa only [mul_comm] using h.mult_right hh

theorem add (h : Burden k w f) (he : Burden k w g) : Burden k w (fun a=>f a+g a) := by
  obtain ⟨C,hc,h⟩:=h; obtain ⟨D,hd,H⟩:=he; refine ⟨C+D,by positivity,?_⟩
  filter_upwards [h,H] with a he hj
  rw [add_mul]; exact (abs_add_le ..).trans (add_le_add he hj)

theorem neg (h : Burden k w f) : Burden k w (fun a=> -f a) := by simpa [Burden] using h

theorem sub (h : Burden k w f) (he : Burden k w g) : Burden k w (fun a=>f a-g a) := by simp_rw [sub_eq_add_neg]; exact h.add he.neg
end Burden

namespace Carry
@[refl] theorem refl (f : α→ℝ) : Carry k w f f := (NearFn.refl _).carry _
@[symm] theorem symm (h : Carry k w f g) : Carry k w g f := by simpa only [Carry,abs_sub_comm] using h

theorem trans (h : Carry k w f g) (h' : Carry k w g p) : Carry k w f p := by
  obtain ⟨C,hc,h⟩:=h; obtain ⟨D,hd,H⟩:=h'
  refine ⟨C+D,by linarith,?_⟩; filter_upwards [h,H] with a ha hj
  rw [add_mul,add_mul]; exact (abs_sub_le ..).trans (add_le_add ha hj)

theorem add (H : Carry k w f g) (h : Carry k w p q) : Carry k w (fun a=>f a+p a) (fun a=>g a+q a) := by
  obtain ⟨C,hc,hf⟩:=H; obtain ⟨D,hd,h⟩:=h
  refine ⟨C+D,by linarith,?_⟩; filter_upwards [hf,h] with a hx hy
  rw [add_mul,add_mul,show f a+p a - (g a+_)= f a-g a+(p a-q a) by abel]
  exact (abs_add_le ..).trans (add_le_add hx hy)

theorem neg (h : Carry k w f g) : Carry k w (fun a=> -f a) (fun a=> -g a) := by
  unfold Carry; simp only [← neg_sub', abs_neg]; exact h

theorem sub (H : Carry k w f g) (h : Carry k w p q) : Carry k w (fun a=>f a-p a) (fun a=>g a-q a) := by
  simp_rw [sub_eq_add_neg]; exact H.add h.neg

theorem mul_bounded (H : Carry k w f g) (B : Bounded k p) : Carry k w (fun a=>f a*p a) (fun a=>g a*p a) := by
  obtain ⟨C,hc,h⟩:=H; obtain ⟨D,hd,H⟩:=B
  refine ⟨C*D,by positivity,?_⟩; filter_upwards [h,H,k.currency] with a he hq ho
  rw [← sub_mul, abs_mul]
  convert! mul_le_mul he hq (abs_nonneg _) (by positivity) using 1; ring

-- Key product: one factor of unknown size multiplies a *small* error.
-- A second unknown multiplying a first is NOT part of this API (when at
-- degree n>0, it cannot occur; construct at the coefficient level below).
theorem of_mul_uncertain (H : NearFn k f g) (B : Burden k w p) : Carry k w (fun a=>f a*p a) (fun a=>g a*p a) := by
  obtain ⟨C,hc,h⟩:=H; obtain ⟨D,hd,H⟩:=B; refine ⟨C*D,by positivity,?_⟩
  filter_upwards [h,H,k.currency] with a he hq ho
  rw [←sub_mul,abs_mul]; convert! mul_le_mul he hq (abs_nonneg _) (by positivity) using 1; ring

theorem mul_left (H : Carry k w f g) (hf : Burden k w g) (h : NearFn k p q) (hQ : Bounded k p) : Carry k w (fun a=> f a*p a) (fun a=>g a*q a):= by
   apply (H.mul_bounded hQ).trans
   simpa only [mul_comm] using of_mul_uncertain h hf

theorem mul_right (H : Carry k w p q) (hq : Burden k w q) (h : NearFn k f g) (hF : Bounded k f) : Carry k w (fun a=>f a*p a) (fun a=>g a*q a) := by simpa only [mul_comm] using H.mul_left hq h hF

theorem congr (H : Carry k w p q) (h : p =ᶠ[k.along] f) (hp : q =ᶠ[k.along] g) : Carry k w f g := by
  obtain ⟨C,hc,H⟩:=H; refine ⟨C,hc,?_⟩; filter_upwards [H,h,hp] with a ha ht hp
  rwa [←ht,←hp]

theorem boundedWeight (H : Carry k w f g) (B : Bounded k w) : NearFn k f g := by
  obtain ⟨C,hc,H⟩:=H; obtain ⟨D,hD,H'⟩:=B
  refine ⟨C*(1+D),by positivity,?_⟩; filter_upwards [H,H',k.currency] with a hv hb hk
  rw [mul_right_comm]; apply hv.trans; gcongr
end Carry

section total
variable {v u : I → α→ℝ} {s : Finset I}
theorem burden_sum (H : ∀ i∈s,Burden k w (v i)) : Burden k w (fun a=> ∑ i∈s,v i a):= by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Burden.of_bounded (Bounded.const _)
  | insert i s hi ih=>simp_rw [Finset.sum_insert hi]; exact (H _ (by simp)).add (ih fun j hj=> H _ (by simp [hj]))

theorem carry_sum (H : ∀ i∈s,Carry k w (v i) (u i)) : Carry k w (fun a=>∑ i∈s,v i a) (fun a=>∑ i∈s,u i a) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp_rw [Finset.sum_empty]; exact Carry.refl _
  | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (H _ (by simp)).add (ih fun j hj=>H _ (by simp [hj]))
variable [Fintype I] [DecidableEq I] (L : (I→ℝ)→ₗ[ℝ] ℝ)

theorem carry_linear (H : ∀ i,Carry k w (v i) (u i)) :
    Carry k w (fun a=>L (fun i=>v i a)) (fun a=>L (fun i=>u i a)) := by
  rw [show (fun a=>L (fun i=>v i a))=_ from funext fun a=>linear_eq (I:=I) L (fun i=>v i a),
    show (fun a=>L (fun i=>u i a))=_ from funext fun a=>linear_eq (I:=I) L (fun i=>u i a)]
  exact carry_sum fun i _=>(H i).mul_bounded (Bounded.const _)
end total

/-- At a detector transition: one residual factor with weight price the
l1 total of unknown *current* coefficients, not presumed bounded. Prove
boundedness and then actual rate. -/
theorem absorb [Fintype I] (y : α→I→ℝ) (u : I→ℝ)
    (h : ∀ i, Carry k (fun a=>∑ j,|y a j|) (fun a=>y a i) (fun _=>u i)) :
    (Bounded k (fun a=>∑ j,|y a j|)) ∧ ∀ i, Near k (fun a=> y a i) (u i) := by
  have hall:=h
  choose C hC hc using h
  let D:= ∑ i,C i
  have hd : 0 ≤ D := Finset.sum_nonneg fun i _=>hC i
  let M:= ∑ i,|u i|
  have hm : 0 ≤ M := Finset.sum_nonneg fun _ _=>abs_nonneg _
  let W (a:α):=∑ i,|y a i|
  have hs : ∀ᶠ a in k.along, D*k.E a < 1/2 := (show Tendsto (fun a=>D*k.E a) _ (𝓝 0) by simpa using (k.gone.const_mul D)).eventually (gt_mem_nhds (by norm_num))
  have HB:Bounded k W:= by
    refine ⟨1+2*M,by positivity,?_⟩
    filter_upwards [hs, Filter.eventually_all.mpr hc, k.currency] with a (hD:_<1/2) H hw
    have hv : 0 ≤ W a:= Finset.sum_nonneg fun _ _=>abs_nonneg _
    have hi : W a ≤ D*k.E a*(1+W a)+M := by
      change ∑ i, |y a i| ≤ _
      rw [show M=∑ i,|u i| from rfl] -- specify D
      unfold D; simp_rw [Finset.sum_mul,← Finset.sum_add_distrib]; refine Finset.sum_le_sum ?_
      intro i _; specialize H i; dsimp only at *; rw [abs_of_nonneg hv] at H
      calc |y a i|=|y a i-u i+u i|:=by rw [sub_add_cancel]
           _ ≤ |y a i-u i|+|u i|:=abs_add_le ..
           _ ≤ _:=by gcongr
    rw [abs_of_nonneg hv]; nlinarith [hi]
  exact ⟨HB, fun i=> Carry.boundedWeight (hall i) HB⟩
end YM.RG11.Rate
