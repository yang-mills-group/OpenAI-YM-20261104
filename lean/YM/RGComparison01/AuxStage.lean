import YM.RGComparison01.AuxGeo

/-! # A finite, rescaled perturbative test calculation in jet norms

Keep the names and actual coefficients, not just existence of a polynomial
approximation. On unnormalised Lie `x` use Brush budget `(period cost, s⁻¹)`,
not claiming an activity bound at this stage. Account coefficients at real
coupling in *physical* test scaling, including polynomial costs in that budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxStage
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxJets AuxCurtain PhysicalNext.Repeat WilsonStartup Tensor
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Co (E : Type) := ℕ → E → ℝ
-- h=gStep β, b=x/g
def headAt (c : Co E) (h : ℝ) (i : ℕ) (x : E) := h^i*c i (h⁻¹ • x)
def price (c : Co E) (h : ℝ) (k : ℕ) (x : E) := ∑ i∈ Finset.range (k+1), headAt c h i x
structure Points (v d h : ℝ) (k j : ℕ) (f:E→ℝ) (x:E) (c : Co E) : Prop where
  bill : ∀ i ≤ k, Brush j (v*h^i) d (headAt c h i) x
  tail : Brush j (v*h^(k+1)) d (f-price c h k) x
variable {f g : E→ℝ} {x : E} {v d h u p : ℝ} {k j n : ℕ} {F G : Co E}

namespace Points
section
variable (H : Points v d h k j f x F)
include H
lemma pos : 0 ≤ d := H.tail.pos
lemma nonneg : 0 ≤ v:= by simpa only [pow_zero,mul_one] using (H.bill 0 (Nat.zero_le _)).nonneg
lemma funding (hv : v ≤ u) (he : 0 ≤ h) (hd : d ≤ p) : Points u p h k j f x F:= ⟨fun i hi=> (H.bill i hi).climb (mul_le_mul_of_nonneg_right hv (pow_nonneg he _)) hd,H.tail.climb (mul_le_mul_of_nonneg_right hv (pow_nonneg he _)) hd⟩
lemma smaller (hi : n ≤ j) : Points v d h k n f x F:= ⟨fun i hh=> (H.bill i hh).smaller hi,H.tail.smaller hi⟩
lemma adjust (q : g =ᶠ[𝓝 x] f) : Points v d h k j g x F:= ⟨H.bill,H.tail.shimmy (q.sub EventuallyEq.rfl)⟩

def allowance (v : ℝ) (k : ℕ) := (k+1:ℕ)*v
lemma bulk (hh:0 ≤ h) (hv:h≤1) : Brush j (allowance v k) d (price F h k) x:= by
  have hB := Brush.spree (Finset.range (k+1)) (headAt F h) (fun _=> v) H.pos (fun i hi=> (H.bill _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).climb (mul_le_of_le_one_right H.nonneg (pow_le_one₀ hh hv)) le_rfl)
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hB; exact hB

lemma full (hh : 0 ≤ h) (hv : h ≤ 1) : Brush j (v+allowance v k) d f x:= ((H.tail.climb (mul_le_of_le_one_right H.nonneg (pow_le_one₀ hh hv)) le_rfl).gathering (H.bulk hh hv)).shimmy (Eventually.of_forall fun _=> (sub_add_cancel ..).symm)

lemma scale (a : ℝ) : Points (‖a‖*v) d h k j (fun i=> a*f i) x (a • F):= by
  have hh i (y:E): headAt (a • F) h i y=a*headAt F h i y:= mul_left_comm ..
  constructor
  · intro i hi
    rw [funext (hh i),mul_assoc]; exact ((H.bill i hi).smul a)
  have hz(y:E): price (a • F) h k y=a * price F h k y:= by simp_rw [price, hh,← Finset.mul_sum]
  rw [mul_assoc]; apply (H.tail.smul a).shimmy; refine Eventually.of_forall fun i=>?_; change _-_=a*(f _-_); rw [hz,mul_sub]

lemma quote (a : ℝ) {X : E→ℝ} (H' : Brush j (a*h^(k+1)) d (X - f) x) (ha : 0≤a) (hh : 0 ≤ h) : Points (a+v) d h k j X x F:= by
  refine ⟨fun i hi=> (H.bill i hi).climb (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) (pow_nonneg hh i)) le_rfl, ?_⟩
  rw [add_mul]; exact (H'.gathering H.tail).shimmy (Eventually.of_forall fun _=> (sub_add_sub_cancel ..).symm)
lemma off_one (hz : F 0=fun _=> p) (he : 0 ≤ h) (hh : h ≤ 1) : Brush j ((v+allowance v k)*h) d (fun i=> f i - p) x:= by
  let s:= Finset.range (k+1); have h₀:0∈s:=Finset.mem_range.mpr (Nat.zero_lt_succ k)
  let T (x:E):= ∑ i∈s.erase 0,headAt F h i x
  have ht (i:E): price F h k i= p+ T i:= by unfold price; rw [← Finset.add_sum_erase _ _ h₀]; rw [headAt,hz,pow_zero,one_mul]
  have hV : Brush j (allowance v k*h) d T x:= by
    have he' : Brush j (∑ i∈s.erase 0,v*h) d T x:= Brush.spree _ _ _ H.pos (fun i hi=>by
      obtain ⟨hy,hg⟩:= Finset.mem_erase.mp hi
      refine (H.bill i (Nat.le_of_lt_succ (Finset.mem_range.mp hg))).climb (mul_le_mul_of_nonneg_left ?_ H.nonneg) le_rfl
      exact (pow_le_pow_of_le_one he hh (by omega : 1 ≤ i)).trans_eq (pow_one _))
    refine he'.climb ?_ le_rfl; rw [Finset.sum_const,nsmul_eq_mul]; unfold allowance; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (Finset.card_range _)) (mul_nonneg H.nonneg he)
  rw [add_mul]
  refine (((H.tail.climb (mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one he hh (by omega : 1 ≤ k+1)).trans_eq (pow_one _)) H.nonneg) le_rfl)).gathering hV).shimmy ?_
  refine Eventually.of_forall fun i=>?_ ; change _= _-price F h k _ + _; rw [ht]; ring
lemma add (H' : Points u d h k j g x G) : Points (v+u) d h k j (f+g) x (F+G):= by
  have he i y : headAt (F+G) h i y=headAt F h i y+headAt G h i y:= mul_add ..
  constructor
  · intro i hi; rw [add_mul, funext (he i)]; exact (H.bill i hi).gathering (H'.bill i hi)
  rw [add_mul]; apply (H.tail.gathering H'.tail).shimmy; refine Eventually.of_forall fun i=>?_; simp only [Pi.add_apply, Pi.sub_apply, price, he,Finset.sum_add_distrib]; ring
end

def scalar (t:ℝ) : Co E := fun i _=> if i=0 then t else 0
lemma start (t:ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h) : Points ‖t‖ d h k j (fun _=>t) x (scalar t):= by
  have hz : 0∈Finset.range (k+1):= Finset.mem_range.mpr k.zero_lt_succ
  have ht (y:E) : price (scalar t) h k y=t:= by
    unfold price; rw [Finset.sum_eq_single_of_mem 0 hz _]; simp [headAt,scalar]; intro i _ hi; simp [headAt,scalar,hi]
  constructor
  · rintro i hi
    by_cases H:i=0
    · subst i; unfold headAt; simp only [scalar,pow_zero,mul_one,one_mul,↓reduceIte]; exact Brush.certified hd _
    unfold headAt; simp_rw [scalar,if_neg H,mul_zero]; exact AuxCurtain.constant hd (by rw [norm_zero]; positivity)
  rw [funext ht,sub_self]; exact AuxCurtain.constant (u:=(0:ℝ)) hd (by rw [norm_zero]; positivity)
lemma constant_zero (hd : 0 ≤ d) (hh : 0 ≤ h): Points 0 d h k j (0:E→ℝ) x (0:Co E):= by
  have he:= start (x:=x) (k:=k) (j:=j) 0 hd hh
  rw [show scalar (E:=E) 0 = 0 from funext fun i=> funext fun y=> by simp [scalar],norm_zero] at he; exact he
lemma summing {α : Type} (W : α → ℝ) (A : α → Co E) (c : α → E→ℝ) (s : Finset α) (hd : 0 ≤ d) (hh : 0 ≤ h) (ht : ∀ i∈s, Points (W i) d h k j (c i) x (A i)) : Points (∑ i∈s,W i) d h k j (∑ i∈s,c i) x (∑ i∈s,A i):= by
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty]; exact constant_zero hd hh
  | insert i s hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact (ht i (Finset.mem_insert_self ..)).add (ih fun i hi=> ht i (Finset.mem_insert_of_mem hi))

-- retain actual product from a source (Γ-profile conditional value); no germ choices.
def weave (F G : Co E) : Co E:=fun i x=>∑ k∈Finset.range (i+1), F k x*G (i-k) x

def cores (k j : ℕ) (u v : ℝ):= ((k+1:ℕ):ℝ)*(u*v*2^j)
def fuse (k j : ℕ) (u v : ℝ):=cores k j u v + ((k+1:ℕ)^2:ℕ)*(u*v*2^j) +
    u*(v+allowance v k)*2^j+allowance u k*v*2^j

lemma bill_joint (H : Points v d h k j f x F) (H' : Points u d h k j g x G) (hh : 0 ≤ h) : ∀ i ≤ k, Brush j (cores k j v u*h^i) d (headAt (weave F G) h i) x:= by
  intro i hi
  let s:=Finset.range (i+1); let f l:=headAt F h l; let g l:= headAt G h (i-l)
  have he : headAt (weave F G) h i=(fun y=>∑ l∈s,f l y*g l y):= by
    ext1 y; unfold headAt weave; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l hl=>?_)
    dsimp only [f,g,headAt]; have hL:= Finset.mem_range.mp hl; nth_rw 1 [show i=l+(i-l) from Eq.symm (Nat.add_sub_of_le (by omega : l ≤ i))]; rw [pow_add]; ring_nf
  let p:=v*u*2^j*h^i
  have ht (l:ℕ) (hl:l∈s) : Brush j p d (fun x=> f l x*g l x) x := by
    have hx := Finset.mem_range.mp hl
    have hg:= together (H.bill l (by omega)) (H'.bill (i-l) (by omega)); refine hg.climb (le_of_eq ?_) le_rfl
    unfold p; nth_rw 2 [show i=l+(i-l) from Eq.symm (Nat.add_sub_of_le (by omega : l ≤ i))]; rw [pow_add]; ring_nf
  rw [he]; refine (Brush.spree s _ _ H.pos ht).climb ?_ le_rfl
  rw [Finset.sum_const,nsmul_eq_mul]; unfold s p; rw [Finset.card_range]; unfold cores; rw [mul_assoc (↑(k+1 : ℕ) : ℝ)]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hi) (by have h:=H.nonneg; have h':=H'.nonneg; positivity)
end Points
end YM.RGComparison01.AuxStage
