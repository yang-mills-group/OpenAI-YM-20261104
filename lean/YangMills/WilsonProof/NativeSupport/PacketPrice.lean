import YangMills.WilsonProof.NativeSupport.CalibratedTerminal
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Reading one whole, possibly nonlocal word per translate from the actual
square-zero marker polynomial. All lower moments within a translate survive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Finset Marker Extra.Trajectories
open scoped Classical BigOperators
variable {V H : Type*} [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H]

abbrev tag (S : Finset V) : (Stock.census V).Mode := ⟨S, mem_univ _⟩

def liftSet (g : V → H) (J : Finset H) := univ.filter fun v => g v ∈ J
def fibre (g : V → H) (h : H) := univ.filter fun v => g v = h

def read (g : V → H) (s : ℂ) (P : Poly (Stock.census V)) :=
  ∑ J ∈ (univ : Finset H).powerset, s^J.card * P.part (tag (liftSet g J))

lemma shift_part (P : Poly (Stock.census V)) (A S : Finset V) (p : ℂ) :
    (P*Poly.send (tag A) p).part (tag S) = if A⊆S then P.part (tag (S\A))*p else 0 := by
  rw [Poly.part_mul]
  let f (i j : (Stock.census V).Mode) := if Poly.merges i j (tag S) then P.part i*(Poly.send (tag A) p).part j else 0
  have he (i : (Stock.census V).Mode) : ∑ j, f i j=f i (tag A) := by
    rw [sum_eq_single (tag A)]
    · intro j _ hj; unfold f; simp only [Poly.part_send,if_neg hj]; split <;> simp
    · simp
  have hc (i : (Stock.census V).Mode) : f i (tag A) = if A⊆S then (if i = tag (S\A) then P.part i*p else 0) else 0 := by
    have hm : Poly.merges i (tag A) (tag S) ↔ A⊆S ∧ i=tag (S\A) := by
      change Disjoint i.val A ∧ i.val∪A=S ↔ _
      constructor
      · rintro ⟨di,rfl⟩
        refine ⟨subset_union_right, Subtype.ext ?_⟩
        ext v
        change v∈i.val ↔ v∈(i.val∪A)\A
        simp only [mem_sdiff,mem_union]
        constructor
        · intro hv; exact ⟨Or.inl hv, disjoint_left.mp di hv⟩
        · tauto
      · rintro ⟨sub,rfl⟩; exact ⟨sdiff_disjoint,sdiff_union_of_subset sub⟩
    simp [f,hm,ite_and]
  change (∑ i, ∑ j, f i j)=_
  simp_rw [he,hc]; split <;> simp

private lemma read_add (g : V → H) (s : ℂ) (P Q : Poly (Stock.census V)) :
    read g s (P+Q)=read g s P+read g s Q := by
  simp only [read,Poly.part_plus,mul_add,sum_add_distrib]

private lemma read_send (g : V → H) (s : ℂ) (P : Poly (Stock.census V)) (T : Finset V) (c : ℂ) :
    read g s (P*Poly.send (tag T) c) = c*read g s (P*Poly.send (tag T) 1) := by
  simp only [read,Finset.mul_sum,shift_part,mul_one]
  apply sum_congr rfl; intro J _; split <;> ring

private lemma shifted_cost (g : V → H) (s : ℂ) (P : Poly (Stock.census V)) (A D : Finset V) (c : ℂ) {B : ℝ}
    (h : ∀ T : Finset V, ‖read g s (P*Poly.send (tag T) 1)‖ ≤ B) :
    ‖read g s ((P*(1+Poly.send (tag D) c))*Poly.send (tag A) 1)‖ ≤ (1+‖c‖)*B := by
  rw [mul_add,mul_one,add_mul,read_add,mul_assoc]
  have tail : ‖read g s (P*(Poly.send (tag D) c * Poly.send (tag A) 1))‖ ≤ ‖c‖*B := by
    by_cases hd : Disjoint D A
    · rw [tagged_mul _ _ (tag (D∪A)) ⟨hd,rfl⟩,mul_one,read_send,norm_mul]
      exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
    · have e : Poly.send (tag D) c * Poly.send (tag A) 1 = 0 := by
        by_contra nh; obtain ⟨z,di,_⟩ := merges_of_tagged_mul nh; exact hd di
      rw [e,mul_zero]; simp only [read,Poly.part_nil,mul_zero,sum_const_zero,norm_zero]
      exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (h ∅))
  exact (norm_add_le ..).trans ((add_le_add (h _) tail).trans_eq (by ring))

/-- A collection of cross-word log monomials costs its sum of absolute
coefficients, independently of the number of translations. -/
theorem cross_price {ι : Type*} (g : V → H) (s : ℂ) (P : Poly (Stock.census V))
    (I : Finset ι) (D : ι → Finset V) (c : ι → ℂ) {B : ℝ}
    (h : ∀ T : Finset V, ‖read g s (P*Poly.send (tag T) 1)‖ ≤ B) :
    ‖read g s (P * ∏ i ∈ I, (1+Poly.send (tag (D i)) (c i)))‖ ≤ Real.exp (∑ i ∈ I, ‖c i‖)*B := by
  classical
  have go (U : Finset ι) (A : Finset V) :
      ‖read g s ((P * ∏ i ∈ U, (1+Poly.send (tag (D i)) (c i)))*Poly.send (tag A) 1)‖
        ≤ (∏ i∈U, (1+‖c i‖))*B := by
    induction U using Finset.induction_on generalizing A with
    | empty => simpa using h A
    | insert i U hi ih =>
      rw [prod_insert hi, prod_insert hi]
      rw [show P*((1+Poly.send (tag (D i)) (c i))*∏ j∈U,(1+Poly.send (tag (D j)) (c j)))=
        (P*∏ j∈U,(1+Poly.send (tag (D j)) (c j)))*(1+Poly.send (tag (D i)) (c i)) by ring]
      exact (shifted_cost g s _ A _ _ ih).trans_eq (by ring)
  have hh := go I ∅
  change ‖read g s ((P*∏ i∈I,_)*1)‖ ≤ _ at hh
  rw [mul_one] at hh
  refine hh.trans (mul_le_mul_of_nonneg_right ?_ ((norm_nonneg _).trans (h ∅)))
  rw [Real.exp_sum]
  exact prod_le_prod (by intro i _; positivity) (fun i _ => by simpa [add_comm] using Real.add_one_le_exp ‖c i‖)

omit [Fintype H] in
private lemma fibre_diff (g : V → H) (J : Finset H) (A : Finset V) (h : H) :
    (liftSet g J\A)∩fibre g h = if h∈J then fibre g h\A else ∅ := by
  ext v
  by_cases e : g v = h <;> by_cases y : h ∈ J <;> simp [liftSet,fibre,e,y,and_comm]

/-- A monomial that has already used a marker of a word can get its
remaining markers only from that same word's submoment. -/
theorem read_product (g : V → H) (s : ℂ) (P : Poly (Stock.census V))
    (M : H → Finset V → ℂ) (quiet : ∀ h, M h ∅=1)
    (part : ∀ U, P.part (tag U) = ∏ h, M h (U∩fibre g h)) (A : Finset V) :
    read g s (P*Poly.send (tag A) 1) =
      ∏ h, ((if h∈A.image g then 0 else 1) + s*M h (fibre g h\A)) := by
  let X (h : H) : ℂ := if h∈A.image g then 0 else 1
  let Y (h : H) : ℂ := s*M h (fibre g h\A)
  change _ = ∏ h, (X h+Y h)
  simp_rw [add_comm (X _) (Y _)]
  rw [prod_add]
  unfold read
  apply sum_congr rfl
  intro J _
  rw [shift_part]
  by_cases ha : A ⊆ liftSet g J
  · rw [if_pos ha,mul_one,part]
    have lift (h : H) (hy : h∉J) : h∉A.image g := by
      rintro hh; obtain ⟨v,hv,rfl⟩ := mem_image.mp hh
      exact hy ((mem_filter.mp (ha hv)).2)
    have x : ∏ h∈univ\J,X h=1 := prod_eq_one fun h hh =>
      if_neg (lift _ (mem_sdiff.mp hh).2)
    rw [x,mul_one]
    have kept : (∏ h, M h ((liftSet g J\A)∩fibre g h)) = ∏ h∈J,M h (fibre g h\A) := by
      rw [← prod_sdiff (f := fun h => M h ((liftSet g J\A)∩fibre g h)) (subset_univ J)]
      have z : ∏ h∈univ\J,M h ((liftSet g J\A)∩fibre g h)=1 := prod_eq_one fun h hh => by
        rw [fibre_diff,if_neg (mem_sdiff.mp hh).2,quiet]
      rw [z,one_mul]; apply prod_congr rfl; intro h hh; rw [fibre_diff,if_pos hh]
    rw [kept]; simp [Y,prod_mul_distrib]
  · rw [if_neg ha,mul_zero]
    obtain ⟨v,hv,hj⟩ := Finset.not_subset.mp ha
    have j : g v∉J := by simpa [liftSet] using hj
    have zero : ∏ h∈univ\J, X h = 0 := prod_eq_zero (mem_sdiff.mpr ⟨mem_univ _,j⟩)
      (show X (g v)=0 from if_pos (mem_image_of_mem _ hv))
    rw [zero,mul_zero]

/-- All submoments may be dependent and complex. Only the whole-word expectation
is translation invariant and real at this stage. -/
theorem word_price (g : V → H) (s : ℝ) (P : Poly (Stock.census V))
    (M : H → Finset V → ℂ) (quiet : ∀ h, M h ∅=1)
    (part : ∀ U, P.part (tag U) = ∏ h, M h (U∩fibre g h))
    (mom : ∀ h T, ‖M h T‖ ≤ 1) {w : ℝ} (full : ∀ h, M h (fibre g h) = (w : ℂ))
    (hw : |w| ≤ 1) (hs : |s| ≤ 1/4) (A : Finset V) :
    ‖read g s (P*Poly.send (tag A) 1)‖ ≤ (1+s*w)^Fintype.card H := by
  rw [read_product g _ P M quiet part A,norm_prod]
  have sw : |s*w| ≤ 1/4 := by
    rw [abs_mul]; exact (mul_le_mul hs hw (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
  have floor : 3/4 ≤ 1+s*w := by linarith [neg_abs_le (s*w)]
  rw [← card_univ (α := H), ← prod_const (s := (univ : Finset H))]
  apply prod_le_prod (fun h _ => norm_nonneg _)
  intro h _
  by_cases hh : h∈A.image g
  · rw [if_pos hh,zero_add,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (mom ..) (abs_nonneg _)).trans (by linarith)
  · have eq : fibre g h\A=fibre g h := sdiff_eq_self_iff_disjoint.mpr (disjoint_left.mpr (by
      intro v he ha; apply hh; have := (mem_filter.mp he).2; rw [← this]; exact mem_image_of_mem _ ha))
    rw [if_neg hh,eq,full,← Complex.ofReal_mul,← Complex.ofReal_one,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (by linarith)]


end YM.Integration.InletSusceptibility.Packet
