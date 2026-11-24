import YM.FormalBulk08.Flat.LevelD

/-!
For price estimates on real punctured momentum retain BOTH inputs, a fixed
power inverse momentum loss, and the rate target (usually M⁻¹ᐟ²). The loss
will only be used *locally* to obtain honest history rates with **fixed**
strip; no iteration of inverse weights is intended. Exponents explicit,
independent of family, L, J and depths. The generic index may include the
prescribed hierarchy itself, so none of the depth/shape uniformity is lost
before later schedule choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators
variable {ι α β γ : Type*}

def Paired (w r : ι → ℝ) (t : ℕ) (F H : ι → ℂ) : Prop :=
    ∃ C : ℝ, 0<C ∧ ∀ i, let D:= C*w i^t
      ‖F i‖≤D ∧ ‖H i‖≤D ∧ ‖F i-H i‖≤D*r i

variable {w r : ι → ℝ}
namespace Paired
variable {F G H I : ι → ℂ} {t s n : ℕ}
lemma extra (h : Paired w r t F G) (hw : ∀ i,1≤w i) (hr : ∀ i,0 ≤ r i) (ht : t ≤ s) :
    Paired w r s F G := by
  obtain ⟨C,hC,h⟩:=h
  refine ⟨C,hC,fun i =>?_⟩
  have ht := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hw i) ht) hC.le
  exact ⟨(h i).1.trans ht,(h i).2.1.trans ht,(h i).2.2.trans (mul_le_mul_of_nonneg_right ht (hr i))⟩
lemma adjusts (h : Paired w r t F G) {v : ι → ℝ} (hw : ∀ i,1≤w i) (hr : ∀ i, r i ≤ v i) :
    Paired w v t F G := by
  obtain ⟨C,hC,h⟩:=h
  exact ⟨C,hC,fun i=> ⟨(h i).1,(h i).2.1,(h i).2.2.trans (mul_le_mul_of_nonneg_left (hr i) (mul_nonneg hC.le (pow_nonneg (le_trans zero_le_one (hw i)) _)))⟩⟩
lemma plugs (h : Paired w r t F G) (he : ∀ i, F i = H i) (hg : ∀ i, G i=I i) : Paired w r t H I := funext he ▸ funext hg ▸ h
lemma equal (hr : ∀ i,0≤r i) (h : ∃ C, ∀ i, ‖F i‖≤C) : Paired w r 0 F F := by
  obtain ⟨C,h⟩:=h
  refine ⟨max 1 C,lt_max_of_lt_left one_pos,fun i => ?_⟩
  simp only [pow_zero,mul_one,sub_self,norm_zero]
  have he := (h i).trans (le_max_right 1 C)
  exact ⟨he,he,mul_nonneg ((norm_nonneg _).trans he) (hr i)⟩
lemma const (x : ℂ) (hr : ∀ i,0≤r i) : Paired w r 0 (fun _=> x) (fun _=>x) := equal hr ⟨‖x‖,fun _=>le_rfl⟩
lemma neg (h : Paired w r t F G) : Paired w r t (fun i=> -F i) fun i=> -G i := by
  obtain ⟨C,hC,h⟩:=h; refine ⟨C,hC,fun i=>?_⟩
  have hv : -F i- -G i= -(F i-G i):= by abel
  simpa only [hv,norm_neg] using h i
lemma add (h : Paired w r t F G) (g : Paired w r t H I) : Paired w r t (fun i=>F i+H i) fun i=> G i+I i := by
  obtain ⟨C,hC,h⟩:=h; obtain ⟨K,hK,g⟩:=g
  refine ⟨C+K,by positivity,fun i=>?_⟩
  obtain ⟨hh,hg,h⟩:=h i; obtain ⟨ht,he,g⟩:=g i
  dsimp only
  rw [add_sub_add_comm,add_mul,add_mul]
  exact ⟨(norm_add_le ..).trans (add_le_add hh ht),(norm_add_le ..).trans (add_le_add hg he),(norm_add_le ..).trans (add_le_add h g)⟩
lemma sub (h : Paired w r t F G) (g : Paired w r t H I) : Paired w r t (fun i=>F i-H i) fun i=>G i-I i := by
  simpa only [sub_eq_add_neg] using h.add g.neg
lemma mul (h : Paired w r t F G) (g : Paired w r s H I) : Paired w r (t+s) (fun i=>F i*H i) fun i=> G i*I i := by
  obtain ⟨C,hC,h⟩:=h; obtain ⟨K,hK,g⟩:=g
  refine ⟨2*(C*K),by positivity,fun i=>?_⟩
  obtain ⟨hh,hg,h⟩:=h i; obtain ⟨ht,he,g⟩:=g i
  dsimp only
  rw [norm_mul,norm_mul,pow_add]
  have hT := (norm_nonneg _).trans hh
  have hS := mul_nonneg hT ((norm_nonneg _).trans ht)
  have hu : C*w i^t*(K*w i^s) ≤ 2*(C*K)*(w i^t*w i^s) := by linarith
  exact ⟨(mul_le_mul hh ht (norm_nonneg _) hT).trans hu,(mul_le_mul hg he (norm_nonneg _) hT).trans hu, (product_move _ _ _ _ h g hh he).trans_eq (by ring)⟩
lemma recip (h : Paired w r t F G) (hw : ∀ i,1 ≤ w i) (hr : ∀ i,0 ≤ r i)
    (hx : ∃ c : ℝ,0<c ∧ ∀ i,c/(w i^s)≤‖F i‖ ∧ c/(w i^s)≤‖G i‖) :
    Paired w r (t+s+s) (fun i=> (F i)⁻¹) fun i=> (G i)⁻¹ := by
  obtain ⟨c,hc,hx⟩:=hx; obtain ⟨C,hC,h⟩:=h
  let M:=max c⁻¹ (C/(c*c)); have hM : 0<M:=lt_max_of_lt_left (inv_pos.mpr hc)
  refine ⟨M,hM,fun i=>?_⟩
  have hv := one_pos.trans_le (hw i)
  have hg : 0<c/w i^s := by positivity
  have ht (x : ℂ) (ha : c/w i^s ≤ ‖x‖) : ‖x⁻¹‖ ≤ M*w i^(t+s+s) := by
    rw [norm_inv]
    calc
      _ ≤ (c/w i^s)⁻¹ := (inv_le_inv₀ (hg.trans_le ha) hg).2 ha
      _ = c⁻¹*w i^s := by rw [inv_div,div_eq_mul_inv,mul_comm]
      _ ≤ _ := mul_le_mul (le_max_left ..) (pow_le_pow_right₀ (hw i) (by omega)) (by positivity) hM.le
  refine ⟨ht _ (hx i).1,ht _ (hx i).2,(inv_move hg hg (hx i).1 (hx i).2 (h i).2.2).trans ?_⟩
  calc
    _ = C/(c*c)*w i^(t+s+s)*r i := by rw [pow_add,pow_add]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_pos hv _).le) (hr i)
lemma sum (s : Finset α) (hw : ∀ i,1≤w i) (hr : ∀ i,0≤r i) (F G : α → ι → ℂ) (h : ∀ a∈s, Paired w r t (F a) (G a)) :
    Paired w r t (fun i=> ∑ a∈s,F a i) fun i=>∑ a∈s,G a i := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using ((const 0 hr).extra hw hr (Nat.zero_le t))
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a (Finset.mem_insert_self ..)).add (ih fun _ hb=>h _ (Finset.mem_insert_of_mem hb))
lemma prod (s : Finset α) (hr : ∀ i, 0≤r i) (F G : α → ι → ℂ) (h : ∀ a∈s, Paired w r t (F a) (G a)) :
    Paired w r (t*s.card) (fun i=>∏ a∈s,F a i) fun i=>∏ a∈s, G a i := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.card_empty,Nat.mul_zero,Finset.prod_empty] using (const (w:=w) 1 hr)
  | insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha,Nat.mul_add,Nat.mul_one,Nat.add_comm]
    simpa only [Finset.prod_insert ha] using (h a (Finset.mem_insert_self ..)).mul (ih fun _ hb=> h _ (Finset.mem_insert_of_mem hb))
end Paired

def Boards (w r : ι→ℝ) (n : ℕ) (A B : ι→Matrix α β ℂ) := ∀ i j, Paired w r n (fun x=> A x i j) fun x=> B x i j

namespace Boards
variable {t s n : ℕ} {A B C D : ι → Matrix α β ℂ} {F H : ι → Matrix β γ ℂ}
lemma plugs (h : Boards w r t A B) (he : ∀ i, A i = C i) (hg : ∀ i, B i=D i) : Boards w r t C D := funext he ▸ funext hg ▸ h
lemma extra (h : Boards w r t A B) (hw : ∀ i,1≤w i) (hr : ∀ i,0 ≤ r i) (ht : t ≤ s) : Boards w r s A B := fun i j=> (h i j).extra hw hr ht
lemma add (h : Boards w r t A B) (g : Boards w r t C D) : Boards w r t (fun i=>A i+C i) fun i=>B i+D i := fun i j=> (h i j).add (g i j)
lemma sub (h : Boards w r t A B) (g : Boards w r t C D) : Boards w r t (fun i=>A i-C i) fun i=>B i-D i := fun i j=> (h i j).sub (g i j)
lemma sm {x y : ι→ℂ} (h : Paired w r s x y) (g : Boards w r t A B) :
    Boards w r (s+t) (fun i=> x i • A i) fun i=> y i • B i := fun i j=> h.mul (g i j)
lemma times [Fintype β] (hw : ∀ i,1≤w i) (hr : ∀ i,0≤r i) (h : Boards w r t A B) (g : Boards w r s F H) :
    Boards w r (t+s) (fun i=> A i*F i) fun i=> B i*H i := fun i j=> Paired.sum Finset.univ hw hr
      (fun k l=> A l i k*F l k j) (fun k l=> B l i k*H l k j) fun k _=> (h i k).mul (g k j)
lemma sum (k : Finset γ) (hw : ∀ i,1 ≤ w i) (hr : ∀ i,0 ≤ r i) (F G : γ→ι→ Matrix α β ℂ)
    (h : ∀ x∈k, Boards w r t (F x) (G x)) : Boards w r t (fun i=>∑ j∈k,F j i) fun i=>∑ j∈k,G j i := by
  intro i j
  simp only [Matrix.sum_apply]
  exact Paired.sum k hw hr (fun k l=>F k l i j) (fun k l=>G k l i j) fun x hx=>h x hx i j
lemma mask_paired (a b : ι → Axis → ℂ) (hw : ∀ i,1≤w i) (hr : ∀ i,0≤r i) (h : ∀ i : Axis, Paired w r t (fun j=> a j i) fun j=>b j i) :
    Boards w r (t*n) (fun i=>mask n (a i)) fun i=> mask n (b i) := by
  intro i j
  unfold mask
  by_cases hh : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    simpa only [i.property,inventory] using Paired.prod i.val hr (fun k j=>a j k) (fun k j=>b j k) fun i _=>h i
  simpa only [Matrix.diagonal_apply_ne _ hh] using ((Paired.const 0 hr).extra hw hr (Nat.zero_le (t*n)))
lemma fixed (hr : ∀ i,0 ≤ r i) (F : Matrix α β ℂ) : Boards w r 0 (fun _=>F) fun _=>F := fun i j=> Paired.const (F i j) hr
end Boards
end YM.FormalBulk08.Flat
