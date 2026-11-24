import YM.Pert.Flow.Barriers
/-! Linear substitutions for polynomial prices. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.Pert.Flow.Price
open Function Filter Topology
open scoped Topology Classical
variable {F : Type*} {f g : ℕ → ℝ}

lemma tamer (hf : tame f) (hg : ∀ i, |g i| ≤ |f i|) : tame g := by
   obtain ⟨q,C,hC,h⟩:=hf
   exact ⟨q,C,hC,fun i=>(hg i).trans (h i)⟩
lemma flatter (hf : flat f) (hg : ∀ i, |g i| ≤ |f i|) : flat g := fun q=>by
   obtain ⟨C,hC,h⟩:=hf q
   exact ⟨C,hC,fun i=>(hg i).trans (h i)⟩

lemma mild_constant (C : ℝ) : tame (fun _=>C) := ⟨0,|C|,abs_nonneg _,fun _=>by simp⟩
lemma tame_add (hf : tame f) (hg : tame g) : tame (fun i=>f i+g i) := by
   obtain ⟨q,C,hC,h⟩:=hf
   obtain ⟨p,B,hB,b⟩:=hg
   refine ⟨max q p,C+B,by positivity,fun i=>?_⟩
   dsimp only
   have hr := duration_large i
   refine (abs_add_le ..).trans ((add_le_add (h i) (b i)).trans ((add_mul C B _).symm ▸ ?_))
   gcongr <;> first | exact le_max_left .. | exact le_max_right ..

lemma tame_times (hf : tame f) (hg : tame g) : tame (fun i=> f i * g i) := by
   obtain ⟨q,C,hC,h⟩:=hf
   obtain ⟨p,B,hB,b⟩:=hg
   refine ⟨q+p,C*B,by positivity,fun i=> ?_⟩
   rw [abs_mul,pow_add]
   exact (mul_le_mul (h i) (b i) (abs_nonneg _) ((abs_nonneg _).trans (h i))).trans_eq (by ring)

lemma tame_flat (hf : tame f) (hg : flat g) : flat (fun i=>f i*g i) := by
   intro q
   obtain ⟨p,B,hB,b⟩:=hf
   obtain ⟨C,hC,h⟩:=hg (q+p)
   refine ⟨B*C,by positivity,fun i=> ?_⟩
   rw [abs_mul]
   have hh :=duration_large i
   exact (mul_le_mul (b i) (h i) (abs_nonneg _) ((abs_nonneg _).trans (b i))).trans_eq (by rw [pow_add];field_simp)

lemma flat_plus (hf : flat f) (hg : flat g) : flat (fun i=>f i+g i) := fun q=>by
   obtain ⟨C,hC,h⟩:=hf q; obtain ⟨B,hB,b⟩:=hg q
   exact ⟨C+B,by positivity,fun i=> (abs_add_le ..).trans ((add_le_add (h i) (b i)).trans_eq (add_div ..).symm)⟩
lemma flat_tame (hf:flat f) : tame f := by
   obtain ⟨C,hC,h⟩:=hf 0; exact ⟨0,C,hC,fun i=> by simpa using h i⟩

lemma sum_tame {s : Finset F} {a:F→ℕ→ℝ} (ha : ∀ i∈s,tame (a i)) : tame (fun t=>∑i∈s,a i t) := by
   induction s using Finset.induction_on with
   | empty=>simpa only [Finset.sum_empty] using mild_constant 0
   | insert i s h ih =>
       exact (tame_add (ha i (Finset.mem_insert_self ..)) (ih fun j h=>ha j (Finset.mem_insert_of_mem h))) |> fun he=> (by simpa only [Finset.sum_insert h] using he)

lemma sum_flat {s : Finset F} {a:F→ℕ→ℝ} (ha : ∀ i∈s,flat (a i)) : flat (fun t=>∑i∈s,a i t) := by
   induction s using Finset.induction_on with
   | empty=> exact fun _=>⟨0,le_rfl,fun _=>by simp⟩
   | insert i s h ih =>
       exact (flat_plus (ha i (Finset.mem_insert_self ..)) (ih fun j h=>ha j (Finset.mem_insert_of_mem h))) |> fun he=> (by simpa only [Finset.sum_insert h] using he)

lemma product_tame {s : Finset F} {a:F→ℕ→ℝ} (ha : ∀ i∈s,tame (a i)) : tame (fun t=>∏ i∈s,a i t) := by
   induction s using Finset.induction_on with
   | empty=>simpa only [Finset.prod_empty] using mild_constant 1
   | insert i s h ih =>
       exact (tame_times (ha i (Finset.mem_insert_self ..)) (ih fun j h=>ha j (Finset.mem_insert_of_mem h))) |> fun he=> (by simpa only [Finset.prod_insert h] using he)

lemma duration_mild (p : ℕ) : tame (fun i=>(duration i)^p) :=
   ⟨p,1,zero_le_one,fun i=> by rw [one_mul]; exact le_of_eq (abs_of_nonneg (pow_nonneg (zero_le_one.trans (duration_large _)) _))⟩
lemma polynomial_pays {q : ℕ} (hf : tame f) (ht : ∀ i, |f i| ≤ (duration i)^q * |g i|) (hg : flat g) : flat f :=
   flatter (tame_flat (duration_mild q) hg) (fun i=>by
     have hi := duration_large i
     rw [abs_mul]; rw [abs_of_nonneg (show 0≤(duration i)^q by positivity)]
     exact ht i)
end YM.Pert.Flow.Price
