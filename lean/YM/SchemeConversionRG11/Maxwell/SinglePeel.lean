import YM.SchemeConversionRG11.Maxwell.Arms

/-! # Extract along one actual mobile square vertex.

Spectators are at arbitrary real separated positions. The same triggered
moment may involve a nonlocal combo of (color-charged) entries. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped BigOperators ComplexOrder

variable {n k l : ℕ} {G : Gauge} {ι : Type*} [Fintype ι]

def boundSet (n : ℕ) (W : Fin n → ℕ) := armset n W ×ˢ armset n W

lemma families_split (C₀ : G.ColorIndex) (x : Points n) (p : ι → ℂ) (W : ι → Fin n→WickPol G) (N : Fin n → ℕ) (r : Flavor 0)
    (hx : x ∈ conf _) (hw : ∀ i v,W i v ∈ shelf G (N v)) (H : ∀ b:E4, Points.cons b x∈ conf _ → ∑ i:ι,p i*bookend x b (W i) (team G r r)=0) :
    ∃ f : Arms n → Script, (∀ b : Space, ∀ u, aeval b (f u)=payable x p W u.1.1 u.2.1 (shoot C₀ u.1.2 (b-poles x u.1.1) r) (shoot C₀ u.2.2 (b-poles x u.2.1) r)) ∧
      ∀ b:E4,(∀ i,b ≠ x i) → ∑ i∈boundSet n N, aeval (paint b) (f i)/aeval (paint b) (DD (poles x) (charges i)) = 0 := by
  classical
  choose f hf hh using fun u : Arms n ↦ pairFamily C₀ u x p W r
  refine ⟨f,fun b i ↦ hf i b,fun b hb ↦ ?_⟩
  have hy : Points.cons b x∈conf _ := by
    intro i j; refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact Fin.cases (fun _ ↦ rfl) (fun j h ↦ (hb j h).elim) j
    exact Fin.cases (fun h ↦ (hb i h.symm).elim) (fun j h ↦ congr_arg Fin.succ (hx h)) j
  have h := H b hy
  unfold team bit at h; simp_rw [map_sum,bival _ x b hy hx _ N (hw _),Finset.mul_sum] at h
  simp_rw [boundSet, hh _ b hb]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  exact h

variable {x : Fin n → Space} {u : Arms n} {a y : Fin n} {N : Fin n → ℕ}

lemma arm_reflected (h : u∈ boundSet n N) : u.swap∈ boundSet n N := by
  rw [boundSet,Finset.mem_product] at h ⊢; exact ⟨h.2,h.1⟩
lemma arm_switch : charges u=charges u.swap := add_comm ..
lemma through_middle (h : y≠a) (hv : u∈ boundSet n N) (hp : N y=0) (hK : k+3 ≤ charges u a) (hT : 3≤charges u y) :
    ∃ l ≥ k, u=((a,l),(y,0)) ∨ u=((y,0),(a,l)) := by
  obtain ⟨⟨i,l⟩,j,m⟩ := u
  have hv₁ : l ≤ N i := arm_in.mp (Finset.mem_product.mp hv).1; have hv₂ : m ≤ N j := arm_in.mp (Finset.mem_product.mp hv).2
  unfold charges chargeArm at hT hK; simp only [Pi.add_apply] at hT hK
  by_cases he : i=a
  · subst i; by_cases hh : j=y
    · subst j; rw [hp] at hv₂; obtain rfl : m=0 := Nat.eq_zero_of_le_zero hv₂; simp only [if_neg h.symm,if_true] at hK; exact ⟨l,by omega,Or.inl rfl⟩
    simp only [if_neg h, if_neg (Ne.symm hh)] at hT; omega
  by_cases hh : j=a
  · subst j; by_cases hJ : i=y
    · subst i; rw [hp] at hv₁; obtain rfl : l=0 := Nat.eq_zero_of_le_zero hv₁
      simp only [if_neg h.symm,if_true] at hK; exact ⟨m,by omega,Or.inr rfl⟩
    simp only [if_neg (Ne.symm hJ),if_neg h] at hT; omega
  simp only [if_neg (Ne.symm he),if_neg (Ne.symm hh)] at hK; omega

def tip (a y : Fin n) (k : ℕ) : Arms n := ((a,k),(y,0))
lemma tip_a (h : a≠y) : charges (tip a y k) a=k+3 := by simp [charges,chargeArm,h,tip]
lemma tip_y (h : a≠y) : charges (tip a y k) y=3 := by simp [charges,chargeArm,h.symm,tip]
lemma tip_fixed (h : a≠y) : tip a y k ≠ (tip a y k).swap := fun he ↦ h (congr_arg (fun i : Arms n ↦ i.1.1) he)
lemma tip_clear (x : Fin n→Space) : extDD x (charges (tip a y k)) a y=1 := by
  unfold extDD; apply Finset.prod_eq_one; intro i hi; simp [charges,chargeArm, tip, (Finset.mem_erase.mp hi).1, (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1]
lemma tip_degree (ha : a≠y) (hv : u∈ boundSet n N) (hp : N y=0) (hK : k+3 = charges u a) (hT : 3=charges u y) :
    u=tip a y k ∨ u=(tip a y k).swap := by
  obtain ⟨l,_,hl⟩ := through_middle (Ne.symm ha) hv hp hK.le hT.le
  rcases hl with he|he
  · change u=tip a y l at he; rw [he,tip_a ha] at hK; obtain rfl : k=l := by omega
    exact Or.inl he
  change u=(tip a y l).swap at he; rw [he,← arm_switch,tip_a ha] at hK; obtain rfl : k=l := by omega
  exact Or.inr he

variable {X : Points n}

lemma peel (C₀ : G.ColorIndex) (p : ι → ℂ) (W : ι → Fin n→WickPol G)
    (N : Fin n → ℕ) (r : Flavor 0) (hx : X∈conf _) (ha : a≠y)
    (hw : ∀ i v,W i v ∈ shelf G (N v)) (hp : N y=0)
    (H : ∀ b:E4, Points.cons b X ∈ conf _ → ∑ i:ι,p i*bookend X b (W i) (team G r r)=0)
    (k : ℕ) (hl : k ≤ N a)
    (higher : ∀ l>k, ∀ (D : Echo l) (E : Echo 0), payable X p W a y D E=0)
    {d : Space} (hv : Blip (poles X) a y d) :
    payable X p W a y (shoot C₀ k d r) (shoot C₀ 0 (d-(poles X y-poles X a)) r)=0 := by
  classical
  obtain ⟨f,hf,h⟩ := families_split C₀ X p W N r hx hw H
  let u := poles X
  let z := d+u a
  have he := bi_read _ f charges _ hx hv ha (k+3) 3 (fun i hi ↦ ?_) h
  · let R (i : Arms n) := if charges i a=k+3 ∧ charges i y=3 then aeval z (f i)/aeval z (extDD u (charges i) a y) else 0
    let A := tip a y k; let B := boundSet n N
    have hh : A∈ B := Finset.mem_product.mpr ⟨arm_in.mpr hl,arm_in.mpr (Nat.zero_le _)⟩
    have hB : A.swap ∈ B.erase A := Finset.mem_erase.mpr ⟨(tip_fixed ha).symm, arm_reflected hh⟩
    change ∑ i∈B,R i=0 at he; rw [← Finset.sum_erase_add B R hh, Finset.sum_eq_single_of_mem A.swap hB] at he
    · have H (i) (hK : charges i=charges A) : R i=aeval z (f i) := by
        simp only [R,hK,A,tip_a ha,tip_y ha,and_self,↓reduceIte,tip_clear,map_one,div_one]
      rw [H A.swap arm_switch.symm,H A rfl, hf,hf] at he
      change payable X p W y a (shoot C₀ 0 (z-u y) r) (shoot C₀ k (z-u a) r) + payable X p W a y _ _=0 at he
      rw [pay_switch p W _ _ (Ne.symm ha)] at he
      change payable X p W a y (shoot C₀ k (z-u a) r) (shoot C₀ 0 (z-u y) r)+payable X p W a y (shoot C₀ k (z-u a) r) (shoot C₀ 0 (z-u y) r)=0 at he
      rw [←two_mul,show z-u a=d by unfold z; abel, show z-u y=d-(u y-u a) by unfold z; abel] at he; exact (mul_eq_zero.mp he).resolve_left (by norm_num)
    intro i hi hQ; unfold R; apply if_neg; rintro ⟨hK,hT⟩; obtain hm := Finset.mem_erase.mp hi
    exact (tip_degree ha hm.2 hp hK.symm hT.symm).elim hm.1 hQ
  rcases lt_or_ge (charges i a) (k+3) with hh|hh; · exact Or.inr (Or.inl hh)
  rcases lt_or_ge (charges i y) 3 with hu|hu; · exact Or.inr (Or.inr (Or.inl hu))
  obtain ⟨l,hL,ht⟩ := through_middle (Ne.symm ha) hi hp hh hu
  rcases eq_or_lt_of_le hL with hK|hK
  · subst l; right; right; right
    rcases ht with he|he
    · change i=tip a y k at he; rw [he]; exact ⟨tip_a ha,tip_y ha⟩
    change i=(tip a y k).swap at he; rw [he, ← arm_switch]; exact ⟨tip_a ha,tip_y ha⟩
  left; apply MvPolynomial.funext; intro x; change aeval x _ = aeval x _; rw [map_zero,hf]; rcases ht with rfl|rfl
  · exact higher _ hK _ _
  exact (pay_switch p W _ _ ha.symm).trans (higher _ hK _ _)

end YM.SchemeConversionRG11.Corona
