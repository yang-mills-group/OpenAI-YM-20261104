import YM.SchemeConversionRG11.FirstW.Hart.Gaze
import YM.Pert.Position.Board
/-! Put E actual quotiented-comparator operators on clamped Deck. Only coordinate lift in this module. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Topology Deck Maxwell MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {r d : ℕ} (F : Labels.Frames G)
def cloak (p : Position.E F d) : Part G d := (killCompl (f:=fun x:Who G d=>x.val) Subtype.val_injective) (Full.sections _ _ p)
lemma stretch (p : Position.E F d) : uncap (cloak F p)=Full.sections _ _ p := by
  unfold uncap cloak
  obtain ⟨u,hu⟩:= (Full.sections _ _ p).exists_rename_eq_of_vars_subset_range (fun x:Who G d =>x.val) Subtype.val_injective (fun a ha=> ⟨⟨a, Full.height_le (RawLabels.physicalLabel F d p) a ha⟩, rfl⟩)
  rw [←hu,killCompl_rename_app]
def robes (d : ℕ) : Position.E F d→ₗ[ℂ] Part G d := ((killCompl (f:=fun x:Who G d=> x.val) Subtype.val_injective).toLinearMap).comp (Full.sections _ _)
lemma robes_eq (p : Position.E F d): robes F d p=cloak F p:=rfl
abbrev fee (k : Who G d) := mass k.val
lemma height_pass (p : Position.E F d) {s : Who G d →₀ ℕ} (h : s ∈ (cloak F p).support) : Finsupp.weight fee s ≤ d := by
  let f: Who G d → Labels.Key G:= Subtype.val
  have he : ∀ s : Who G d→₀ℕ,Labels.height (Finsupp.mapDomain f s)= Finsupp.weight fee s := by
    intro b; induction b using Finsupp.induction_linear with
    | zero=> simp [Labels.height]
    | add b c i j=> simp only [Labels.height,Finsupp.mapDomain_add,map_add] at *;rw [i,j]
    | single a b=> simp only [Labels.height,Finsupp.mapDomain_single,Finsupp.weight_single];rfl
  let q:=RawLabels.physicalLabel F d p
  have hp : q.val=rename f (cloak F p):= (stretch F p).symm
  have hu : Finsupp.mapDomain f s∈q.val.support:= by rw [mem_support_iff,hp,coeff_rename_mapDomain f Subtype.val_injective]; exact mem_support_iff.mp h
  rw [←he];exact (mem_restrictSupport_iff ℂ).1 (show q.val∈Labels.limited G d from q.property.1) hu
-- dish derivative coefficients at zero
abbrev D1 {I : Type*} (i : I) (p : Cache I):=pderiv i p
def loot {I : Type*} (p : Cache I) (i j:I) : ℂ := coeff 0 (D1 j (D1 i p))
def root3 {I : Type*} (p : Cache I) (i j k : I) : ℂ := coeff 0 (D1 k (D1 j (D1 i p)))
lemma commute {I : Type*} (p : Cache I) (i j : I) : D1 i (D1 j p)=D1 j (D1 i p) := by
  by_cases h:i=j; · subst j; rfl
  apply MvPolynomial.ext; intro s
  simp only [D1,coeff_pderiv,Finsupp.add_apply,Finsupp.single_apply];rw [if_neg h,if_neg (Ne.symm h),add_right_comm s]; ring
lemma nonzero_leaf {I : Type*} (w : I→ℕ) (s : I →₀ ℕ) (hs:s≠0) (h : ∀ i,w i≥2) : 2 ≤ Finsupp.weight w s := by
  obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hs
  change s i≠ 0 at hi; nth_rw 1 [←Finsupp.sub_add_single_one_cancel hi];simp only [map_add,Finsupp.weight_single,one_smul]; exact (h i).trans (Nat.le_add_left ..)
lemma leafup {I : Type*} (p : Cache I) (i:I) {s:I →₀ ℕ} (hp : s∈(D1 i p).support) : (s+Finsupp.single i 1)∈p.support := mem_support_iff.mpr (fun hx=> mem_support_iff.mp hp (by rw [D1,coeff_pderiv,hx,zero_mul]))
lemma top_money (p : Position.E F d) (k j l : Who G d) (h : root3 (cloak F p) k j l≠0) : fee l+fee j+fee k ≤ d := by
  have H:= height_pass F p (leafup _ k (leafup _ j (leafup _ l (mem_support_iff.mpr h)))); simpa only [map_add,map_zero,Finsupp.weight_single,one_smul,zero_add] using H
lemma top_six (p : Position.E F 6) (k j l : Who G 6) (h : root3 (cloak F p) k j l≠0) : fee l=2 ∧ fee j=2 ∧ fee k=2 := by
  have H:= top_money F p k j l h; unfold fee mass at *; omega
lemma leaf_floor (a : Who G d) : fee a ≥ 2 := Nat.le_add_left ..
lemma bill_three (p : Position.E F 6) (k j l : Who G 6) : D1 l (D1 j (D1 k (cloak F p))) = C (root3 (cloak F p) k j l) := by
  apply MvPolynomial.ext; intro s; by_cases h:s=0; · subst s; rw [coeff_zero_C]; rfl
  rw [coeff_C_of_ne_zero h]; by_contra he
  have ht:= height_pass F p (leafup _ _ (leafup _ j (leafup _ l (mem_support_iff.mpr he)))) -- first _ infer
  have H:= nonzero_leaf (fee (G:=G)) s h leaf_floor; have hu := leaf_floor k; have hv:=leaf_floor j; have hz:=leaf_floor l
  simp only [map_add,Finsupp.weight_single,one_smul] at ht; omega
lemma const_right {I : Type*} [Fintype I] (p q : Cache I) (he:coeff 0 p=coeff 0 q) (h : ∀ i, D1 i p=D1 i q) : p=q := by
  apply MvPolynomial.ext; intro s; by_cases hr:s=0; · rw [hr]; exact he
  obtain ⟨i,hi⟩:= Finsupp.ne_iff.mp hr
  change s i≠0 at hi
  let t := s-Finsupp.single i 1
  have hE : (↑(t i):ℂ)+1 ≠ 0 := by exact_mod_cast (by omega : t i+1≠0)
  apply mul_right_cancel₀ hE; rw [show coeff s p * _ = coeff t (D1 i p) from (by rw [D1,coeff_pderiv, show t+ _=s from Finsupp.sub_add_single_one_cancel hi]),h i]; rw [D1,coeff_pderiv,show t+ _=s from Finsupp.sub_add_single_one_cancel hi]
lemma bill_two (p : Position.E F 6) (k j : Who G 6) : D1 j (D1 k (cloak F p)) = C (loot (cloak F p) k j) + ∑ t:Who G 6,C (root3 (cloak F p) k j t) * X t := by
  apply const_right
  · rw [coeff_add,coeff_zero_C, coeff_sum,Finset.sum_eq_zero,add_zero]; rfl; intro i _; rw [coeff_C_mul]; simp
  intro i; rw [bill_three]; unfold D1; rw [_root_.map_add,_root_.map_sum,pderiv_C,zero_add,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; simp; intro j _ hj; rw [pderiv_C_mul,pderiv_X_of_ne hj,mul_zero]
end YM.RG11.FirstW
