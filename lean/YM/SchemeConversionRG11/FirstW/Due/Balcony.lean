import YM.SchemeConversionRG11.FirstW.Due.Robe
/-! Assembly of local first variation and Wick constants under real transformation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD
open scoped BigOperators Classical
variable {G : Gauge} {X : Type*} [AddCommGroup X] [One X] {d : ℕ} {n : Side} (F : Labels.Frames G)
section wonder
variable {I : Type*} [Fintype I] (p q : Cache I) (f g : I→I→ℝ) (B C:I→I→I→ℝ) (L: Module.End ℝ (I→ℝ))
lemma paint_two (he : ∀ x,look x p=look (L x) q) (hp:∀ i j,g i j=∑ a:I,∑ b:I,(accord L i a*accord L j b)*f a b) :
   ∑ i:I,∑ j:I, loot p i j*(f i j:ℝ) = ∑ i:I,∑ j:I,loot q i j*(g i j:ℝ) := by
  simp_rw [second_turn p q L he,Finset.sum_mul]; conv_lhs=> arg 2; intro i; arg 2; intro j
  conv_lhs=> arg 2; intro i; rw [Finset.sum_comm]; arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [hp]; simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
lemma paint_three (he : ∀ x,look x p=look (L x) q) (hp : ∀ i j k,C i j k=∑ a:I,∑ b:I,∑ c:I, (accord L i a * accord L j b * accord L k c) * B a b c) :
   ∑ i:I,∑ j:I, ∑ k:I,root3 p i j k*(B i j k:ℝ)=∑ i:I,∑ j:I,∑ k:I,root3 q i j k*(C i j k:ℝ) := by
  simp_rw [third_turn p q L he, Finset.sum_mul]; rw [abc_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; rw [hp]; simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
end wonder
section Local
variable (K : Who G d → Wind G X) (h : ℝ) (o : Four X) (T : Sky G X)
variable (p q : Part G d)
-- zinc: the rank2 p'' constant giving a linear output on repeated terms
-- moon: scalar all-to-rank3
-- burn: paired output raw *without symmetrization yet*
def zinc (A : Wind G X) : ℂ := ∑ i:Who G d,∑ j:Who G d,loot p i j * ((3*T (K i) (K j) A +2*echoLeg h o i.val (K j) A):ℝ)
def moon := ∑ i:Who G d,∑ j:Who G d,∑ k:Who G d, root3 p i j k * ((T (K i) (K j) (K k)+echoLeg h o i.val (K j) (K k)):ℝ)
def sectorA (i j : Who G d) := (3:ℝ) • (T (K i) (K j))+(2:ℝ) • echoLeg h o i.val (K j)
def burn (p : Part G d) : Wind G X →ₗ[ℝ] Wind G X→ₗ[ℝ]ℂ := ∑ i:Who G d,∑ j:Who G d,∑ k:Who G d,root3 p i j k • ((((LinearMap.mul ℝ ℝ).compl₂ (tape k.val h o)).comp (sectorA K h o T i j)).compr₂ Complex.ofRealCLM.toLinearMap)
lemma sector_eq (A : Wind G X) (i j : Who G d) : sectorA K h o T i j A=3*T (K i) (K j) A + 2*echoLeg h o i.val (K j) A := rfl
lemma burn_eq (p : Part G d) (A B:Wind G X) : burn K h o T p A B=∑ i:Who G d,∑ j:Who G d,∑ k:Who G d,root3 p i j k*(sectorA K h o T i j A*tape k.val h o B:ℝ) := by simp only [burn,LinearMap.sum_apply]; rfl
variable (S : Module.End ℝ (Wind G X)) (L : Module.End ℝ (Dot G d)) (ht : TiltM L S o h)
variable (he : ∀ x,look x p=look (L x) q)
variable (hk : ∀ i:Who G d, ∑ a:Who G d, accord L i a • S (K a)=K i)
variable (hp : ∀ A B C,T (S A) (S B) (S C) = T A B C)
include ht
lemma swayed (i : Who G d) (A B:Wind G X) : echoLeg h o i.val (S A) (S B) = ∑ a:Who G d,accord L i a*echoLeg h o a.val A B := by
  change guardH d o h (S A) (S B) i=_; rw [←ht.upright, ac_sum];rfl
include hk hp
lemma trills (i j : Who G d) (A:Wind G X) : sectorA K h o T i j (S A)=∑ a:Who G d,∑ b:Who G d, (accord L i a* accord L j b)*sectorA K h o T a b A := by
  have hw : echoLeg h o i.val (K j) (S A)=∑ a:Who G d,∑ b:Who G d,(accord L i a* accord L j b)*echoLeg h o a.val (K b) A := by
    -- don't rewrite b if i=j
    rw [←hk j]; simp only [map_sum,LinearMap.sum_apply,map_smul, LinearMap.smul_apply, smul_eq_mul, swayed h o S L ht, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
  have hv : T (K i) (K j) (S A) = ∑ a:Who G d,∑ b:Who G d,(accord L i a*accord L j b)* T (K a) (K b) A := by
    rw [←hk i,←hk j]; simp only [map_smul,map_sum, LinearMap.sum_apply,LinearMap.smul_apply, Finset.mul_sum, smul_eq_mul]; simp_rw [hp]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
  rw [sector_eq, hw,hv]; simp_rw [sector_eq,mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> (apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring)
include he
lemma tint_zinc (A : Wind G X) : zinc K h o T p A=zinc K h o T q (S A) := paint_two p q (fun i j=>sectorA K h o T i j A) (fun i j=>sectorA K h o T i j (S A)) L he (fun i j=>trills K h o T S L ht hk hp i j A)
lemma tint_burn (A B:Wind G X) : burn K h o T p A B=burn K h o T q (S A) (S B) := by
  rw [burn_eq,burn_eq]; apply paint_three p q _ _ L he; intro a b c; have hc : tape c.val h o (S B)=∑ j:Who G d,accord L c j*tape j.val h o B := by
    have hj:= ac_sum L (taxes d o h B) c; rw [ht.flow] at hj; exact hj -- definitional
  rw [hc,trills K h o T S L ht hk hp]; simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
lemma tint_moon : moon K h o T p=moon K h o T q := paint_three _ _ (fun i j k=> T (K i) (K j) (K k)+echoLeg h o i.val (K j) (K k)) (fun i j k=> T (K i) (K j) (K k)+echoLeg h o i.val (K j) (K k)) L he (fun i j k=>by
  have hh a : S (∑ u:Who G d,accord L a u • K u)= K a := by rw [map_sum]; simpa only [map_smul] using! (show ∑ u:Who G d, S (accord L a u • K u)=K a from by simp only [map_smul]; exact hk a)
  rw [←hh i,←hh j,←hh k,hp,swayed h o S L ht]; simp only [map_sum,map_smul, LinearMap.smul_apply, LinearMap.sum_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]; conv_lhs=> arg 2; intro u; rw [Finset.sum_comm] -- order k? inspect
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; ring
  apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; ring)
end Local
end YM.RG11.FirstW
