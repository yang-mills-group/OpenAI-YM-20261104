import YM.SchemeRG11.Wilson.Grotto
import YM.SchemeRG11.Cover.Ferry
import YM.SchemeRG11.MSDetector.Dye
/-! Vanishing tadpoles and three long-line estimates. Generic enough to handle both PT limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G : Gauge} {N : Side} {B K X : Type*}[AddCommGroup X][One X]
def grass (D:Dose (Code G X) ℝ): Prop:=∀ i j, i.2 ≠ j.2 → D.pulse i j=0
open YM.SchemeRG11.MSDetector
variable (x:Four X)(i j:Axis)
lemma palate (D:Dose (Code G X) ℝ)(a b:G.ColorIndex)(h:a≠b)(H:grass D)(t s:Axis): D.bed (tongue x i j t a) (tongue x i j s b)=0:=by
 have hp(e f:Edge (Four X)):D.pulse (e,a) (f,b)=0:= H _ _ h
 fin_cases t <;> fin_cases s <;> simp [Dose.bed,sense,Dose.windfall,tongue,hp]
lemma palate₂ (D:Dose (Code G X) ℝ)(a b:G.ColorIndex)(h:a≠b)(H:grass D)(t:Axis): D.bed (tongue x i j t a) (intake x i j b)=0:=by unfold intake Dose.bed; rw [_root_.map_sum]; apply Finset.sum_eq_zero; intro u _; apply palate x i j D a b h H
lemma paled (D:Dose (Code G X) ℝ)(H:grass D)(a b c:G.ColorIndex)(s t:Axis): D.heat (leaf (intake x i j a) * (Triangle.colorF b c a • staple x i j b c s t)) = leaf (intake x i j a)*(Triangle.colorF b c a • staple x i j b c s t):=by
 unfold staple; split <;> rename_i h
 · rw [mul_smul_comm,map_smul] -- only once maybe
   by_cases hi:a=b; · simp [hi]
   by_cases hj:a=c; · simp [hj]
   by_cases hk:b=c; · simp [hk]
   let A:=intake x i j a; let B:=tongue x i j s b;let C':=tongue x i j t c
   have h1:sense (D.windfall A) B=0:= (D.bed_comm ..).trans (palate₂ x i j _ b a (Ne.symm hi) H s); have h2:sense (D.windfall A) C'=0:=(D.bed_comm ..).trans (palate₂ x i j _ c a (Ne.symm hj) H t)
   have h3:sense (D.windfall B) C'=0:=palate x i j _ b c hk H s t
   congr 1; change D.heat (leaf A*(leaf B*leaf C'))=_; rw [Dose.zephyr,Dose.zephyr,Dose.lit,taste,h3,map_zero,add_zero,vent_l,taste,taste,h1,h2]; simp;rfl
 simp
lemma vapid(D:Dose (Code G X) ℝ)(H:grass D):D.heat (Tree.cost x i j)=Tree.cost x i j:=by
 unfold Tree.cost; split
 · simp_rw [map_smul,oreL, stockpile,Finset.mul_sum,_root_.map_sum,paled x i j _ H]
 exact map_zero _
lemma oneGrade (q:Stem K ℝ): IsHomogeneous (leaf q) 1:=by
 induction q using Finsupp.induction_linear with
 | zero=> rw [map_zero]; exact isHomogeneous_zero ..
 | add a b ha hb=> rw [map_add]; apply IsHomogeneous.add <;> assumption
 | single q a=> rw [leaf,Finsupp.linearCombination_single, MvPolynomial.smul_eq_C_mul]; apply isHomogeneous_C_mul_X
lemma gradeFace :IsHomogeneous (Tree.cost (G:=G) x i j) 3:=by
 unfold Tree.cost; split
 · rw [MvPolynomial.smul_eq_C_mul]; apply IsHomogeneous.C_mul; apply IsHomogeneous.sum
   intro a _; apply IsHomogeneous.mul (n:=2) (oneGrade _)
   unfold oreL stockpile; refine IsHomogeneous.sum _ _ _ (fun s hs=>IsHomogeneous.sum _ _ _ fun t ht=> IsHomogeneous.sum _ _ _ fun b hb=>IsHomogeneous.sum _ _ _ fun c hc=>show IsHomogeneous _ 2 from ?_)
   rw [MvPolynomial.smul_eq_C_mul]; apply IsHomogeneous.C_mul; unfold staple; split
   · exact IsHomogeneous.mul (oneGrade _) (oneGrade _)
   apply isHomogeneous_zero
 apply isHomogeneous_zero
end YM.SchemeRG11.Acorn
