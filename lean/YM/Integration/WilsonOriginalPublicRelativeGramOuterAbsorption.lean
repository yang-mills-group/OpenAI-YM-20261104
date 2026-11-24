import YM.Integration.WilsonOriginalPublicRelativeGramOuterCards
import YM.Integration.WilsonOriginalPublicPivotSelf

/-! Self-hearing of an evaluated complete exterior column. The two mixed
responses and the prior constant enter under their original signed sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterAbsorption
open Filter Finset Function Lattice RG Wilson Source PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicWickGram (nodes reading)
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicPivotCross (detector old left right Film)
open scoped BigOperators Classical

private theorem absorb {k x z c : ℝ} (kp : 0<k) (xp : 0 ≤ x) (zp : 1 ≤ z) (cp : 0 ≤ c)
    (p : k*x^2  ≤  c*z^2+1+(k/8)*(1+x)^2) :
    x  ≤  max 1 ((c+k/4+5)/(k/2))*z := by
  have zsq : 1 ≤ z^2 := one_le_pow₀ zp
  have quarter : k/4 ≤ (k/4)*z^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left zsq (show 0 ≤ k/4 by positivity)
  have e := mul_nonneg kp.le (sq_nonneg (x-1))
  have nn := mul_nonneg kp.le (sq_nonneg x)
  apply WilsonOriginalPublicPivotReflected.absorption (k:=k/2) (e:=0) (u:=0) (t:=0)
    (c:=c+k/4) (by positivity) xp le_rfl zp (by positivity) (by norm_num)
    (by norm_num) (by norm_num)
  nlinarith only [p, quarter, e, nn]

variable {G : Gauge} {h : ℕ} {B : Local.Physical.Deck G} {I : Type} [Fintype I]

theorem original (axis : Axis) (leg : I  →  Glyph B h) (covers : Injective leg) :
    ∃k τ : ℝ, 0<k ∧ 0<τ ∧
    ∀(R : Run G) (W : Initialize G) {L : Type} [Fintype L]
      (d : Fin 2  →  ℕ) (v : (i : Fin 2)  →  (R.family.labels.level (d i)).Coeff)
      (X : L  →  Sample 2) (μ : L  →  ℂ) (q : ℕ) (g : ℝ) (coarse : ℂ)
      (a : I  →  ℂ) (A B : I  →  Film W) (c z : ℝ),
      let H := detector W X μ q g
      let U := left R W d v a A
      let V := right R W d v a B
      0 ≤ c  →  1 ≤ z  →  ‖(fun i j=>H (A i*B j))-reading axis (nodes axis) leg‖ ≤ τ  → 
      ‖coarse‖ ≤ c*z^2  →  ‖sampled R W d v X μ univ q g-coarse‖ ≤ 1  → 
      ‖((∑i,star (a i)*H (A i*V))+(∑i,a i*H (U*B i)))+
        (old R W d v X μ q g+H (U*V))‖ ≤ (k/8)*(1+‖a‖)^2  → 
      ‖a‖ ≤ max 1 ((c+k/4+5)/(k/2))*z := by
  obtain ⟨k,τ,kp,hp,rank⟩ := WilsonPositionProgramPublicWickGram.original axis leg covers
  refine ⟨k,τ,kp,hp,?_⟩
  intro R W L inst d v X μ q g coarse a A B c z H U V cp zp gram paid witnessed residue
  let y := sampled R W d v X μ univ q g
  let p := fun i j => H (A i*B j)
  let remainder := ((∑i,star (a i)*H (A i*V))+(∑i,a i*H (U*B i)))+(old R W d v X μ q g+H (U*V))
  have split : y=assay a a p+remainder := by
    rw [show y=_ from WilsonOriginalPublicPivotCross.spread R W d v X μ q g a A B]
    change _+_+_= _+(_+_)
    abel
  have income : ‖y‖ ≤ c*z^2+1 := by
    calc ‖y‖  ≤  ‖y-coarse‖+‖coarse‖ := norm_le_norm_sub_add y coarse
         _  ≤  _ := by linarith
  apply absorb kp (norm_nonneg a) zp cp
  calc k*‖a‖^2  ≤  ‖assay a a p‖ := rank p gram a
       _ = ‖y-remainder‖ := by rw [split,add_sub_cancel_right]
       _  ≤  ‖y‖+‖remainder‖ := norm_sub_le .. 
       _  ≤  _ := add_le_add income residue

end YM.Integration.WilsonOriginalPublicRelativeGramOuterAbsorption
end
