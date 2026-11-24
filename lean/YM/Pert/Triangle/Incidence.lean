import YM.Pert.Triangle.ShellFan
import YM.Next.RANK.GaussLeg
/-! Separated Wick moment at linearly polarized polynomial vertices by occurrence expansion. Needed to test a triangle without assuming that arbitrary weight-six field shifts stay in the undifferentiated columns. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Pert.Triangle.Receipt
open Maxwell Analysis Set Function Wick Matrix Next.Rank.Normal MvPolynomial
open scoped Topology ContDiff Classical
variable {G:Gauge} {J : Type} [Fintype J] (loc : J → Fin 3) (g : J→ℕ)
variable (L : (j:J)→ Probe G (g j)) (x:Points 3) (hx:x∈conf 3)
local notation "I3" => Fin 3

def block (i:I3) := ∏ j ∈ (Finset.univ.filter (fun j=>loc j=i)), symbol (g j) (L j)
def draw := Wick.moment G x (block loc g L)
def tours (P:Equiv.Perm J) := (∏ j∈Finset.univ.filter (fun j=>loc j < loc (P j)), (legKernel (L j) (L (P j)) (x (loc j)-x (loc (P j))):ℂ))
def sumTours := ∑ P∈register loc Finset.univ, tours loc g L x P

include hx
lemma tour_base {a : ∀ j:J, Fin (legDim G (g j))} (hL : ∀j, L j = coordinateLeg (⟨g j,a j⟩ : Slot G)):
  draw loc g L x = sumTours loc g L x := by
  let Z j := (loc j, (⟨g j,a j⟩:Slot G))
  have h : ∀ i,block loc g L i = ∏ j∈Finset.univ.filter (fun j=>loc j=i), MvPolynomial.X (Z j).2 := by
    intro i; exact Finset.prod_congr rfl fun j _=>by rw [hL]; exact symbol_coordinate (⟨g j,_⟩:Slot G)
  rw [draw,Wick_reads hx _, funext h]
  have hh : (∏ i:I3, rename (R:=ℂ) (fun y=> (i,y)) (∏ j∈Finset.univ.filter (fun j=> loc j=i), MvPolynomial.X (Z j).2)) = glyphs Z Finset.univ := by
    simp_rw [map_prod]
    calc _ = ∏ i:I3,∏ j∈Finset.univ.filter (fun j=>loc j=i), MvPolynomial.X (Z j) := Finset.prod_congr rfl fun i _=>Finset.prod_congr rfl (fun j hj=> (rename_X ..).trans (congrArg (fun u:Fin 3=> MvPolynomial.X (u,(Z j).2)) (Finset.mem_filter.mp hj).2.symm))
         _ = _ := Finset.prod_fiberwise (κ:=I3) Finset.univ loc _
  have H a b (hab : loc a=loc b) : (frameX hx (G:=G)).cov (Z a) (Z b)=0 := if_pos hab
  rw [hh,headed loc (frameX hx) Z H]
  unfold sumTours
  apply Finset.sum_congr rfl; intro P hP
  have hP' := Finset.mem_filter.mp hP |>.2
  exact Finset.prod_congr rfl fun j _=> (if_neg (hP'.2.1 j (Finset.mem_univ j)).symm).trans (show (Wick.entry (Z j).2 (Z (P j)).2 _ _)=_ from by rw [hL j,hL (P j)];rfl)
omit hx

def lineAt (j : J) : Probe G (g j) →ₗ[ℝ] WickPol G where
  toFun v := symbol (g j) v
  map_add' u v := by unfold symbol;dsimp;simp only [Complex.ofReal_add,LinearMap.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' r v := by
    change symbol (g j) (r • v) = r • symbol (g j) v
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) r,smul_eq_C_mul]; unfold symbol; dsimp; simp only [Complex.ofReal_mul, LinearMap.smul_apply,smul_eq_mul,map_mul, ←mul_assoc,Finset.mul_sum]
end YM.Pert.Triangle.Receipt
