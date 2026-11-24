import YM.FVAAlt2.Restriction

/-! Hessian accounting at the Landau embedding. Includes ghost sign in
ordered derivative slots and orbit measure convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Finset Pert.Orb SchemeRG11.Sway Function
open MS MS.Koszul MS.Native MS.Plane MS.Landau MS.Cylinder MS.Cylinder.Taylor MS.Book MS.Native.Chart
open MS.Cylinder.Lab MS.Native.Wilsonian
open Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {G:Gauge}{n:Side}
local notation "X" => Land G n
local notation "Q" => Potential G n
variable {ι κ:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))

local notation "L" => embeddingM A b
local infix:70 " ⋄ " => product isOdd
local notation "Y" => Raw (Alpha ι κ) ℂ
local notation "v" => ink (dirA4 (κ:=κ) A)

lemma LANDpair (i j:Alpha ι κ) : v LAND [i,j]=(↑((landLaw G n).P (dirA4 A i) (dirA4 A j)):ℂ):=by
  let e:= fun z:Alpha ι κ=> g0 G n (dirA4 A z)
  rw [LAND_eq,ink_ctrl_one (dirA4 A) (g0 G n) diff_action]
  change (↑(layer (e j) (layer (e i) (Pert.Orb.action G n)) 0):ℂ)=_
  let f:= Pert.Orb.action G n
  rw [show layer (e j) (layer (e i) f) 0 = iteratedFDeriv ℝ 2 f 0 ![e j,e i] from ?_,jets_action.2.2,form_symm]; rfl
  unfold layer
  have he:ContDiffAt ℝ ω f 0:= diff_action
  have hu:= ((he.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)|>.hasFDerivAt.clm_apply (hasFDerivAt_const (e i) (0:Q)))
  rw [hu.fderiv]; simp [iteratedFDeriv_two_apply]

section
variable {τ:Type}{q:Sector τ}
-- derivative pair on even/odd ordered linear factors
lemma coeff_one_product (x:τ)(f g:Raw τ ℂ): product q f g [x]= f [x]*g []+f []*g [x]:= by
  rw [D_eval x (product _ _ _),D_product]; simp
lemma coeff_two_product (x y:τ)(f g:Raw τ ℂ)(h:f []=0)(hg:g []=0): product q f g [x,y]= f [x]*g [y]+ cross (q x) (q y)* f [y]*g [x] := by
  rw [D_eval x (product _ _ _),D_product,Pi.add_apply,coeff_one_product,coeff_one_product]; simp [h,hg]
end

lemma pair_ghost_general (x y:Alpha ι κ) : ghostAction A b [x,y]=∑ i:κ,∑ j:κ,
    ((if antigh i=x ∧ gh j=y then 1 else 0)-(if antigh i=y ∧ gh j=x then 1 else 0)) * (fpLetter b i j 0:ℂ):=by
  classical
  unfold ghostAction
  simp_rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
  rw [coeff_two_product (h:=rfl) (hg:=by simp [atLetter]) x y,coeff_one_product,coeff_one_product]
  by_cases he:(antigh i=y ∧ gh j=x)
  · obtain ⟨rfl,rfl⟩:=he; simp [atLetter,antigh,gh,isOdd]
  by_cases hy: antigh i=y <;> by_cases hx:antigh i=x <;> by_cases hL: gh j=y <;> by_cases hg:gh j=x <;> simp_all [atLetter] -- loops?

def Rgh {ι κ:Type} [DecidableEq κ] : Matrix (Alpha ι κ) (Alpha ι κ) ℂ
 | gh i, antigh j=> if i=j then 1 else 0
 | antigh i, gh j=> if i=j then -1 else 0
 | _,_=>0

lemma ghostActpair (x y:Alpha ι κ): ghostAction A b [x,y]= Rgh x y:= by
  rw [pair_ghost_general]; rcases x with x|x|x <;> rcases y with y|y|y <;>
    simp [gh,antigh,Rgh,ite_mul,fp_flat,ite_and] -- check
  · by_cases h:x=y <;> simp [h, eq_comm]
  by_cases h:x=y <;> simp [h]

def posHessian (G:Gauge)(n:Side) : Matrix (Mode G n) (Mode G n) ℂ:=
  pairMatrix ((1/2:ℂ) • docket n (Wilsonian.core G 0))

def Rpair : Matrix (Alpha ι κ) (Alpha ι κ) ℂ:= fun x y=> -(↑((landLaw G n).P (dirA4 A x) (dirA4 A y)):ℂ)+Rgh x y

def Rcov : Matrix (Alpha ι κ) (Alpha ι κ) ℂ
 | avec i, avec j=> ↑((landLaw G n).wick (A.coord i) (A.coord j))
 | x,y=> Rgh x y

lemma HessSame(x y:Mode G n): posHessian G n x y= (1/2:ℂ)* docket n (Wilsonian.W G) [x,y] := by
  change (1/2:ℂ)* docket n (Wilsonian.core G 0) [x,y] = _; rw [Wilsonian.at_rest]
  change _*docket n (model 2 _) _=_; congr 1; rw [show docket n (model _ _) =_ from enterShim (b:=true) n 2]; exact enough _ (by simp)

lemma RGHpair : L * posHessian G n * (L).transpose = Rpair A := by
  rw [show posHessian G n=pairMatrix ((1/2:ℂ) • docket n (Wilsonian.W G)) from Matrix.ext fun i j=>HessSame i j, ← pull_pairMatrix,on_W]
  ext i j
  simp only [pairMatrix,Pi.add_apply,Pi.neg_apply, LANDpair,ghostActpair]; rfl

lemma bos_eq (i j:ι) : ∑ k:ι, (↑((landLaw G n).P (A i) (A k)):ℂ) * (↑((landLaw G n).wick (A.coord k) (A.coord j)):ℂ) = if i=j then 1 else 0:=by
  let F:=landLaw G n
  have hs (k:ι): F.wick (A.coord k) (A.coord j)= A.coord k (F.inverse (A.coord j)):= by
    calc
      _= F.P (F.inverse (A.coord j)) (F.inverse (A.coord k)):= by rw [F.applies]; rfl
      _= _ := by rw [F.turns,F.applies]
  have hu(z:X): ∑ k:ι, F.P (A i) (A k)* A.coord k z=F.P (A i) z := by
    nth_rw 2 [← A.sum_repr z]
    rw [map_sum]
    exact sum_congr rfl fun k _=> Eq.trans (mul_comm _ _) (Eq.symm (map_smul _ _ _))
  change ∑ k, (↑(F.P _ _):ℂ)*(↑(F.wick _ _):ℂ)=_
  simp_rw [hs, ←Complex.ofReal_mul, ←Complex.ofReal_sum, hu,F.turns (A i) (F.inverse _),F.applies]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,Finsupp.single_apply]; split <;> simp [*]

lemma Rinverse : Rpair A (κ:=κ)* Rcov A= -(1:Matrix (Alpha ι κ) (Alpha ι κ) ℂ) := by
  ext (i|i|i) (j|j|j) <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Rpair,Rcov,dirA4,Rgh,Matrix.one_apply,bos_eq]
  all_goals by_cases h:i=j <;> simp [h]
end YM.FVAAlt2
