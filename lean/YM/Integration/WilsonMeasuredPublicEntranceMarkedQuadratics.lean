import YM.Integration.WilsonMeasuredPublicEntranceQuadraticProducts
import YM.XSpace.OrthoActor
import YM.XSpace.Twins

/-! The quadratic label B(U) uses the original two-form fields in their six ordered slots.
The diagonal and both occurrences of each off-diagonal component have their original
Wick multiplicities. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceMarkedQuadratics
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceQuadraticProducts
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

def flavor (i:Six):Flavor 0:=Maxwell.Free.cell (left i) (right i)
theorem native_axes(i:Six):edge i=(left i,right i):=(by decide:∀i:Six,edge i=(left i,right i)) i

def tile (hd:4≤d)(i j:Six):HFields G d:=postedTeam hd (flavor i) (flavor j)
theorem transpose_tile (hd:4≤d)(i j:Six):tile (G:=G) hd j i=tile hd i j:=
  Subtype.ext (team_swap G _ _)

def marked (G:Gauge){d:ℕ}(hd:4≤d):Plane ℝ→ₗ[ℝ] HFields G d where
  toFun U:=∑i,∑j,U i j • tile hd i j
  map_add' U V:=by simp [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a U:=by simp [Matrix.smul_apply,Finset.smul_sum,smul_smul]

def spot(i j:Six):Plane ℝ:=fun s t=>if s=i then if t=j then 1 else 0 else 0
theorem read_spot(hd:4≤d)(i j:Six):marked G hd (spot i j)=tile hd i j:=by
  classical
  simp [marked,spot,ite_smul]
theorem transpose_spot(i j:Six):(spot i j).transpose=spot j i:=by
  ext a b
  by_cases hi:b=i <;> by_cases hj:a=j <;> simp [Matrix.transpose_apply,spot,hi,hj]

def symmetrical:Submodule ℝ (Plane ℝ) where
  carrier:={u|u.transpose=u}
  zero_mem':=rfl
  add_mem':=by intro a b ha hb;exact (Matrix.transpose_add a b).trans (congrArg₂ (·+·) ha hb)
  smul_mem':=by intro c a ha;exact (Matrix.transpose_smul c a).trans (congrArg (c • ·) ha)

def fixed (T:Module.End ℂ (HFields G d)):Submodule ℂ (HFields G d):=LinearMap.ker (T-1)
def held (hd:4≤d)(T:Module.End ℂ (HFields G d)):Submodule ℝ (Plane ℝ):=
  symmetrical ⊓ ((fixed T).restrictScalars ℝ).comap (marked G hd)

theorem finite (hd:4≤d)(T:Module.End ℂ (HFields G d))
    (signed:T (marked G hd 1)=marked G hd 1)
    (directional:∀a b:WilsonMeasuredPublicEntranceQuadraticGrid.Four,∀U V:Plane ℝ,U.transpose=U→V.transpose=V→
      T (marked G hd U)=marked G hd U→T (marked G hd V)=marked G hd V→
      T (marked G hd (product (lift (exterior a b)) U V))=
        marked G hd (product (lift (exterior a b)) U V))
    {m:Plane ℝ}(real_slot:m.transpose=m):T (marked G hd m)=marked G hd m:=by
  have symRay (a b:WilsonMeasuredPublicEntranceQuadraticGrid.Four):(lift (exterior a b)).transpose=lift (exterior a b):=by
    ext i j
    change ((exterior a b j i:ℤ):ℝ)=((exterior a b i j:ℤ):ℝ)
    exact_mod_cast (by decide:∀a b:WilsonMeasuredPublicEntranceQuadraticGrid.Four,∀i j:Six,exterior a b j i=exterior a b i j) a b i j
  have entered (u:Plane ℝ):u∈held hd T ↔
      u.transpose=u ∧ T (marked G hd u)=marked G hd u:=by
    change (u.transpose=u ∧ T (marked G hd u)-marked G hd u=0) ↔ _
    simp only [sub_eq_zero]
  have bought:=WilsonMeasuredPublicEntranceQuadraticProducts.original (held hd T)
    ((entered _).mpr ⟨Matrix.transpose_one,signed⟩) (fun a b U hU V hV=>by
      obtain ⟨u,hu⟩:=(entered _).mp hU
      obtain ⟨v,hv⟩:=(entered _).mp hV
      apply (entered _).mpr
      refine ⟨?_,directional a b U V u v hu hv⟩
      simp [product,Matrix.transpose_add,Matrix.transpose_mul,symRay,u,v,mul_assoc,add_comm])
    real_slot
  exact ((entered _).mp bought).2

theorem original (hd:4≤d)(T:Module.End ℂ (HFields G d))
    (fixed_forms:∀u:Plane ℝ,u.transpose=u→T (marked G hd u)=marked G hd u)
    (v:Flavor 0):T (postedTeam hd v v)=postedTeam hd v v:=by
  have one (i j:Six):tile (G:=G) hd i j∈fixed T:=by
    have paid:=fixed_forms (spot i j+spot j i) (by rw [Matrix.transpose_add,
      transpose_spot,transpose_spot,add_comm])
    simp only [map_add,read_spot,transpose_tile hd i j] at paid
    change T (tile hd i j)-tile hd i j=0
    exact sub_eq_zero.mpr (by
      have ha:(2:ℂ) • T (tile hd i j)=(2:ℂ) • tile hd i j:=by simpa [two_smul] using paid
      exact (smul_right_injective _ (by norm_num : (2:ℂ)≠0)) ha)
  let seen:=(fixed T).map (shellSector G d).subtype
  have all:Teams G 0 0≤seen:=by
    rw [label_span,Submodule.span_le]
    rintro _ ⟨i,j,_,rfl⟩
    exact ⟨tile hd i j,one i j,rfl⟩
  obtain ⟨w,hw,same⟩:=all (in_team G v v)
  have identifying:w=postedTeam hd v v:=Subtype.ext same
  rw [identifying] at hw
  exact sub_eq_zero.mp hw
end YM.Integration.WilsonMeasuredPublicEntranceMarkedQuadratics

