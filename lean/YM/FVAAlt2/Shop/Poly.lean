import YM.FVAAlt2.Shop.RealInk
import YM.Comparison.Stencils.Letters
/-! At the stencil we can use the polynomial sensor convention in
`Comparison/Stencils/Letters`. This is the *same* kernel before Fourier effects. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open MS MS.Native MS.Landau MS.Koszul MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor
open PertExtension PertExtension.Series PertExtension.Series.Radial
open Lattice Function Set Finset Filter Topology Wilson Labels Source Source.Drops
open Planned.PrimaryIntegral295.Place
open Comparison.Stencils (columnSeries cylinder)
open Comparison.Stencils.Symbols
open scoped Topology ContDiff
variable {G:Gauge}{d:ℕ}{n:Side}{F:Labels.Frame G d}(S : SectionData F)
local notation "W"=> Spot S.stencil
local notation "M"=> W × Conn G
local notation "D₀"=> Dev S.stencil G
local notation "L"=> (placeEdge (S:=S.stencil))
section
variable {I:Type}[DecidableEq I][Fintype I]
def Λ (p:I×G.ColorIndex→ℝ)(i:I):G.Color:= WithLp.toLp 2 (fun j=> p (i,j))
def isob (G:Gauge)(I:Type)[Fintype I]: Lot G I≃ₗ[ℝ] (I×G.ColorIndex→ℝ) where
 toFun X i:=X i.1 i.2
 invFun:= Λ
 left_inv _:=rfl
 right_inv _:=rfl
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def bar (G:Gauge)(I:Type)[Fintype I]: Module.Basis (I×G.ColorIndex) ℝ (Lot G I):= Module.Basis.ofEquivFun (isob G I)
omit [DecidableEq I] in
lemma coord_isob (i:I×G.ColorIndex)(x:Lot G I): (bar G I).coord i x=x i.1 i.2:=by
 change (bar G I).equivFun x i=_; unfold bar; rw [Module.Basis.equivFun_ofEquivFun]; rfl
lemma privbar (i:I×G.ColorIndex): bar G I i=priv i:=by
 apply (bar G I).equivFun.injective; funext k; change (bar G I).coord k _=(bar G I).coord k _; rcases i with ⟨i,a⟩; rcases k with ⟨k,b⟩; rw [coord_isob (x:=priv _), Module.Basis.coord_apply]; by_cases h:i=k <;> by_cases he:a=b <;> simp_all [priv,Pi.single_apply,Finsupp.single_apply,baseC,eq_comm (a:=i),eq_comm (a:=a)];
set_option linter.unusedSectionVars false
abbrev bos_poly (I:Type)[Fintype I]: MvPolynomial I ℂ→ₐ[ℂ] Bos I:= MvPolynomial.aeval Bos.letter
open MvPolynomial
lemma poly_read(x:I→ℂ)(p:MvPolynomial I ℂ): Bos.evalAt x (bos_poly I p)=aeval x p:=by
 induction p using MvPolynomial.induction_on with
 | C a=> simp [bos_poly]; exact Bos.eval_constant ..
 | add p q hp hq=> rw [map_add,map_add,hp,hq,map_add]
 | mul_X p i h=> rw [map_mul,map_mul,h,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_X]; have he:= Bos.eval_letter x (1:Bos I) i; rw [mul_one,show Bos.evalL x 1=1 from map_one (Bos.evalAt x),mul_one] at he; rw [show Bos.evalAt x _=x i from he]
lemma all_bos : Surjective (bos_poly I):=by
 intro x; apply Bos.induction (fun x: Bos I=>∃ p,bos_poly I p=x) ⟨1,map_one _⟩ _ _ _ x <;> clear x
 · rintro p q ⟨P,rfl⟩ ⟨Q,rfl⟩; exact ⟨P+Q,map_add ..⟩
 · rintro r x ⟨p,rfl⟩; exact ⟨r • p,map_smul ..⟩
 · rintro i _ ⟨p,rfl⟩; exact ⟨X i*p,by simp [map_mul,bos_poly]⟩
lemma poly_eq {I:Type}(p q:MvPolynomial I ℂ)(h:∀ l:I→ℝ,(MvPolynomial.aeval (Complex.ofReal ∘ l) p:ℂ)=MvPolynomial.aeval (Complex.ofReal ∘ l) q): p=q:= by
 apply MvPolynomial.funext_set (fun _=> Set.range (fun x:ℝ=>(x:ℂ))) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective)
 intro x hx; choose y hy using fun k=> hx k (Set.mem_univ k); rw [show x=Complex.ofReal ∘ y from funext fun i=> (hy i).symm]; exact h _
lemma bos_ext (x y:Bos I)(he:∀ l:I→ℝ,Bos.evalAt (Complex.ofReal ∘ l) x=Bos.evalAt (Complex.ofReal ∘ l) y) : x=y:= by
 obtain ⟨p,rfl⟩:= all_bos x; obtain ⟨q,rfl⟩:= all_bos y; apply congr_arg (bos_poly I); apply poly_eq; simp_rw [poly_read] at he; exact he
end
variable (j:F.Index){H:Hol G}(h:S.Sound H)
include h
lemma port_poly (k:ℕ): (bos_poly M (symbol S.stencil (cylinder S j) k)).val=mask k (ink Native.priv (port S j)):=by
 let B:=bar G W; let x:=Bos.bob B (port S j) (port_germ ..) k
 have he: (bos_poly M (symbol S.stencil (cylinder S j) k))=x:=by
    apply bos_ext; intro l; rw [poly_read]; set y:D₀:= Λ l
    have hz(i:M): B.coord i y=l i:=by apply coord_isob (G:=G) i y
    rw [← funext hz]; change _=Bos.evalAt (fun i=>((B.coord i y:ℝ):ℂ)) x; rw [show Bos.evalAt _ x= _ from Bos.sphere B y (port S j) _ k]
    rw [show Complex.ofReal ∘ _ = fun i:M=> (↑(coordinate i y):ℂ) from funext fun i=> congr_arg Complex.ofReal (by rw [coordinate_value]; exact coord_isob ..)]
    rw [show MvPolynomial.aeval _ _= _ from symbol_patch S.stencil (cylinder S j) k y ]; -- Γ
    let q:=port S j; unfold Tensor.diagonal Tensor.coeff Radial.jet
    rw [smul_apply]; have ht: cylinder S j ∘ (pore (S:=S.stencil))= Complex.ofRealCLM ∘ q:= funext fun x=> (fieldReal_in S j h (pore x)).symm
    rw [ht,ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM (port_germ S j) le_top]; push_cast; simp [Complex.real_smul]
 rw [he]; change mask k (ink _ _)=_; rw [show (⇑B)=priv from funext fun i=> privbar i]
end YM.FVAAlt2.Shop
