import YM.OPE.Compatible.Boral.Twine
/-! # Angular replica duplication.Massive conditional rotations with IV. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Flock Lav
variable {X Y:Type}{t s:ℝ}{i:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
variable (A:Law X)
variable [NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
structure Swear (A:Law X)(S:X→ₗ[ℝ] Y)(u:Y→ₗ[ℝ] X):Prop where
     title : ∀ x:Y,S (u x)=x
     rich (v:X): S v=0 →∀ y, A.P (u y) v=0
namespace Swear
variable (S:X→ₗ[ℝ] Y)(u:Y→ₗ[ℝ] X)
noncomputable def kud : X→ₗ[ℝ] X:= LinearMap.id-u ∘ₗ S
variable (h:Swear A S u)
local notation "Q!"=> kud S u
local notation "T!"=>united A A
local notation "LT"=> LinearMap.fst ℝ X X
local notation "RT"=> LinearMap.snd ℝ X X
include h
noncomputable def ren : X×X→ₗ[ℝ] X:= Q! ∘ₗ LT+u ∘ₗ S ∘ₗ RT
omit h
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in lemma shan (p:X×X) : ren S u p=Q! p.1+u (S p.2):=rfl
abbrev spar : X×X→ₗ[ℝ] X×X:= LinearMap.prod ((u ∘ₗ S) ∘ₗ LT + Q! ∘ₗ RT) ((u ∘ₗ S) ∘ₗ RT+ Q! ∘ₗ LT)
include h
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in lemma rot (p:X): S (Q! p)=0:=by change S (p-u (S p))=_; rw [_root_.map_sub,h.title,sub_self]
omit h
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in lemma pil (x:X×X): spar S u x = (u (S x.1)+Q! x.2, u (S x.2)+ Q! x.1):=rfl
include h
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in lemma Proj (x y:X) :S (u (S x)+Q! y)=S x∧Q! (u (S x)+Q! y)=Q! y:=by
        have hv:S (u (S x)+Q! y)=S x:=by rw [_root_.map_add,h.title,rot A S u h,add_zero]
        refine ⟨hv,?_⟩; change u _+Q! y-u (S _)=_; rw [hv]; abel
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in lemma mortar (x:X×X): S (spar S u x).1=S x.1∧ ren S u (spar S u x)=x.2:=by rw [shan,pil]; refine ⟨(Proj A S u h ..).1,?_⟩; rw [show Q! _= _ from (show Q! (u (S x.1)+Q! x.2)=Q! x.2 from (Proj A S u h ..).2),show S (u (S x.2)+ Q! x.1)= S x.2 from (Proj A S u h ..).1]; exact sub_add_cancel .. -- h args?
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in lemma Involve (x:X×X): spar S u (spar S u x)=x:=by rw[pil,pil]; change (u (S (u _+Q! _))+ Q! (u _+Q! _), u (S (u _+Q! _))+ Q! (u _+Q! _))=x; rw [(Proj A S u h _ _).1,(Proj A S u h x.2 x.1).2, (Proj A S u h _ _).1,(Proj A S u h _ _).2]; apply Prod.ext (by change _+(x.1-u (S x.1))=_;abel) (by change _+(x.2-u (S x.2))=_; abel)
omit [FiniteDimensional ℝ Y] in lemma balance (x:X×X): (T!).P (spar S u x) (spar S u x)=(T!).P x x:=by
      let w(a:X):= A.P a a; have he(a b:X):w (u (S a)+Q! b)=w (u (S a))+w (Q! b):=by unfold w; rw [A.P.map_add, LinearMap.add_apply,(A.P (u _)).map_add,(A.P (Q! b)).map_add,A.turns (Q! b) (u (S a)),h.rich (Q! b) (rot A _ _ h _) _,add_zero,zero_add]
      have hp(x:X): w x=w (u (S x))+ w (Q! x):=by rw [←he]; exact congr_arg w (by change x=_+(x-u (S x)); abel)
      rw [united_shape,united_shape,pil]; change w (u (S x.1)+Q! x.2)+w (u (S x.2)+Q! x.1)=w x.1+w x.2; rw [he,he,hp x.1,hp x.2]; ring
variable [MeasurableSpace X][BorelSpace X](μ:Measure X)[μ.IsAddHaarMeasure]
local notation "M"=>quart A μ
local notation "V"=>quart (united A A) (μ.prod μ)
omit [FiniteDimensional ℝ Y] in lemma swing (f:X×X→ℝ):a_ V f = a_ V (f ∘ spar S u):=by
       unfold a_;rw [has_p,has_p]; let g:= spar S u; let f': (X×X)≃ₗ[ℝ] X×X := LinearEquiv.ofBijective _ (Involutive.bijective (f:=g) (Involve A S u h)); exact ward _ _ _ _ f' (balance A S u h) f
omit h S u in lemma prodV (p q:X→ℝ): a_ V ((p ∘ (Prod.fst (α:=X) (β:=X)))*(q ∘ (Prod.snd (α:=X) (β:=X))))=a_ M p*a_ M q:=by
       unfold a_; rw [has_p,has_p,has_p]; let P:= μ.prod μ; let D:=T!; have ht(i:X×X): (((p ∘ (Prod.fst (α:=X) (β:=X)))*(q ∘ (Prod.snd (α:=X) (β:=X))))*D.kern) i=(p i.1*A.kern i.1)*(q i.2*A.kern i.2):=by simp only [Pi.mul_apply,formed,comp_apply,D];ring
       unfold Law.average; unfold D at ht; simp_rw [ht,formed]; rw [integral_prod_mul,integral_prod_mul (fun x=>p x*A.kern x) (fun y=>q y*A.kern y)]; simp only[Pi.mul_apply]; ring -- simplification
omit [FiniteDimensional ℝ Y] in lemma sideP (f:Y→ℝ)(g:X→ℝ): a_ V (fun i:X×X=> f (S i.1) * g (ren S u i)) = a_ M (f ∘ S)* a_ M g:=by
          rw [swing A S u h μ, ← prodV]; apply congr_arg; funext i; obtain ⟨hp,hx⟩:=mortar A S u h i; simp only [Function.comp_apply,hp,hx,Pi.mul_apply]
omit [FiniteDimensional ℝ Y] in lemma aboard (f:X→ℝ): a_ V (f ∘ ren S u)=a_ M f:=by
          convert! sideP A S u h μ (fun _=>1) f using 1; · simp [a_]
          rw [show a_ M ((fun _=>1)∘S)=1 from (by change (∫ x,(1:ℝ) ∂M)=1; simp),one_mul]
end Swear
end YM.OPE.Borealis.Galea
