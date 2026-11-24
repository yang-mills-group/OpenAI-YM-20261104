import YM.RG11Proof.Neighborhood.Features
/-!
# Exterior sensor at fixed geometry detects every complex output row

No requirement to diagonalize near/far pairs across grades/horizons, just
full rank on the whole fixed through-H basis (release leading reflected
positivity). Choose y=c-basis0 so legal for every H including 0 & arbitrary
simple compact G (indeed fullness may require less). Coefficient error costs
may depend on H! This is exact rank, no positivity uniform statement in frames.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Neighborhood
open scoped Classical BigOperators ContDiff Topology
open Set Function Filter Labels Maxwell MeasureTheory
open PowerSeries YM.RG11.Fields YM.RG11.Grove YM.RG11.Stress YM.RG11.Jets YM.RG11.Nodes Pert.Position Extra.FD
variable {G:Gauge}{F:Frames G}

-- E singleton exterior label reindex to enable free_unique

def shore (A:ShapeReport G F)(d:ℕ)(y:Tail 1):Square (lab F d) (PowerSeries ℂ):=Matrix.of fun i j=>backRow A d d y i (fun _=>j)

def oppositePoint (c y:E4)(hc:c≠y): Tail 1:= ⟨c,points fun _:Fin 1=>y, Work.A01.conf_cons (fun _ _ _=>Subsingleton.elim ..) (fun _=>hc)⟩

private theorem shines (A:ShapeReport G F)(d:ℕ)(c y:E4)(hc:c≠y)(i j): constantCoeff (shore A d (oppositePoint c y hc) i j)=
    visible F d (Extra.FD.couple c y) ![(tower F d).b i,(tower F d).b j]:=by
   have H(v:Fin 2→ (tower F d).toBasis.J)(x:Points 2)(hx:x∈conf 2):constantCoeff (survey A (tower F d).toBasis (here x) v) = visible F d x ((tower F d).b ∘ v):=by
     -- survey_integrated any smooth, survey_zero4 only 4
     rw [←coeff_zero_eq_constantCoeff_apply]
     apply (survey_integrated A (tower F d).toBasis v 0 (here x)
       (K:=fun y=>visible F d y ((tower F d).b ∘ v)) (show ContDiffOn ℝ ∞ _ _ from (freeTable F).class_smooth _ (table_smooth F) (fun i=>⟨d,((tower F d).b ∘ v) i⟩)) (fun f=> by rw [A.maxwell]; rfl)).trans (here_at x hx _ _)
   have hu:close (oppositePoint c y hc)=(Extra.FD.couple c y):=by
      apply PiLp.ext; intro i; fin_cases i <;> rfl
   unfold shore backRow rear; rw [Matrix.of_apply, Matrix.submatrix_apply, hu, link_tray A d _ (hi:=le_rfl) (he:=le_rfl)]
   unfold tray; rw [rises_self,H _ _ (Extra.FD.couple_ok hc)]; congr 1; funext i; fin_cases i <;> rfl

private def columns {I:Type*}[Fintype I] (D:Square I ℂ) : (I→ℂ)→ₗ[ℂ] (I→ℂ) where
   toFun x i:= fires D x i
   map_add':=by intro x y; funext i; simp [fires,add_mul,Finset.sum_add_distrib]
   map_smul':=by intro c x; funext i; simp [fires,mul_assoc,←Finset.mul_sum]

private theorem listens_left {I:Type*}[Fintype I][DecidableEq I](D:Square I ℂ)(h:Function.Injective (columns D)):
    ∃ W:Square I ℂ,D * W=1:=by
   obtain ⟨f,hf⟩:=LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.mpr h)
   refine ⟨Matrix.of (fun i j=> f (Pi.single i (1:ℂ)) j),?_⟩
   ext i j
   rw [Matrix.mul_apply]; simp only [Matrix.of_apply]
   have he : columns D (Pi.single i 1)=(D i):=by
       unfold columns; ext1 l; change ∑ z,(Pi.single i (1:ℂ):I→ℂ) z * D z l = D i l; simp [Pi.single_apply,ite_mul]
   have hu:=LinearMap.congr_fun hf (Pi.single i (1:ℂ))
   rw [LinearMap.comp_apply,he] at hu
   apply Eq.trans _ (b:=f (D i) j)
   · rw [hu,Matrix.one_apply]; simp [Pi.single_apply,eq_comm]
   conv_rhs=> rw [← Module.Basis.sum_repr (Pi.basisFun ℂ I) (D i)]
   rw [map_sum]; simp only [Finset.sum_apply,map_smul, Pi.smul_apply,Pi.basisFun_apply,Pi.basisFun_repr,smul_eq_mul]

open YM.Pert.Scale
private theorem noGap {V I:Type*}[AddCommGroup V][Module ℂ V][Fintype I]
    (B:Module.Basis I ℂ V)(L:MultilinearMap ℂ (fun _:Fin 2=>V) ℂ)(h:∀ v,v≠0 → ∃ b,L ![v,b] ≠ 0)
    (D:Square I ℂ)(he:∀ i j,D i j=L ![B i,B j]):Injective (columns D):=by
   apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr
   intro x hx; let z:=B.equivFun.symm x
   suffices z=(0:V) by rw [←B.equivFun.apply_symm_apply x]; change B.equivFun z=_; rw [this,map_zero]
   by_contra hi; obtain ⟨v,hv⟩:=h z hi; apply hv
   let p:= L.toLinearMap ![z,(0:V)] 1
   have hp (t:V):p t = L ![z,t]:=by rw [show p= L.toLinearMap ![z,(0:V)] 1 from rfl, MultilinearMap.toLinearMap_apply]; apply congrArg L; ext1 j; fin_cases j <;> simp
   rw [←hp,← B.sum_repr v,map_sum]
   apply Finset.sum_eq_zero; intro i _; rw [map_smul,hp];
   suffices L ![z,B i]=0 by rw [this,smul_zero]
   unfold z; rw [Module.Basis.equivFun_symm_apply]
   change L.curryLeft (∑ i,x i • B i) ![B i]= _
   rw [map_sum,_root_.sum_apply]; simp_rw [map_smul,_root_.smul_apply, smul_eq_mul]
   have heq(j:I): (L.curryLeft (B j)) ![B i] = L ![B j,B i]:=rfl
   simp_rw [heq,←he]; exact congrFun hx i

-- convert D at fixed positions. `Ward.disc` def using tags but full correlation same.
private theorem hears {d:ℕ}(x y:E4)(hc:x≠y)(v:E F d)(h:v≠0):∃ t:E F d, visible F d (Extra.FD.couple x y) ![v,t]≠0:=by
    obtain ⟨t,ht⟩:=fullness F hc v h
    exact ⟨t,ht⟩

 theorem light (A:ShapeReport G F)(d:ℕ)(c y:E4)(hc:c≠y):∃ W:Square (lab F d) ℂ, (shore A d (oppositePoint c y hc)).map constantCoeff * W=1:=
   listens_left _ (noGap (tower F d).b (visible F d (Extra.FD.couple c y)) (hears c y hc) _ (shines A d c y hc))
end YM.RG11.Neighborhood
