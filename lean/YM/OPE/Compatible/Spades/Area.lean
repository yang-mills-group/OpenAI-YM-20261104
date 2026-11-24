import YM.OPE.Compatible.Spades.Cred
/-!
# Unrestricted Gaussian marginals. Positive Def matrix even empty stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X] [NormedSpace ℝ X]
variable {I J:Type}{i j k r:ℕ}
section
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ X][FiniteDimensional ℝ F](P:Law E)(A:Law F)(S:E→ₗ[ℝ] X)(hx:Surjective S)
lemma law_eq (Q:Law E)(h:∀ i j:Dual' E,P.wick i j=Q.wick i j):P=Q:=by
       have he(i):P.inverse i=Q.inverse i:= (SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)).2 (fun q=>h i q.toLinearMap)
       have hp:P.P=Q.P:= LinearMap.ext fun i=> (Q.applies (P.P i)).symm.trans (by rw[← he,P.solves]); cases P; cases Q; congr
local notation "U"=> LinearMap.ker S
noncomputable abbrev Budge (P:Law E)(T: Submodule ℝ E):Law T:=by
       let S:((T:Type) →ₗ[ℝ] E):=T.subtype; exact Libra.giraffe ((S.dualMap ∘ₗ P.P) ∘ₗ S) (fun _ _=> P.turns ..) (fun x h=> keptZ P x.val (fun hh=> h (Subtype.ext hh)))
noncomputable def bulwark : (X×(U)) ≃ₗ[ℝ] E:=by
       let f:= claspR P S hx; let g:X×(U)→ₗ[ℝ] E:= (f ∘ₗ LinearMap.fst ..) + ((U).subtype ∘ₗ LinearMap.snd ..); exact {g with
           invFun:= fun e=>(S e,⟨e-f (S e), show S _=0 from by rw [map_sub,drapeB P S hx (S e),sub_self]⟩)
           right_inv:= fun e=> show f (S e)+(e-f (S e))=e from add_sub_cancel ..
           left_inv:= fun z=> by have hp:S (g z)=z.1:=by change S (f z.1+ z.2.val)= _; rw [map_add, drapeB P S hx z.1, show S z.2.val=0 from z.2.property,add_zero]
                                 exact Prod.ext hp (Subtype.ext (show g z-f (S (g z))=z.2.val from by rw[hp]; exact add_sub_cancel_left .. )) }
lemma pullW (v:X×(U)): S (bulwark P S hx v)=v.1:=by
       change S (claspR P S hx v.1 + v.2.val)=_; rw [map_add,drapeB,show S v.2.val=0 from v.2.property,add_zero]
lemma transitA (x:X×(U)): P.P (bulwark P S hx x) (bulwark P S hx x) = (united (chiselR P S hx) (Budge P (LinearMap.ker S))).P x x:=by
       let v:= claspR P S hx x.1; change P.P (v+x.2.val) (v+x.2.val)= _; have he:S (v+x.2.val)=x.1:=pullW P S hx x; rw [P.P.map_add,LinearMap.add_apply,show P.P v _=_ from Chwist P S hx x.1 _,P.turns x.2.val,P.P.map_add,LinearMap.add_apply,show P.P v _=_ from Chwist P S hx x.1 _,he,show S x.2.val=0 from x.2.property,map_zero,zero_add];rfl
-- no hypotheses p required
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
variable [MeasurableSpace F][BorelSpace F](ν:Measure F)[ν.IsAddHaarMeasure]
lemma spent (G:Law E): 0 < ∫ e, G.kern e ∂μ:=by
       apply integral_exp_pos; simpa only [one_mul] using! lumpZ μ G (1:E→ℝ) (Bond.keep 1)
open Measure
lemma ward (g:F≃ₗ[ℝ] E) (h:∀ v, P.P (g v) (g v)=A.P v v)(f:E→ℝ):P.average μ f=A.average ν (f ∘ g):=by
       let L:=g.toContinuousLinearEquiv; let p:=ν.map L; let B:= Measure.addHaarScalarFactor p μ
       have hp:p=(B:ℝ≥0∞) • μ:=isAddLeftInvariant_eq_smul p μ; have he: 0<B:=addHaarScalarFactor_pos_of_isAddHaarMeasure p μ; let C:ℝ:= B; have hc: C≠0:= by unfold C; exact_mod_cast he.ne'
       have hv(k:E→ℝ): ∫ v:F,k (L v) ∂ν=C * ∫ v:E,k v ∂μ:=by
             rw [← (show MeasurableEmbedding (L) from L.toHomeomorph.toMeasurableEquiv.measurableEmbedding).integral_map (μ:=ν) k]
             change ∫ v,k v ∂p=_; rw [hp, integral_smul_measure];rfl -- coe
       have ht :∀ v:F, A.kern v=P.kern (L v):=fun v=> congr_arg Real.exp (congr_arg (fun x:ℝ=>-x/2) (h v).symm)
       unfold Law.average; rw [show (∫ x,(f ∘ g * A.kern) x ∂ν)= C * ∫ x, (f*P.kern) x ∂μ from by simp only [Pi.mul_apply,ht]; exact hv (f*P.kern),show (∫ x,A.kern x ∂ν)= _ from by simp_rw[ht]; exact hv P.kern,mul_div_mul_left]; exact hc
omit [BorelSpace E] in
lemma zonal (p:E→ℝ): (united P A).average (μ.prod ν) (p ∘ Prod.fst) = P.average μ p:=by
       have he(k:E→ℝ): ∫ x:E×F,k x.1*A.kern x.2 ∂μ.prod ν = (∫ x,k x ∂μ)*(∫ x,A.kern x ∂ν):= integral_prod_mul ..
       unfold Law.average; simp only [formed,Pi.mul_apply,comp_apply]; simp_rw [← mul_assoc]; rw [he (fun x=>p x*P.kern x),he P.kern]; rw [mul_div_mul_right]; exact (spent ν A).ne'
variable [MeasurableSpace X][BorelSpace X](η:Measure X)[η.IsAddHaarMeasure]
lemma through (p:X→ℝ): P.average μ (p ∘ S)= (chiselR P S hx).average η p:=by
       let T:= Budge P (LinearMap.ker S); let L:= Measure.addHaar (G:=LinearMap.ker S); rw [ward P (united (chiselR P S hx) T) μ (η.prod L) (bulwark P S hx) (transitA P S hx) (p ∘ S)]; rw [show (p ∘ S) ∘ (bulwark P S hx)=p ∘ Prod.fst from funext fun i=> congrArg p (pullW P S hx i)]; exact (zonal _ _ η L p) -- comp rw
omit [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X] in
lemma margin (T:F→ₗ[ℝ] X)(h:∀ p q:Dual' X,P.wick (p.comp S) (q.comp S)=A.wick (p.comp T) (q.comp T)) (f:X→ℝ):P.average μ (f ∘ S)=A.average ν (f ∘ T):=by
       let M:= LinearMap.range S; have he: LinearMap.range T=M:=(Plum P S T A h).symm; let L:= S.rangeRestrict; let D:= LinearMap.codRestrict M T (fun c=>he ▸ ⟨c,rfl⟩); let B:= LinearMap.range T; have hL:Surjective L:= S.surjective_rangeRestrict; have hV: Surjective D:= fun i=>by
           have hi:i.val∈B:= Eq.mp (congrArg (fun s : Submodule ℝ X=> i.val∈s) he.symm) i.property; obtain ⟨k,hk⟩:=hi; exact ⟨k,Subtype.ext hk⟩
       let p:M→ℝ:=fun x=>f x.val; letI: MeasurableSpace M:=borel _; letI: BorelSpace M:= ⟨rfl⟩; change P.average μ (p ∘ L)=A.average ν (p ∘ D); rw [through P L hL μ Measure.addHaar p,through A D hV ν Measure.addHaar p]; congr 1; apply law_eq; intro i j
       rw [tunesB, tunesB]; have hv (i:Dual' M):∃ q:Dual' X,i=q ∘ₗ M.subtype:= ?_
       · obtain ⟨c,rfl⟩:=hv i; obtain ⟨d,rfl⟩:=hv j; exact h c d
       let S:= M.subtype; obtain ⟨g,hg⟩:=S.exists_leftInverse_of_injective M.ker_subtype; exact ⟨i ∘ₗ g,by rw [LinearMap.comp_assoc,hg,LinearMap.comp_id]⟩
end
end YM.OPE.Jargon
