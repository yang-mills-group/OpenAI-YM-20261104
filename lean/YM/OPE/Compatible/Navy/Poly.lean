import YM.OPE.Compatible.Melon.Ritzy
/-!
# Compound axes. Index decompositions give exact Born products
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J U K:Type}[Fintype I][Fintype J][Fintype U]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric
attribute [local instance] Gauge.frobInner
variable (p: U ≃ I ⊕ J)
-- transports independent of product measure
def lead (p: U≃I ⊕ J)(x:I):U:=p.symm (.inl x)
def secondC (p:U≃ I ⊕ J)(x:J):U:=p.symm (.inr x)
abbrev prL (G:Gauge): Keys G U→L[ℝ] Keys G I:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (lead p i)
abbrev prR (G:Gauge): Keys G U→L[ℝ] Keys G J:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (secondC p i)
def crewE (p:U≃ I ⊕ J)(K:Type): (U→K)≃ ((I→K)× (J→K)) where
   toFun v :=(fun i=> v (lead p i),fun j=> v (secondC p j))
   invFun y:= fun x=>(p x).elim y.1 y.2
   left_inv v:=by
       funext i; change (p i).elim _ _= _; cases ht:p i
       next h=> exact congr_arg v (p.apply_eq_iff_eq_symm_apply.mp ht).symm
       next h=> exact congr_arg v (p.apply_eq_iff_eq_symm_apply.mp ht).symm
   right_inv:= by rintro ⟨i,j⟩; dsimp only [lead,secondC];simp
protected def drinks (G:Gauge): Keys G U ≃L[ℝ] (Keys G I × Keys G J) := LinearEquiv.toContinuousLinearEquiv ({
      crewE p G.Color with map_add':= by intro x y;rfl,
                            map_smul':=fun c u=>rfl } : Keys G U≃ₗ[ℝ](Keys G I × Keys G J))
omit [Fintype I] [Fintype J] in
lemma beer (x:Keys G U): Pilot.drinks p G x = (prL p G x,prR p G x):=rfl
noncomputable def shoot (p:U≃ I⊕J)(K:Type)[TopologicalSpace K]:(U→K) ≃ₜ ((I→K)×(J→K)):= {crewE p K with
   continuous_toFun :=(continuous_pi fun _=> continuous_apply _).prodMk (continuous_pi fun _=>continuous_apply _)
   continuous_invFun:=by apply continuous_pi; intro i; change Continuous (fun x:(I→K)×(J→K)=> (p i).elim x.1 x.2); cases h:p i
                         · exact (continuous_apply _).comp continuous_fst
                         exact (continuous_apply _).comp continuous_snd }
lemma brewing (G:Gauge) : MeasurePreserving (shoot p G.El).symm ((Gem G I).prod (Gem G J)) (Gem G U):=by
      let X:=shoot p G.El; refine ⟨X.symm.measurable,Eq.symm ?_⟩; apply Measure.pi_eq; intro s hs; rw [Measure.map_apply X.symm.measurable (MeasurableSet.univ_pi hs)]; have he : X.symm ⁻¹' Set.univ.pi s = Set.univ.pi (s ∘ lead p) ×ˢ Set.univ.pi (s ∘ Pilot.secondC p):=by -- precedence
          ext ⟨x,y⟩; simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_prod]; constructor
          · intro H; constructor
            · intro i; have h(p':U): (p p').elim x y∈s p':= H _; simpa [lead,Function.comp_apply] using h (lead p i)
            intro i; have h(p':U): (p p').elim x y∈s p':=H _; simpa [Pilot.secondC,Function.comp_apply] using h (Pilot.secondC p i)
          rintro ⟨h1,h2⟩ i; change (p i).elim x y ∈ _; cases ht:p i with
          | inl k=> rw [show i=lead p k from p.apply_eq_iff_eq_symm_apply.mp ht]; exact h1 _
          | inr k=> rw [show i=Pilot.secondC p k from p.apply_eq_iff_eq_symm_apply.mp ht]; exact h2 _
      rw [he,Measure.prod_prod,Measure.pi_pi,Measure.pi_pi,← Equiv.prod_comp p.symm _]; rw [Fintype.prod_sum_type];rfl
lemma jacSplit (X:Keys G U)(R:ChartRatio G): Chart.jacobian R X=Chart.jacobian R (prL p G X)*Chart.jacobian R (prR p G X):=by unfold Chart.jacobian; rw [← Equiv.prod_comp p.symm, Fintype.prod_sum_type];rfl
end YM.OPE.Cascade.Pilot
