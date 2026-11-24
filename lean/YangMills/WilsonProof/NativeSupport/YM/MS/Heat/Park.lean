import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Mutual
/-!
# Compact integration on any external space

Volumes are finite, no atlas. Include time transport $R$ interval of any sign.
 Need mixed t→ external f derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open scoped Topology ContDiff
variable {P E F : Type} [NormedAddCommGroup P][NormedSpace ℝ P] [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [MeasurableSpace P][BorelSpace P][FiniteDimensional ℝ P](μ:Measure P)

def Cour (μ:Measure P): Prop:= ∃ s:Set P, IsCompact s∧ ∀ᵐ i ∂μ,i∈s
lemma Lot [IsFiniteMeasure μ](h:Cour μ){f:P×E→ F}(hx:ContDiff ℝ ∞ f): Majorant μ (fun p x=> f (p,x)) where
   smooth:= Eventually.of_forall (fun i => (hx.comp (g:=f) (f:=fun x:E=> (i,x)) (by fun_prop)))
   borel j x:= by
       simp_rw [extDer hx]; let T:= ContinuousMultilinearMap.compContinuousLinearMapL (F:=F) (fun _:Fin j=> ContinuousLinearMap.inr ℝ P E)
       have ht : Continuous fun p=> T (iteratedFDeriv ℝ j f (p,x)) := T.continuous.comp ((hx.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast le_top)).comp (by fun_prop : Continuous (fun p:P=> (p,x))))
       exact ht.aestronglyMeasurable
   major i x:= by
       let Z (p:P×E) := ‖iteratedFDeriv ℝ i f p‖; have hZ:Continuous Z:= (hx.continuous_iteratedFDeriv (m:=i) (by exact_mod_cast le_top)).norm
       obtain ⟨s,hs,h⟩:= h; let V:=s ×ˢ ({x}:Set E); have hV : IsCompact V:= hs.prod (isCompact_singleton (x:=x))
       obtain ⟨r,hr⟩:= (hV.image hZ).bddAbove; let X:= Z ⁻¹' Set.Iio (r+1);
       have ht : V⊆ X := fun y hy=> lt_of_le_of_lt (show Z y≤r from hr (mem_image_of_mem _ hy)) (lt_add_one _)
       obtain ⟨A,B,hA,hB,h',he,hu⟩:= generalized_tube_lemma hs (isCompact_singleton (x:=x)) (hZ.isOpen_preimage _ isOpen_Iio) ht
       refine ⟨B,hB.mem_nhds (he (Set.mem_singleton x)), fun _=>r+1, integrable_const _,h.mono (fun i' hi q h=>?_ )⟩
       exact le_trans (norm_extDer hx i' q i) ( (show Z (i',q)< r+1 from hu (Set.mk_mem_prod (h' hi) h)).le) -- name wrong
-- measure implies any. ∫ F not require NormedE etc
omit [NormedSpace ℝ F] in
lemma cafe [IsFiniteMeasure μ](h:Cour μ){f:P→F}(hx:Continuous f): Integrable f μ:= by
    obtain ⟨s,hs,h⟩:= h; obtain ⟨k,hk⟩:=(hs.image hx.norm).bddAbove
    exact (integrable_const (c:=k) (μ:=μ)).mono' hx.aestronglyMeasurable (h.mono (fun i hi=> hk (Set.mem_image_of_mem (fun i=>‖f i‖) hi)))

-- interval integration
variable [CompleteSpace F]
private def slice1 : Measure ℝ:= volume.restrict (Set.Icc 0 1)
private instance sliceI : IsFiniteMeasure slice1:= ⟨by rw [slice1,Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
private lemma sliceC : Cour slice1:= ⟨Set.Icc 0 1,isCompact_Icc,ae_restrict_mem measurableSet_Icc⟩
variable {T:ℝ×E→ F}
def desk (T:ℝ×E→F)(r:ℝ×E):=∫ z:ℝ in 0..r.1,T (z,r.2)
omit [CompleteSpace F] [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma table (T:ℝ×E→ F)(x:E)(r:ℝ): desk T (r,x)= r • (∫ u,T (r*u,x) ∂slice1):= by
    unfold slice1; rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    unfold desk; simpa only [mul_zero,mul_one] using (intervalIntegral.smul_integral_comp_mul_left (fun z=> T (z,x)) (a:=0) (b:=1) r).symm
lemma park (h:ContDiff ℝ ∞ T): ContDiff ℝ ∞ (desk T):= by
    let F (x:ℝ× (ℝ×E)) := T (x.2.1*x.1,x.2.2); have he := Lot slice1 sliceC (h.comp (show ContDiff ℝ ∞ (fun x:ℝ× (ℝ×E)=> (x.2.1*x.1,x.2.2)) by fun_prop)); rw [show desk T=fun z:ℝ×E=> z.1 • (∫ r,F (r,z) ∂slice1) from funext fun x=> table T x.2 x.1]; exact contDiff_fst.smul he.contDiff
lemma hfun {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{f:ℝ→E} (hx:Continuous f) (r:ℝ): HasDerivAt (fun t:ℝ=>∫ z:ℝ in 0..t,f z) (f r) r:= intervalIntegral.integral_hasDerivAt_right (hx.intervalIntegrable ..) (hx.stronglyMeasurableAtFilter ..) hx.continuousAt -- maybe `ae_strongly`
omit [NormedSpace ℝ E] in
lemma deskD (h:Continuous T)(r:ℝ)(x:E): HasDerivAt (fun t:ℝ=> desk T (t,x)) (T (r,x)) r:= hfun (h.comp (show Continuous (fun t:ℝ=> (t,x)) by fun_prop)) r
lemma comp_iter (h:ContDiff ℝ ∞ T) (r:ℝ)(j:ℕ) : iteratedFDeriv ℝ j (fun x=> desk T (r,x))= fun x:E=> ∫ s:ℝ in 0..r, iteratedFDeriv ℝ j (fun x=> T (s,x)) x:= by
   have he := Lot slice1 sliceC (h.comp (show ContDiff ℝ ∞ (fun x:ℝ× E=> (r*x.1,x.2)) by fun_prop)); simp_rw [table]
   have he':Majorant slice1 (fun z x=>T (r*z,x)):=he
   funext x; rw [iteratedFDeriv_const_smul_apply' (he'.contDiff.contDiffAt.of_le (by exact_mod_cast le_top)), he'.identity]; exact (table (T:=fun y:ℝ×E=> iteratedFDeriv ℝ j (fun z=> T (y.1,z)) x) x r).symm -- need curry he
lemma deskD_iter (h:ContDiff ℝ ∞ T)(i:ℕ) (p:ℝ)(x:E): HasDerivAt (fun t:ℝ=> iteratedFDeriv ℝ i (fun z:E=> desk T (t,z)) x) (iteratedFDeriv ℝ i (fun z:E=> T (p,z)) x) p := by
   simp_rw [comp_iter h]; refine hfun ?_ p; simp_rw [extDer h]; exact (ContinuousMultilinearMap.compContinuousLinearMapL (F:=F) (fun _:Fin i=> ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp ((h.continuous_iteratedFDeriv (m:=i) (by exact_mod_cast le_top)).comp (show Continuous fun r:ℝ=> (r,x) by fun_prop))
end YM.MS.Heat
