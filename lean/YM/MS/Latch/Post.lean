import YM.MS.Latch.Clan
/-!
# Finite-dimensional tests suffice. Exterior derivative measurability.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff
variable {ι I E F P A:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup P][NormedSpace ℝ P][FiniteDimensional ℝ P]
-- factor on the range to preserve net even on B
lemma canon (w:Wire A E P){b:Bool}(h:Course b w): ∃ (B: Type)(_i:NormedAddCommGroup B) (_n:NormedSpace ℝ B) (_a:FiniteDimensional ℝ B) (v: Wire A B P) (L:E→L[ℝ] B), (∀ x,sail w x=sail v (L x)) ∧ Course b v := by
   let L:E→L[ℝ] (Fin w.length→ P) := ContinuousLinearMap.pi fun i=>(w.get i).2; let B:=L.range; let f:E→L[ℝ] B:= L.rangeRestrict
   let v:Wire A B P:= List.ofFn (fun i:Fin w.length=> ((w.get i).1,(ContinuousLinearMap.proj i).comp B.subtypeL)); have he (x:E):sail w x=sail v (f x):= by
         unfold sail v; apply List.ext_getElem; all_goals simp [L,f,_root_.List.get_eq_getElem]
   refine ⟨ B,inferInstance,inferInstance,inferInstance,v,f,he, fun hx=>?_⟩; ext x; obtain ⟨q,hq⟩:= x.property; have hT:f q=x:= Subtype.ext hq; rw [ ← sail_net,← hT, ← he,sail_net,h hx]; rfl
omit [FiniteDimensional ℝ P] in
lemma peat (w:Wire A E P)(v: Wire A F P)(L:E→L[ℝ] F)(h:∀ x,sail w x=sail v (L x))(c:A→ℤ): fieldDim c w=fieldDim c v:= by rw [← sail_dim w (0:E),h, sail_dim] -- lint
-- transfer for any property of length etc.
lemma factorS {b:Bool}(P':ℕ→Prop) {G:Gauge}(S:Scale ι)(F:ι→Law G)(a:ι→ℝ)(h:∀ (E:Type)[NormedAddCommGroup E][ NormedSpace ℝ E][ FiniteDimensional ℝ E],∀ w: Wire ( BH G ) E QP,P' w.length→Course b w→Cape S F a w)(w:Wire ( BH G ) E QP)(he:P' w.length)(hy:Course b w): Cape S F a w:= by
   obtain ⟨B,i,n,hB,v,L,hp,hv⟩:= canon w hy; have hz:v.length=w.length:= by rw [← sail_len v (L 0), ← hp, sail_len ]
   have hm := h B v (by rwa [hz]) hv; unfold Cape Plane.Chart; simp_rw [hp]; rw [ show pitch w=pitch v from peat w v L hp wfield ]; exact Bound.linear L hm
-- meas.E
variable [FiniteDimensional ℝ E]
variable [MeasurableSpace I]{μ:Measure I}
lemma slip {F':I→ E→L[ℝ] F}(h:∀ p, AEStronglyMeasurable (fun i=> F' i p) μ): AEStronglyMeasurable F' μ:= by
   let B:= Module.finBasis ℝ E; let Y i: F→L[ℝ] E→L[ℝ] F:= ContinuousLinearMap.smulRightL ℝ E F (( B.coord i ).toContinuousLinearMap); rw [show F'=(fun x=> ∑ i:Fin (Module.finrank ℝ E), Y i (F' x ( B i )) ) from ?_]; exact Finset.aestronglyMeasurable_fun_sum _ fun i _=> (Y i).continuous.comp_aestronglyMeasurable ( h ( B i ) ); funext x; ext p; nth_rw 1 [ ← B.sum_repr p ]; simp [Y, _root_.sum_apply] ; simp_rw [← map_smul (F' x),← map_sum]; rw [ B.sum_repr ]
lemma velocity {f:I→ E→F}(hp:∀ x,AEStronglyMeasurable (fun i=>f i x) μ)(ht:∀ᵐ i∂μ,ContDiff ℝ ∞ (f i))(j:ℕ)(p:E): AEStronglyMeasurable (fun i=> iteratedFDeriv ℝ j (f i) p ) μ:= by
    induction j generalizing F f with -- IH.F implicit? choose general p
    | zero=> exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp_aestronglyMeasurable ( hp p )
    | succ j ih=>
         let g i := fderiv ℝ ( f i ); rw [show (fun i=>iteratedFDeriv ℝ (j+1) (f i) p )= _ from funext fun i=>iteratedFDeriv_succ_eq_comp_right] -- name
         refine (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.continuous|>.comp_aestronglyMeasurable (ih ( f:=g ) ?_ (ht.mono fun i hi=> (contDiff_infty_iff_fderiv.mp hi).2 )); intro p; refine slip (fun v=>?_); refine aestronglyMeasurable_of_tendsto_ae ( f:=fun (u:ℝ) i=> u⁻¹ • (f i (p+u • v)-f i p)) (𝓝[≠] 0 ) (fun _=> ((hp _).sub (hp _)).const_smul _) ( ht.mono fun i hi=> ?_ ); have hz : HasDerivAt (fun u:ℝ=> f i (p+u • v)) (g i p v) 0:= by convert! (hi.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (0:ℝ) (( hasDerivAt_id' (0:ℝ) |>.smul_const v).const_add p) using 1; simp; rfl
         simpa using! hz.tendsto_slope_zero
end YM.MS.Latch
