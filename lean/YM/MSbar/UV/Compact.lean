import YM.MSbar.UV.Uniform
/-! Compact scale and shell integrals, including the estimates needed on derivatives along all
 linear plots. Doesn't assume regulator independence. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.High
open Function Filter Set Metric Asymptotics MeasureTheory YM.Planned.AtomRegular
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {ι X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
  [NormedAddCommGroup Z][NormedSpace ℝ Z]
variable {x:X}{y:Y} {U: Set Y}{B:Book ι} {P:Damping ι}{n m:ℕ} {f : X × Y → Z}
-- partial Taylor map
noncomputable abbrev leaf (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] := ContinuousLinearMap.inl ℝ X Y
def half (n:ℕ)(f:X×Y→Z) (a:X×Y):= iteratedFDeriv ℝ n (fun x=> f (x,a.2)) a.1
lemma leaf_map (h:ContDiff ℝ ∞ f)(v:X × Y) : half n f v= (iteratedFDeriv ℝ n f v).compContinuousLinearMap (fun _=>leaf X Y):=by
    let g(w:X×Y):=f (w+(0,v.2)); let L:=leaf X Y; have he:(fun x=> f (x,v.2))=g ∘ L:=by ext; simp [g,L,leaf]
    have hG:ContDiff ℝ ∞ g:=h.comp (contDiff_id.add contDiff_const)
    rw [half,he, L.iteratedFDeriv_comp_right hG v.1 (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right _ (0,v.2)]; simp [L,leaf]
lemma leaf_cost (h:ContDiff ℝ ∞ f)(v:X × Y): ‖half n f v‖ ≤ ‖iteratedFDeriv ℝ n f v‖*‖leaf X Y‖^n:=by rw [leaf_map h]; simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ n f v) (fun _=>leaf X Y)
lemma leaf_cont (h:ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (half n f):=by
    rw [funext (leaf_map (n:=n) h)]
    let T:= ContinuousMultilinearMap.compContinuousLinearMapL (F:=Z) (fun _:Fin n=> leaf X Y)
    exact T.contDiff.comp (h.iteratedFDeriv_right (by exact_mod_cast (show (⊤:ℕ∞)+↑n ≤ (⊤:ℕ∞) from le_top)))
variable [FiniteDimensional ℝ X][MeasurableSpace Y][BorelSpace Y] {μ: Measure Y} [IsLocallyFiniteMeasure μ]
lemma veil (h:ContDiff ℝ ∞ f)(hx:IsCompact U): Covered (μ.restrict U) (fun y x=> f (x,y)) n x:= by
    let s:=closedBall x 1; have he:= (isCompact_closedBall x 1).prod hx
    choose F hF using fun i:Fin (n+1)=> he.exists_bound_of_continuousOn ((leaf_cont (n:=(i.val)) h).continuous.continuousOn)
    let R:= ∑ i:Fin (n+1), |F i|
    letI : IsFiniteMeasure (μ.restrict U) := ⟨by simp [hx.measure_lt_top]⟩
    refine ⟨ball x 1,isOpen_ball,mem_ball_self (by linarith), (fun _=>R), ⟨Eventually.of_forall (fun t _ _=>by apply ContDiff.contDiffAt; exact (h.of_le (by exact_mod_cast le_top)).comp (contDiff_id.prodMk contDiff_const)),?_,integrable_const _,?_⟩⟩
    · intro k hk v hv; exact ((leaf_cont (n:=k) h).continuous.comp ((continuous_const (y:=v)).prodMk continuous_id)).continuousOn.aestronglyMeasurable_of_isCompact hx hx.measurableSet
    filter_upwards [ae_restrict_mem hx.measurableSet] with y hy b hb i hi; let z:Fin (n+1):=⟨i,by omega⟩; exact (hF z (b,y) ⟨ball_subset_closedBall hb,hy⟩).trans ((le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (F j)) (Finset.mem_univ z)))
abbrev sectionL (f:X × Y→ Z) (U:Set Y) (μ:Measure Y) (x:X):=∫ y in U, f (x,y)∂μ
lemma section_smooth (h:ContDiff ℝ ∞ f)(hx:IsCompact U): ContDiff ℝ ∞ (sectionL f U μ):=by
    refine contDiff_infty.mpr fun n=> contDiff_iff_contDiffAt.mpr fun x=> ?_; exact (veil (μ:=μ) (n:=n) (x:=x) h hx).leaves EventuallyEq.rfl
lemma under_leaf [CompleteSpace Z] (h:ContDiff ℝ ∞ f)(hx:IsCompact U): iteratedFDeriv ℝ n (sectionL f U μ) x = ∫ y in U, half n f (x,y)∂μ :=by obtain ⟨s,hS,hs,b,H⟩:=veil (μ:=μ) (n:=n) (x:=x) h hx; exact H.differentiate hS hs
-- stamp compact estimates
lemma Stamp.average {u:ι→X×Y→Z}[CompleteSpace Z] (h:Stamp B P u)(hv:IsCompact U): Stamp B P (fun i=> sectionL (u i) U μ):=by
    refine ⟨fun i hi => section_smooth (h.qualify i hi) hv,fun n=>?_⟩; obtain ⟨c,r,hc,H⟩:=h.known n
    obtain ⟨D,hD⟩:= hv.exists_bound_of_continuousOn (f:=id) continuous_id.continuousOn; replace hD (u:Y)(hu:u∈U): ‖u‖ ≤ |D|:= (hD u hu).trans (le_abs_self D)
    refine ⟨μ.real U*((1+|D|)^r*(c*‖leaf X Y‖^n)), r,by positivity,fun i hi x=>?_⟩; dsimp only; rw [under_leaf (h.qualify i hi) hv]; let A:= |D|; let E:= c*(1+A)^r * ‖leaf X Y‖^n
    calc
        _ ≤ ∫ (y:Y) in U, price B P E r i x ∂μ := by
            refine norm_integral_le_of_norm_le (integrableOn_const hv.measure_lt_top.ne) ?_
            filter_upwards [ae_restrict_mem hv.measurableSet] with y hy; apply (leaf_cost (h.qualify i hi) (x,y) (n:=n)).trans; apply le_trans (mul_le_mul_of_nonneg_right (H i hi (x,y)) (by positivity)); unfold E A price Credit; rw [Prod.norm_def]; have hx:max ‖x‖ ‖y‖≤ ‖x‖+|D|:= max_le (by linarith [abs_nonneg D]) ((hD _ hy).trans (by linarith [norm_nonneg x])); have hb:= B.right i
            calc
             _ ≤ _ := show _ ≤ Real.exp (P i)*c*(B.fee i*((1+|D|)*(1+‖x‖)))^r*‖leaf X Y‖^n from by gcongr; nlinarith [mul_nonneg (abs_nonneg D) (norm_nonneg x)]
             _ = _ := by simp only [mul_pow]; ring
        _ = _ := by simp only [setIntegral_const, smul_eq_mul]; unfold price E A; ring
end YM.MSbar.High
