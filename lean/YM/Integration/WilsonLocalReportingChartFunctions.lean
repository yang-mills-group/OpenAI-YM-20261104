import YM.Integration.WilsonLocalPlaquetteRegularity

/-! Measurability of the full fitted weights jointly in sampled exterior
links and the original finite tangent coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingChartFunctions
open Function Set Finset MeasureTheory Lattice Wilson RG Tree RG16 Precision PertExtension
open WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction WilsonLocalPlaquetteForest
open WilsonLocalPlaquetteField WilsonLocalPlaquetteAction WilsonLocalConditionalResidue
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f} {M:Type} [MeasurableSpace M]

theorem background_m (T:Forest S.ratio) (B:Finset T.Free)
    {v:M→({i:T.Free|i∉moving T B}:Set T.Free)→G.El} (hv:Measurable v) :
    Measurable (fun z=>background T B (v z)) := by
  apply measurable_pi_lambda;intro i
  by_cases hi:internal T i.val
  · simpa only [background,dif_pos hi] using (measurable_const (a:=(1:G.El)))
  · simpa only [background,dif_neg hi,Function.comp_def] using (measurable_pi_apply ⟨WilsonReportingForestPivots.pivot T i.val,saved T B i.val hi⟩).comp hv

theorem filled_m (T:Forest S.ratio) (E:Finset T.Free) {v:M→({i:T.Free|i∉E}:Set T.Free)→G.El}
    {q:M→↥E→G.El} (hv:Measurable v) (hq:Measurable q) : Measurable (fun z=>filled T E (v z) (q z)) :=
  T.continuous_drape.measurable.comp ((cut T E).symm.measurable.comp (hq.prodMk hv))

theorem position_m (T:Forest S.ratio) (B:Finset T.Free) {v:M→({i:T.Free|i∉moving T B}:Set T.Free)→G.El}
    {x:M→↥(moving T B)→G.Color} (hv:Measurable v) (hx:Measurable x) (g:ℝ) :
    Measurable (fun z=>WilsonLocalConditionalResidue.position T B (v z) g (x z)) := by
  apply filled_m T (moving T B) hv
  apply Measurable.mul _ (background_m T B hv)
  exact Chart.expLinks_meas.comp ((continuous_const_smul g).measurable.comp hx)

theorem extend_m {α:Type} [MeasurableSpace α] (T:Forest S.ratio) (E:Finset T.Free)
    {w:M→↥E→α} (hw:Measurable w) (a:α) : Measurable (fun z=>extend T E (w z) a) := by
  apply measurable_pi_lambda;intro i
  by_cases h:i∈T.trunks
  · simpa only [WilsonLocalPlaquetteForest.extend,dif_pos h] using (measurable_const (a:=a))
  · by_cases he:(⟨i,h⟩:T.Free)∈E
    · simpa only [WilsonLocalPlaquetteForest.extend,dif_neg h,dif_pos he,Function.comp_def] using (measurable_pi_apply ⟨⟨i,h⟩,he⟩).comp hw
    · simpa only [WilsonLocalPlaquetteForest.extend,dif_neg h,dif_neg he] using (measurable_const (a:=a))

theorem left_m (S':Finset (Bonds f)) (q:Face (Per f)) {Q L:M → Config G f}
    (hq:Measurable Q) (hl:Measurable L) : Measurable (fun z=>fun i:Fin 4=>
      if WilsonPlaquetteIncidence.edges q i∈S' then L z (WilsonPlaquetteIncidence.edges q i)
      else Q z (WilsonPlaquetteIncidence.edges q i)) := by
  apply measurable_pi_lambda;intro i
  by_cases h:WilsonPlaquetteIncidence.edges q i∈S'
  · simp only [if_pos h];exact (measurable_pi_apply _).comp hl
  · simp only [if_neg h];exact (measurable_pi_apply _).comp hq

theorem right_m (S':Finset (Bonds f)) (q:Face (Per f)) {R:M → Config G f}
    (hr:Measurable R) : Measurable (fun z=>fun i:Fin 4=>
      if WilsonPlaquetteIncidence.edges q i∈S' then R z (WilsonPlaquetteIncidence.edges q i) else 1) := by
  apply measurable_pi_lambda;intro i
  by_cases h:WilsonPlaquetteIncidence.edges q i∈S'
  · simp only [if_pos h];exact (measurable_pi_apply _).comp hr
  · simp only [if_neg h];exact measurable_const

theorem angles_m (S':Finset (Bonds f)) (q:Face (Per f)) {Z:M → Angular G f} (hz:Measurable Z) :
    Measurable (fun z=>angles S' (Z z) q) := by
  apply measurable_pi_lambda;intro i;by_cases h:WilsonPlaquetteIncidence.edges q i∈S'
  · simp only [angles,if_pos h];exact (measurable_pi_apply _).comp hz
  · simp only [angles,if_neg h];exact measurable_const

theorem single_m (S':Finset (Bonds f)) (q:Face (Per f)) (p:ℕ) (g:ℝ) {Q L R:M → Config G f} {X:M → Angular G f}
    (hq:Measurable Q) (hl:Measurable L) (hr:Measurable R) (hx:Measurable X) :
    Measurable (fun z=>polynomial p (WilsonLocalPlaquetteField.pivot S' (Q z) (L z) (R z) q) (angles S' (X z) q) g) := by
  let bb : M → WilsonLocalPlaquetteTaylor.Pivots G := fun z=>WilsonLocalPlaquetteField.pivot S' (Q z) (L z) (R z) q
  let aa : M → WilsonLocalPlaquetteTaylor.Angles G := fun z=>angles S' (X z) q
  have pv : Measurable bb := by
    unfold bb WilsonLocalPlaquetteField.pivot
    apply Measurable.prodMk
    · exact left_m S' q hq hl
    · exact right_m S' q hr
  have av : Measurable aa := angles_m S' q hx
  let out:=fun a : WilsonLocalPlaquetteTaylor.Pivots G × WilsonLocalPlaquetteTaylor.Angles G=>polynomial p a.1 a.2 g
  change Measurable (out ∘ fun z=>(bb z,aa z))
  have h : Measurable out := (WilsonLocalPlaquetteRegularity.action (G:=G) p g).measurable
  exact Measurable.comp h (pv.prodMk av)

theorem booked_m (S':Finset (Bonds f)) (p:ℕ) (g:ℝ) {Q L R:M → Config G f} {X Y:M → Angular G f}
    (hq:Measurable Q) (hl:Measurable L) (hr:Measurable R) (hx:Measurable X) (hy:Measurable Y) :
    Measurable (fun z=>booked p S' (Q z) (L z) (R z) (X z) (Y z) g) := by
  unfold booked;apply Finset.measurable_sum;intro q _
  exact (single_m S' q p g hq hl hr hx).sub (single_m S' q p g hq hl hr hy)

theorem score_m (P:ChartRatio G) (p:ℕ) (β g:ℝ) (T:Forest S.ratio) (B:Finset T.Free)
    {v:M→({i:T.Free|i∉moving T B}:Set T.Free)→G.El} {x y:M→↥(moving T B)→G.Color}
    (hv:Measurable v) (hx:Measurable x) (hy:Measurable y) : Measurable (fun z=>score P p β g T B (v z) (x z) (y z)) := by
  let E:=moving T B
  have hw:=background_m T B hv
  apply Measurable.sub
  · apply Finset.measurable_sum;intro i _
    have h:=(WilsonLocalPlaquetteRegularity.haar P p g).measurable
    exact (h.comp ((measurable_pi_apply i).comp hx)).sub (h.comp ((measurable_pi_apply i).comp hy))
  · exact measurable_const.mul (booked_m (support T E) (p+2) g (filled_m T E hv hw) measurable_const
      (extend_m T E hw 1) (extend_m T E hx 0) (extend_m T E hy 0))

end YM.Integration.WilsonLocalReportingChartFunctions
