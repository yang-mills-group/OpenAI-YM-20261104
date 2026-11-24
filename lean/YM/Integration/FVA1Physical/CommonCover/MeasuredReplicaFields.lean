import YM.Integration.FVA1Physical.CommonCover.DistinctReplicaFields
import YM.Integration.FVA1Physical.CommonCover.MeasuredInheritedWilson
import YM.Push.BETA_TRANSPORT.Block

/-! On the selected trajectory use the entire original Haar forest, positive
receiving vacuum, actual mixed inputs and independently supplied Wilson
input. All original incoming mixed modes are charged against their true
vacuum. The Wilson vacuum receives its own integral normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure OriginalMixedWilson
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I} {G : Gauge}

theorem measured_replica_fields (H : History G) (sel : H.Selected) {N n j : ℕ} (step : j<N)
    {O : ChartRatio G} (K : @Bulk.Kernel G (H.S.side j n) (H.S.side (j+1) n) (H.levels.clock.op j n)
      (H.rep N n (j+1)).clip (H.rep N n (j+1)).path O)
    (F : Forest (H.levels.clock.op j n).ratio) (W : Bulk.Colors R G (H.S.side (j+1) n))
    (D : Lit R (Config G (H.S.side (j+1) n))) (floor : Floor (H.rep N n (j+1)) D) (well : Bulk.Well W)
    (w : I → ℝ) (wp : ∀i,0<w i) (V : Config G (H.S.side j n)) :
    let P:=H.rep N n (j+1)
    let g:=measuredCoupling (H.β N n (j+1))
    let dz:=fun y:F.Slice G=>(H.levels.clock.op j n).density P.beta (F.drape y) V
    let a:=fun y:F.Slice G=>P.eval (F.drape y)
    let b:=fun y:F.Slice G=>weight g (levelScalar P) (F.drape y) W P.clip P.path
    let trueW:=fun y=>dz y*a y
    let refW:=fun y=>dz y*b y
    let r:=fun y=>Real.log (a y)-Real.log (b y)
    let X:=fun (s:R.Mode) (y:F.Slice G)=>(unitScale (D (F.drape y))).part s
    let Y:=fun (s:R.Mode) (y:F.Slice G)=>(Poly.pass (markedLog g (F.drape y) W)).part s
    let trueZ:=(H.rep N n j).eval V
    let refZ:=∫y,refW y ∂F.order G
    let actual:=(↑(trueZ⁻¹):ℂ) • forestRead F P.beta V D Set.univ
    let forecast:=Poly.inject (fun s=>FrozenRead.meanOn (F.order G) refW (Y s))
    0<refZ ∧ 2*trueZ*refZ*Poly.price w (actual-forecast) ≤
      2*refZ*(∫y,trueW y*Replica.discrepancy univ (Poly.toll w) X Y y ∂F.order G)+
      ∫z,Replica.actionBill trueW refW r z*Replica.diameter univ (Poly.toll w) Y z ∂(F.order G).prod (F.order G) := by
  intro P g dz a b trueW refW r X Y trueZ refZ actual forecast
  let op : StepData (H.S.side j n) (H.S.side (j+1) n) := H.levels.clock.op j n
  have branch := (H.levels.blocks j n).branches
  have dm : Measurable (F.drape (G:=G)) := F.continuous_drape.measurable
  have kp (y) : 0<dz y :=
    (inv_pos.mpr (YM.Push.BetaTransport.noiseCost_pos op _)).trans_le
      (YM.Push.BetaTransport.density_bounds op branch (β:=P.beta) le_rfl (F.drape y) V).1
  have ap (y) : 0<a y := SectorNext.Vacuum.strictly H sel N n (j+1) step _
  have bp (y) : 0<b y := Real.exp_pos _
  have dk : Envelope dz := by
    have meas : Measurable dz := by
      change Measurable ((fun X : Config G _ × Config G _ => op.density P.beta X.1 X.2) ∘ (fun y => (F.drape y,V)))
      exact (op.density_meas branch P.beta).comp (dm.prodMk measurable_const)
    obtain ⟨C,h⟩:=op.density_bound branch P.beta
    exact ⟨meas,C,fun y=>by rw [Real.norm_of_nonneg (kp y).le];exact h _ _⟩
  have ea : Envelope a := (P.envelope (sel.represents N n (j+1) step).good).comp_env dm
  have eb : Envelope b := by
    have E := (leaf_model K g (levelScalar P) W well R.quiet).comp_env dm
    change Envelope (fun y:F.Slice G=>(model g (levelScalar P) W K (F.drape y)).part R.quiet) at E
    simp_rw [model_unit] at E
    obtain ⟨C,h⟩:=E.cost
    exact ⟨by simpa only [Function.comp_def,Complex.ofReal_re] using Complex.measurable_re.comp E.meas,
      C,fun y=>by simpa only [Complex.norm_real] using h y⟩
  have cols := forest_measured_column H sel step F V D floor.vacancy floor.safe
  have trueMass : (∫y,trueW y ∂F.order G)=trueZ :=
    forest_original_volume H sel step F V D floor.vacancy floor.safe floor.gauges
  have cp : 0<trueZ := SectorNext.Vacuum.strictly H sel N n j step.le _
  have vi : Integrable refW (F.order G) := (dk.mul eb).integrable _
  have vp (y) : 0<refW y := mul_pos (kp y) (bp y)
  have wmass : 0<refZ := by
    apply (integral_pos_iff_support_of_nonneg (fun y=>(vp y).le) vi).2
    rw [show Function.support refW=Set.univ from Set.eq_univ_of_forall fun y=>(vp y).ne'];simp
  have yg : Leaf.All (fun U=>Poly.pass (markedLog g U W)) :=
    Leaf.sum _ _ (fun i=>Leaf.smul (Leaf.atom _) (Leaf.pow (leaf_mark g W well) _))
  have ye (s) : Envelope (Y s) := (yg s).comp_env dm
  have fi (s) : Integrable (fun y=>trueW y • X s y) (F.order G) := by
    simp only [Complex.real_smul];exact (cols.2 s).1
  have valX (s) : FrozenRead.meanOn (F.order G) trueW (X s)=actual.part s := by
    have h := (cols.2 s).2 Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ] at h
    change (∫y,trueW y ∂F.order G)⁻¹ • (∫y,trueW y • X s y ∂F.order G) = _
    change ((∫y,trueW y ∂F.order G)⁻¹:ℝ) • (∫y,trueW y • X s y ∂F.order G) =
      ((trueZ⁻¹:ℝ):ℂ) * (forestRead F P.beta V D Set.univ).part s
    rw [trueMass,Complex.real_smul,h]; simp only [Complex.real_smul];rfl
  have rm : Measurable r := (Real.measurable_log.comp ea.meas).sub (Real.measurable_log.comp eb.meas)
  have bound := Replica.different_readings univ (Poly.toll w) (fun s=>(Poly.worth wp s).le) X Y ye
    (fun y=>(kp y).le) ap bp rm 0 (fun _=> (add_zero _).symm) cols.1 vi (trueMass.symm ▸ cp) wmass fi
  change 2*(∫y,trueW y ∂F.order G)*refZ*(∑s,Poly.toll w s*
    ‖FrozenRead.meanOn (F.order G) trueW (X s)-FrozenRead.meanOn (F.order G) refW (Y s)‖) ≤ _ at bound
  have valY (s) : FrozenRead.meanOn (F.order G) refW (Y s)=forecast.part s := rfl
  rw [trueMass] at bound
  change 0<refZ ∧ _
  refine ⟨wmass,?_⟩
  change 2*trueZ*refZ*(∑s,Poly.toll w s*‖(actual-forecast).part s‖) ≤ _
  simp only [Extra.Trajectories.part_sub]
  simpa only [valX,valY] using bound

end YM.Integration.FVA1Physical.OlderPrice
