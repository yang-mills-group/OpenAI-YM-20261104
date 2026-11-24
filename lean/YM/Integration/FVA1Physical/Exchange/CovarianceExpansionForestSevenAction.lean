import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSevenAction
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionForestFreshBasis

/-! The complete physical three-stencil proper-face table compared under the
original and numerical Wilson vacua. Each product is formed on one field, with
complex engineering weights, before any conditional averaging. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure Labels Source
open YM.Integration.FVA1Physical.OriginalMixedWilson
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] [Fintype I] {C : Census I} {G : Gauge}

def physicalProperRows {X:Type*}(p:Fin 3→X→ℂ):Fin 7→X→ℂ :=
  ![p 0,p 1,p 2,fun x=>p 0 x*p 1 x,fun x=>p 0 x*p 2 x,fun x=>p 1 x*p 2 x,
    fun x=>p 0 x*p 1 x*p 2 x]

private theorem proper_product_env {X:Type*}[MeasurableSpace X]
    (p:Fin 3→X→ℂ)(fee:∀i,Envelope (p i))(s:Fin 7):Envelope (physicalProperRows p s):=by
  fin_cases s
  · exact fee 0
  · exact fee 1
  · exact fee 2
  · exact Leaf.multiply (fee 0) (fee 1)
  · exact Leaf.multiply (fee 0) (fee 2)
  · exact Leaf.multiply (fee 1) (fee 2)
  · exact Leaf.multiply (Leaf.multiply (fee 0) (fee 1)) (fee 2)

/-- v may be any actually submitted finite field vector, including complex
lower-grade compensations. The source weight is charged component by component
at the true measured coupling. Locations may coincide or be distinct. -/
theorem forest_seven_source_action (A : Family G) (sel : A.path.Selected)
    {N n j : ℕ} (step : j<N) {O : ChartRatio G}
    (K : @Bulk.Kernel G (A.side j n) (A.side (j+1) n) (A.path.levels.clock.op j n)
      (A.path.rep N n (j+1)).clip (A.path.rep N n (j+1)).path O)
    (F : Forest (A.path.levels.clock.op j n).ratio)
    (W : Bulk.Colors C G (A.side (j+1) n)) (well : Bulk.Well W)
    (D : Lit C (Config G (A.side (j+1) n))) (floor : Floor (A.path.rep N n (j+1)) D)
    (d:Fin 3→ℕ) (w:(i:Fin 3)→(A.labels.level (d i)).Coeff)
    (x:Fin 3→Site (A.side (j+1) n)) (V:Config G (A.side j n)):
    let H:=A.path; let P:=H.rep N n (j+1); let g:=measuredCoupling P.beta
    let k:=fun y:F.Slice G=>(H.levels.clock.op j n).density P.beta (F.drape y) V
    let a:=fun y:F.Slice G=>P.eval (F.drape y)
    let b:=fun y:F.Slice G=>weight g (levelScalar P) (F.drape y) W P.clip P.path
    let u:=fun y=>k y*a y; let v:=fun y=>k y*b y
    let r:=fun y=>Real.log (a y)-Real.log (b y)
    let z:=(H.rep N n j).eval V; let q:=∫y,v y ∂F.order G
    let h:=fun (i:Fin 3) (y:F.Slice G)=>
      ∑l:(A.labels.level (d i)).Index,
        (g^((A.labels.level (d i)).grades l).2)⁻¹ •
          ((w i l)*(A.localSection (d i)).places (Pi.single l 1) (x i) (F.drape y))
    let raw:=physicalProperRows h
    let U:=fun i=>FrozenRead.meanOn (F.order G) u (raw i)
    let W':=fun i=>FrozenRead.meanOn (F.order G) v (raw i)
    let combined:=fun y=>∑s:Fin 7,properWeights U W' s*raw s y
    0<z ∧ 0<q ∧
      (properThree U-properThree W'=FrozenRead.meanOn (F.order G) u combined-FrozenRead.meanOn (F.order G) v combined) ∧
      2*z*q*‖properThree U-properThree W'‖ ≤
        ∫t,Replica.actionBill u v r t*‖combined t.1-combined t.2‖ ∂(F.order G).prod (F.order G) := by
  intro H P g k a b u v r z q h raw U W' combined
  let S:=H.levels.clock.op j n
  have branch := (H.levels.blocks j n).branches
  have dm : Measurable (F.drape (G:=G)) := F.continuous_drape.measurable
  have kp (y) : 0<k y :=
    (inv_pos.mpr (YM.Push.BetaTransport.noiseCost_pos S _)).trans_le
      (YM.Push.BetaTransport.density_bounds S branch (β:=P.beta) le_rfl (F.drape y) V).1
  have ap (y) : 0<a y := SectorNext.Vacuum.strictly H sel N n (j+1) step _
  have bp (y) : 0<b y := Real.exp_pos _
  have dk : Envelope k := by
    have meas : Measurable k := by
      change Measurable ((fun T : Config G _ × Config G _ => S.density P.beta T.1 T.2) ∘ (fun y => (F.drape y,V)))
      exact (S.density_meas branch P.beta).comp (dm.prodMk measurable_const)
    obtain ⟨M,hm⟩:=S.density_bound branch P.beta
    exact ⟨meas,M,fun y=>by rw [Real.norm_of_nonneg (kp y).le];exact hm _ _⟩
  have ea : Envelope a := (P.envelope (sel.represents N n (j+1) step).good).comp_env dm
  have eb : Envelope b := by
    have E := (leaf_model K g (levelScalar P) W well C.quiet).comp_env dm
    change Envelope (fun y:F.Slice G=>(model g (levelScalar P) W K (F.drape y)).part C.quiet) at E
    simp_rw [model_unit] at E
    obtain ⟨M,hm⟩:=E.cost
    exact ⟨by simpa only [Function.comp_def,Complex.ofReal_re] using Complex.measurable_re.comp E.meas,
      M,fun y=>by simpa only [Complex.norm_real] using hm y⟩
  have ui : Integrable u (F.order G) := (dk.mul ea).integrable _
  have vi : Integrable v (F.order G) := (dk.mul eb).integrable _
  have trueMass : (∫y,u y ∂F.order G)=z :=
    forest_original_volume H sel step F V D floor.vacancy floor.safe floor.gauges
  have zp : 0<z := SectorNext.Vacuum.strictly H sel N n j step.le _
  have vp (y) : 0<v y := mul_pos (kp y) (bp y)
  have qp : 0<q := by
    apply (integral_pos_iff_support_of_nonneg (fun y=>(vp y).le) vi).2
    rw [show Function.support v=Set.univ from Set.eq_univ_of_forall fun y=>(vp y).ne']; simp
  have env(i:Fin 3):Envelope (h i):=by
    apply Envelope.compactC
    apply continuous_finsetSum
    intro l _
    have wh : Continuous (fun y:F.Slice G=>(w i l)*(A.localSection (d i)).places (Pi.single l 1) (x i) (F.drape y)) :=
      continuous_const.mul (((A.localSection (d i)).continuous_places (Pi.single l 1) (x i)).comp F.continuous_drape)
    exact wh.const_smul ((g^((A.labels.level (d i)).grades l).2)⁻¹ : ℝ)
  have joined:=seven_signed_action (F.order G) dk.meas ea.meas eb.meas (fun y=>(kp y).le) ap bp
    (ea.meas.log.sub eb.meas.log) 0 (fun _=>by simp only [add_zero];rfl) raw (proper_product_env h env)
    ui vi (trueMass ▸ zp) qp
  refine ⟨zp,qp,joined.1,?_⟩
  rw [←trueMass]
  exact joined.2

end YM.Integration.FVA1Physical.Exchange.RoseCut
