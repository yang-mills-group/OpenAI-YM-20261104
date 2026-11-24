import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFreshReplicatedBasis
import YM.Integration.FVA1Physical.CommonCover.MeasuredReplicaFields

/-! Two true physical source directions on a single selected reporting forest.
The original and the separately constructed RG02 Wilson tables keep all their
old coefficients. For their raw double fresh variations there is exactly one
remaining bill, the two genuine vacua tested by the one common pair of fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure Labels Source
open YM.Integration.FVA1Physical.OriginalMixedWilson
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] [Fintype I] {C : Census I} {G : Gauge}

/-- These are the actual basis stencils and the same individual coupling
powers used in MSMatch.SourceTop.priced. Their finite grades, basis entries
and locations can all be different. Both source directions are varied at the
same nonbare report. The incoming full independent Wilson table and the actual
table may disagree everywhere on their older fields and actions. -/
theorem forest_fresh_physical_variation (A : Family G) (sel : A.path.Selected)
    {N n j : ℕ} (step : j<N) {O : ChartRatio G}
    (K : @Bulk.Kernel G (A.side j n) (A.side (j+1) n) (A.path.levels.clock.op j n)
      (A.path.rep N n (j+1)).clip (A.path.rep N n (j+1)).path O)
    (F : Forest (A.path.levels.clock.op j n).ratio)
    (W : Bulk.Colors C G (A.side (j+1) n)) (well : Bulk.Well W)
    (D : Lit C (Config G (A.side (j+1) n))) (floor : Floor (A.path.rep N n (j+1)) D)
    (left right : I) (apart : left ≠ right) (s : C.Mode) (pair : s.val = {left,right})
    (d : I → ℕ) (l : (i:I) → (A.labels.level (d i)).Index) (x : I→Site (A.side (j+1) n))
    (V : Config G (A.side j n)) :
    let H:=A.path; let P:=H.rep N n (j+1); let g:=measuredCoupling P.beta
    let k:=fun y:F.Slice G=>(H.levels.clock.op j n).density P.beta (F.drape y) V
    let a:=fun y:F.Slice G=>P.eval (F.drape y)
    let b:=fun y:F.Slice G=>weight g (levelScalar P) (F.drape y) W P.clip P.path
    let u:=fun y=>k y*a y; let v:=fun y=>k y*b y
    let r:=fun y=>Real.log (a y)-Real.log (b y)
    let z:=(H.rep N n j).eval V; let q:=∫y,v y ∂F.order G
    let h:=fun (y:F.Slice G) (i:I)=>
      (g^((A.labels.level (d i)).grades (l i)).2)⁻¹ •
        (A.localSection (d i)).places (Pi.single (l i) 1) (x i) (F.drape y)
    let X:=fun y=>freshPairSecant (unitScale (D (F.drape y))) left right s (h y)
    let Y:=fun y=>freshPairSecant (unitScale (model g (levelScalar P) W K (F.drape y))) left right s (h y)
    let stencil:=fun y=>h y left*h y right
    (∀y,X y=stencil y ∧ Y y=stencil y) ∧
      0<z ∧ 0<q ∧
      2*z*q*‖FrozenRead.meanOn (F.order G) u X-FrozenRead.meanOn (F.order G) v Y‖ ≤
        ∫t,Replica.actionBill u v r t*‖stencil t.1-stencil t.2‖ ∂(F.order G).prod (F.order G) := by
  intro H P g k a b u v r z q h X Y stencil
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
  have unitD (y:F.Slice G) : (unitScale (D (F.drape y))).part C.quiet=1 := by
    rw [unitScale,Poly.part_smul,inv_mul_cancel₀]
    rw [floor.vacancy]; exact Complex.ofReal_ne_zero.mpr (ap y).ne'
  have unitW (y:F.Slice G) : (unitScale (model g (levelScalar P) W K (F.drape y))).part C.quiet=1 := by
    rw [unitScale,Poly.part_smul,inv_mul_cancel₀]
    rw [model_unit]; exact Complex.ofReal_ne_zero.mpr (bp y).ne'
  have common (y:F.Slice G) : (Poly.pass (Multi.lambda C (h y))).part s=stencil y := by
    rw [Comparison.RG02.Cumulants.pass_lambda,pair]; simp [apart,stencil]
  have same (y:F.Slice G) : X y=stencil y ∧ Y y=stencil y :=
    ⟨(fresh_pair_is_filed _ (unitD y) left right apart s pair (h y)).trans (common y),
     (fresh_pair_is_filed _ (unitW y) left right apart s pair (h y)).trans (common y)⟩
  refine ⟨same,zp,qp,?_⟩
  have cont (i:I) : Continuous (fun y=>h y i) := by
    let scale:ℝ:=(g^((A.labels.level (d i)).grades (l i)).2)⁻¹
    change Continuous (fun y:F.Slice G=>scale • (A.localSection (d i)).places (Pi.single (l i) 1) (x i) (F.drape y))
    exact (((A.localSection (d i)).continuous_places (Pi.single (l i) 1) (x i)).comp F.continuous_drape).const_smul scale
  have bounded : Envelope stencil := Envelope.compactC ((cont left).mul (cont right))
  rw [show X=stencil from funext fun y=>(same y).1,show Y=stencil from funext fun y=>(same y).2,←trueMass]
  exact Replica.reading (fun y=>(kp y).le) ap bp (ea.meas.log.sub eb.meas.log) 0 (fun _=>by simp only [add_zero];rfl)
    bounded ui vi (trueMass ▸ zp) qp

end YM.Integration.FVA1Physical.Exchange.RoseCut
