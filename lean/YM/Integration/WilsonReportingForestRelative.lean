import YM.Integration.WilsonReportingForestPivots

/-! Relative coordinates reconstruct every crossing bond from its real, held
fine pivot. Common right multiplication preserves the original product Haar
measure for every value of the shared exterior. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm WilsonPhysicalRegisteredForestAction
open scoped Classical Topology
variable {G:Gauge} {c f:Side} {S:StepData c f}

def restored (T:Forest S.ratio) (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (x:↥(moving T B)→G.El) : Config G f := filled T (moving T B) v (x*background T B v)

/-- The true pivot and all other saved bonds keep their prescribed values.
The original relative coordinate at each integrated bond is precisely x_e. -/
theorem decoded (T:Forest S.ratio) (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (x:↥(moving T B)→G.El) :
    let E:=moving T B
    let u:=(cut T E).symm (x*background T B v,v)
    (∀e:↥E,deviation T u e.val=x e) ∧ (∀e:({i:T.Free|i∉E}:Set T.Free),u e.val=v e) := by
  let E:=moving T B
  let u:=(cut T E).symm (x*background T B v,v)
  have eq:=(cut T E).apply_symm_apply (x*background T B v,v)
  have one (e:↥E):u e.val=x e*background T B v e:=congrFun (congrArg Prod.fst eq) e
  have two (e:({i:T.Free|i∉E}:Set T.Free)):u e.val=v e:=congrFun (congrArg Prod.snd eq) e
  refine ⟨?_,two⟩;intro e
  change deviation T u e.val=x e
  by_cases h:internal T e.val
  · simp only [deviation,if_pos h,one,background,dif_pos h,mul_one]
  · have fixed:=two ⟨pivot T e.val,saved T B e.val h⟩
    dsimp only at fixed
    simp only [deviation,if_neg h,one,background,dif_neg h,fixed,mul_inv_cancel_right]

variable (R:Run G) {I:Type} [Fintype I]
local notation "A"=>R.family.path.levels

/-- For each actual, arbitrary exterior v the complete signed joint retains
its one original Haar Jacobian. Cross-parent wires use their sampled pivot. -/
theorem relative (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:I→ℕ) :
    ∀ᶠ m:ℕ in atTop,∀per (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).clock.op m per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let C:=cold R m per d o
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (a:Config G (R.family.side (m+1) per)→ℝ),Measurable a→
    (∫x,C.indicator a (filled T E v x) ∂Chart.physical G (↥E))=
      ∫x in ball 0 r,Chart.jacobian P x * C.indicator a (restored T B v (Chart.expLinks G (↥E) x)) ∂Chart.tangent G (↥E) := by
  filter_upwards [chart R simple slow J clear pr d] with m all per o T
  dsimp only;intro v a meas
  let B:=incident R T d o
  let E:=moving T B
  let C:=cold R m per d o
  let α:=background T B v
  let F:=fun x:↥E→G.El=>C.indicator a (filled T E v x)
  let Φ:=fun x:↥E→G.El=>F (x*α)
  have mfill:Measurable (filled T E v):=T.continuous_drape.measurable.comp
    ((cut T E).symm.measurable.comp (measurable_id.prodMk measurable_const))
  have raw:Measurable F:=(meas.indicator (MeasurableSet.iInter (fun _=>House.bath _))).comp mfill
  have mΦ:Measurable Φ:=raw.comp (continuous_mul_const α).measurable
  have paid:MeasurePreserving (fun x:↥E→G.El=>x*α) (Chart.physical G (↥E)) (Chart.physical G (↥E)) :=
    measurePreserving_pi _ _ (fun e:↥E=>measurePreserving_mul_right G.probHaar (α e))
  have within (x:↥E→G.El) (g:restored T B v x∈C):x∈Chart.chamber G (↥E) r:=by
    let u:=(cut T E).symm (x*α,v)
    have h:=all per o T u g
    have eq:(fun e:↥E=>deviation T u e.val)=x:=funext (decoded T B v x).1
    rw [←eq];exact h
  have restriction:(Chart.chamber G (↥E) r).indicator Φ=Φ:=by
    funext x;by_cases h:x∈Chart.chamber G (↥E) r
    · exact Set.indicator_of_mem h _
    · rw [Set.indicator_of_notMem h];exact (Set.indicator_of_notMem (fun g=>h (within x g)) a).symm
  change (∫x,F x ∂Chart.physical G (↥E))=_
  calc
    _=∫x,Φ x ∂Chart.physical G (↥E):=(paid.integral_comp (Homeomorph.mulRight α).measurableEmbedding F).symm
    _=∫x in Chart.chamber G (↥E) r,Φ x ∂Chart.physical G (↥E):=by
      rw [←integral_indicator (Chart.Ratio.chamber_open hp sr.le).measurableSet,restriction]
    _=_:=Chart.Ratio.chamber_integral hp Φ mΦ sr pr

end YM.Integration.WilsonReportingForestPivots
