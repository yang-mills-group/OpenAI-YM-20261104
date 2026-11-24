import YM.Integration.WilsonReportingForestPivotConditional
import YM.Integration.WilsonReportingForestPivotReport

/-! The actual jointly admitted registered slot on the whole original occupied forest
fibre. The independently located other marked fields and a signed exterior
are inside the same normalized physical action. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree Source Precision PertExtension
open OPE.Therm MSbar.Heath RG16 PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction
open WilsonPositionSeparatedProfileReportingPrimary RG05Readout Address Native Pulse MergeProof Accent Axial Work.E08
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

/-- Any signed real quadrature of the whole placed primary product, at the
genuine measured singleton values and coupled to a gauge-invariant old spectator. -/
theorem observed (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (D:I→ℕ) (ℓ:(i:I)→Letter (D i)) : ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per (o:I→Site (R.family.side (m+1) per))
    (x:(i:I)→R.family.label (kept (ℓ i))) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let d:=fun i=>kept (ℓ i)
    let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) (m+1) N per) (ℓ i)
    let B:=incident R T d o
    let E:=moving T B
    let joint:=cold R m per d o
    let θ:=(R.family.path.rep N per (m+1)).p.threshold
    let value:=fun U=>H U*χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U)
    let w:=actualConditionalDensity R.family N per m V
    actualAverage R.family (N:=N) (joint.indicator value) V=
      ∫v:({e:T.Free|e∉E}:Set T.Free)→G.El,
        (∫x in ball 0 r,Chart.jacobian P x*joint.indicator (fun U=>w U*value U)
          (restored T B v (Chart.expLinks G (↥E) x)) ∂Chart.tangent G (↥E)) ∂Measure.pi (fun _=>G.probHaar) := by
  let d:=fun i:I=>kept (ℓ i)
  filter_upwards [original R simple slow J clear P hp pr sr d,
    (tendsto_add_atTop_nat 1).eventually (OPE.Therm.narrow (H:=R.family.path) simple)] with m receipt late N live per o x c χ T V H eH gH
  let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) (m+1) N per) (ℓ i)
  let A:=R.family.path.levels
  let θ:=(R.family.path.rep N per (m+1)).p.threshold
  let cell (i:I):=House.chilly (G:=G) (faces R m per (d i) (o i)) (cool A (m+1))
  let joint:=⋂i,cell i
  let rose:=fun U=>χ (c*∏i,Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U)
  let value:=fun U=>H U*χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U)
  let w:=actualConditionalDensity R.family N per m V
  have regular:Continuous rose:=χ.continuous.comp (continuous_const.mul (continuous_finsetProd _ (fun i _=>(R.family.localSection (d i)).continuous_places _ _)))
  have roseB:Envelope rose:=⟨regular.measurable,(isCompact_univ.exists_bound_of_continuousOn regular.continuousOn).imp fun _ a U=>a U (Set.mem_univ U)⟩
  have inv:GaugeInvariant (fun U=>H U*rose U):=by
    intro g U
    have each (i:I):Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) (Lattice.gauge g U)=
        Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U:=
      (R.family.localSection (d i)).placed_invariant (R.makes.sections (d i)) (o i) _ g U
    simp only [rose,each,gH g U]
  have ceiling:cool A (m+1)≤θ:=by
    have same:(R.family.path.rep N per (m+1)).p=A.budget (m+1):=(R.makes.wilson.represents N per (m+1) live).vac
    change 0<cool A (m+1) ∧ 4*cool A (m+1)≤A.clock.threshold (m+1) at late
    dsimp [θ];rw [same];change cool A (m+1)≤A.clock.threshold (m+1);linarith only [late.1,late.2]
  have equal (U) (h:U∈joint):H U*rose U=value U:=by
    have ok:=Set.mem_iInter.mp h
    have single (i:I):Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U=
        Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U:=
      (Push.Local.presented_primary _ (R.makes.sections (d i)) (y i) U (healthy _ (covers R (d i) (o i)) ceiling (ok i))).symm
    simp only [rose,value,single]
  have fuse (a:Config G (R.family.side (m+1) per)→ℝ):
      joint.indicator (fun U=>a U*(H U*rose U))=joint.indicator (fun U=>a U*value U):=by
    funext U;by_cases h:U∈joint
    · simp only [Set.indicator_of_mem h,equal U h]
    · simp only [Set.indicator_of_notMem h]
  have one:joint.indicator (fun U=>H U*rose U)=joint.indicator value:=by simpa only [one_mul] using fuse (fun _=>1)
  have phys:=receipt N live per o T V (fun U=>H U*rose U) (eH.mul roseB) inv
  let B:=incident R T d o
  let E:=moving T B
  change actualAverage R.family (N:=N) (joint.indicator (fun U=>H U*rose U)) V=
    ∫v:({e:T.Free|e∉E}:Set T.Free)→G.El,
      (∫x in ball 0 r,Chart.jacobian P x*joint.indicator (fun U=>w U*(H U*rose U))
        (restored T B v (Chart.expLinks G (↥E) x)) ∂Chart.tangent G (↥E)) ∂Measure.pi (fun _=>G.probHaar) at phys
  rw [one,fuse w] at phys
  exact phys

end YM.Integration.WilsonReportingForestPivots
