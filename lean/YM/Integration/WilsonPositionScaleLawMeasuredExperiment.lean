import YM.Integration.WilsonPositionScaleLawMeasuredCut
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotWeights
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredExperiment
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionProgramTrialPublicJointPivotOriginalArms (ordinary)
open WilsonPhysicalStationMixedWickPositionedMeter (moved)
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S)(J:ℝ→tower S) (Z:WilsonPrescription G)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{B n:ℕ}
local notation "posed" => WilsonPositionPrescribedFrame.positioned F J Z.store
open MeasureTheory
open WilsonPositionProgramTrialPublicJointPivotWeights (salary)
open scoped BigOperators
abbrev Slot (B:ℕ) := Σ j:Fin (B+1),Fin (Z.store.survey j).n
def row (i:Slot Z B) : XSpace.Normalize.Window G i.1 := (Z.store.survey i.1).scope i.2
def peak {I:Type*} [Fintype I] (bill:I→ℝ) : ℝ :=
  (insert 0 (Finset.univ.image bill)).max' (Finset.insert_nonempty ..)
theorem atMost {I:Type*} [Fintype I] (bill:I→ℝ)(i:I) : bill i≤peak bill := by
  apply Finset.le_max'
  simp
def mass {m:ℕ} (φ:Test m) : ℝ := ∫x:Points m,‖φ x‖
def variant (i:Slot Z B) (k:Fin (row Z i).n) : Option (Pin G i.1 ⊕ Unit)→Sec G i.1
  | none=>(row Z i).p k
  | some (.inl b)=>Module.finBasis ℝ (Sec G i.1) b
  | some (.inr _)=>leaf G i.1
abbrev Roster (i:Slot Z B) := Fin (row Z i).n→Option (Pin G i.1 ⊕ Unit)
def arity (B:ℕ) : ℕ := max 3 (Finset.univ.sup (fun i:Slot Z B=>(row Z i).n))
def testMass (B:ℕ) : ℝ := max (mass (Rose.test Z.criterion)) (peak (fun i:Slot Z B=>mass (row Z i).t))
def armMass (B:ℕ) : ℝ := max (∏k,salary (Rose.tag G k))
    (peak (fun h:Σ i:Slot Z B,Roster Z i=>∏ k,salary (variant Z h.1 k (h.2 k))))
def matrixMass (B:ℕ) : ℝ := max |(Rose.cT Z.criterion.cut G Z.criterion.image)⁻¹|
    (peak (fun j:Fin (B+1)=>‖(Z.store.survey j).stamps‖))
theorem budget (i:Slot Z B) (v:Roster Z i) :
    (row Z i).n≤arity Z B ∧ mass (row Z i).t≤testMass Z B ∧
    (∏k,salary (variant Z i k (v k)))≤armMass Z B ∧ ‖(Z.store.survey i.1).stamps‖ ≤ matrixMass Z B ∧
    IsCompact (tsupport ((row Z i).t:Points (row Z i).n→ℂ)) ∧
    tsupport ((row Z i).t:Points (row Z i).n→ℂ)⊆conf (row Z i).n ∧
    Integrable (fun x:Points (row Z i).n=>‖(row Z i).t x‖) := by
  refine ⟨le_trans (Finset.le_sup (f:=fun j:Slot Z B=>(row Z j).n) (Finset.mem_univ i)) (le_max_right ..),?_,?_,?_,?_,?_,?_⟩
  · exact (atMost (fun j:Slot Z B=>mass (row Z j).t) i).trans (le_max_right ..)
  · exact (atMost (fun h:Σ j:Slot Z B,Roster Z j=>∏k,salary (variant Z h.1 k (h.2 k))) ⟨i,v⟩).trans (le_max_right ..)
  · exact (atMost (fun j:Fin (B+1)=>‖(Z.store.survey j).stamps‖) i.1).trans (le_max_right ..)
  · exact (row Z i).t.hasCompactSupport
  · exact (row Z i).t.tsupport_subset
  · exact ((row Z i).t.continuous.integrable_of_hasCompactSupport (row Z i).t.hasCompactSupport).norm
theorem determines (d:ℕ)(T:Change G d) :
    (Z.store.survey d).tally (fun i=>watch ((Z.store.survey d).scope i) (gradient G d T))=T :=
  ((Z.store.survey d).equal _).trans ((Z.store.prepared d).1 T)
theorem condition (j:Fin (B+1))(T:Change G j) :
    ‖guide G j T‖ ≤ matrixMass Z B*‖fun i=>watch ((Z.store.survey j).scope i) (gradient G j T)‖ := by
  let D:=Z.store.survey j
  let a:=fun i=>watch (D.scope i) (gradient G j T)
  have measured:D.stamps a=guide G j T:=congrArg (guide G j) (determines Z j T)
  rw [←measured]
  exact (D.stamps.le_opNorm a).trans (mul_le_mul_of_nonneg_right
    ((atMost (fun k:Fin (B+1)=>‖(Z.store.survey k).stamps‖) j).trans (le_max_right ..)) (norm_nonneg a))
theorem clockBudget (B:ℕ) :
    3≤arity Z B ∧ mass (Rose.test Z.criterion)≤testMass Z B ∧
    (∏k,salary (Rose.tag G k))≤armMass Z B ∧
    |(Rose.cT Z.criterion.cut G Z.criterion.image)⁻¹| ≤ matrixMass Z B ∧
    Rose.cT Z.criterion.cut G Z.criterion.image<0 :=
  ⟨le_max_left ..,le_max_left ..,le_max_left ..,le_max_left ..,Z.criterion.fresh⟩
theorem original (simple:G.Simple) (prior:(l:Filter _)≤o.fuse)(A:ℝ→Group R.family B)
    (paid:Book (f:=o) (l:=l) (H:=H) A J)(six:6≤B) :
    ∀ᶠr in trail,∀rp:0<r,∀e:ℝ,0<e→∀ᶠz in (l:Filter (ℕ×ℕ)),
    (∀i:Slot Z B,∀v:Roster Z i,let w:=row Z i;let p:=fun k=>variant Z i k (v k)
      ‖WilsonPositionScaleLawMeasuredCut.sample F J Z (A r) i.1 rp w.t p z -
        WilsonPositionPrescribedScreen.hierarchy F posed i.1 r w.n w.t p‖<e) ∧
    |WilsonPositionScaleLawMeasuredCut.reading F J Z (A r) six r z - WilsonPositionHomogeneousFrame.reading F J Z r|<e := by
  filter_upwards [WilsonPositionScaleLawMeasuredCut.receives F J Z prior A paid,
    WilsonPositionScaleLawMeasuredCut.sensor F J Z simple prior A paid six] with r stock heat rp e ep
  apply Filter.Eventually.and
  · refine eventually_all.mpr fun i=>eventually_all.mpr fun v=>?_
    exact ((Metric.tendsto_nhds.mp (stock rp i.1 _ (row Z i).t (fun k=>variant Z i k (v k))) e ep).mono
      fun _ h=>by simpa only [dist_eq_norm] using h)
  · simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (heat rp) e ep
end YM.Integration.WilsonPositionScaleLawMeasuredExperiment
