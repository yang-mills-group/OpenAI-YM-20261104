import YM.Integration.WilsonMatrixTicketLanesRetainedRoster

/-! The local registered angular cup and the true upper Wilson insertion on the very same forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedPlacement
open Function Filter MeasureTheory Finset Lattice RG Tree Gauge Wilson Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Stage
open RGComparison.Core16.Lumen.Planet RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Spool
open FVA2 FVA2.CityHistory WilsonCoherentLampTicket WilsonMatrixTicketLanesReflectedInner WilsonMatrixTicketLanesRetainedRoster
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {I : Type} [Fintype I] (J : I→Lamp G) {c f : Side} (S : StepData c f) (T : Tree.Forest S.ratio) (o : I→Site f) (part : Bool)
local notation "layer" => Descent.push S T Descent.nil

def lift (x : Future G S T) : Descent.Coordinates G layer := Sum.elim x Empty.elim

theorem chart (x : Future G S T) : ∀ᶠ t : ℝ in 𝓝 0,
    sight J (placed J S T o (t•x))=tally J o (T.drape (Chart.expLinks G T.Free (t•x))) := by
  have enter (e : T.Free) : ∀ᶠ t : ℝ in 𝓝 0,launch (turn (t•x e))=G.lieExp (t•x e) := by
    have cont : Continuous (fun t:ℝ=>G.lieExp (t•x e)) := by fun_prop
    have tends : Tendsto (fun t:ℝ=>G.lieExp (t•x e)) (𝓝 0) (𝓝 1) := by simpa using (cont.continuousAt (x:=0)).tendsto
    exact tends.eventually (leaving (G:=G))
  filter_upwards [eventually_all.mpr enter] with t ht
  rw [←exhibition J o];apply congrArg (exhibit J);funext j
  let q:=legs J o j
  change launch (Fk.scene (earns S T J o) (0,t•x) j)=T.drape (Chart.expLinks G T.Free (t•x)) q
  unfold Fk.scene;by_cases h : q∈T.trunks
  · rw [show earns S T J o j=.inr 0 from dif_pos h]
    change launch ((0:ℝ)•(0:G.Color))=_;rw [zero_smul,launch_zero]
    exact (T.on_tree _ ⟨q,h⟩).symm
  · rw [show earns S T J o j=.inl ⟨q,h⟩ from dif_neg h]
    exact (ht ⟨q,h⟩).trans (T.off_tree (Chart.expLinks G T.Free (t•x)) ⟨q,h⟩).symm

/-- This is the actual finite Wilson source on the upper torus. The held shift enters only
through the genuine free coordinates in the original tree projection. -/
theorem jet (test : Descent.Testable layer (look part ∘ column J o)) (k : ℕ) (z : Future G S T × Pins G c) :
    Radial.jet (source J S T o part) k z =
      Radial.jet ((look part ∘ column J o) ∘ (layer).fine 1 ∘ (layer).tablePath) k (lift S T z.1) := by
  have same : ∀ᶠ t : ℝ in 𝓝 0,source J S T o part (t•z)=
    ((look part ∘ column J o) ∘ (layer).fine 1 ∘ (layer).tablePath) (t•lift S T z.1) := by
    filter_upwards [chart J S T o z.1] with t ht;exact congrArg (look part) ht
  have old:=directions test.smooth (lift S T z.1)
  have current:=directions ((admitted J S T o part).of_le le_top) z
  apply congr_fun (current.unique ?_) k;intro n
  obtain ⟨C,hC,amount⟩:=old n;refine ⟨C,hC,?_⟩
  filter_upwards [same.filter_mono nhdsWithin_le_nhds,amount] with t eq h
  change ‖source J S T o part (t•z)-_‖≤_;rwa [eq]

end YM.Integration.WilsonMatrixTicketLanesRetainedPlacement
