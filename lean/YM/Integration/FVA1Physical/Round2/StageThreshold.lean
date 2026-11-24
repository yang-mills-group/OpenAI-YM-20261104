import YM.Integration.FVA1Physical.Round2.VacuumInvoice

/-! Buy any numerical threshold depending on the two actual stage profiles,
block patch and kernel before choosing the period, cutoff or source tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Schedule
open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Classical Topology
variable {G : Gauge}

abbrev StageThreshold := Stage → Stage → Patch → KernelChoices → ℝ

def selectedThreshold (f : StageThreshold) : Goal G := fun _ _ A _ =>
  ∀ j n, f (A.B.a.params j) (A.B.a.params (j+1)) (A.B.a.clock.op j n).patch
    (A.B.a.clock.op j n).kernel ≤ A.B.a.clock.hatBeta j

theorem selectedThreshold_obtainable (f : StageThreshold) : Obtainable (selectedThreshold (G:=G) f) := by
  intro s T C z R E hdr
  refine ⟨fun _=>0,?_⟩
  intro l hl D w v Z F S pocket records admissible P menus V
  let Y := ThroughLaunch.raise s l
  let test (a : ℕ) (x : ℝ) := ∀ i ≤ a, ∀ patch : Patch, patch.J=a → patch.L=D.L a →
    f (Y.profile i) (Y.profile a) patch Y.kernel ≤ x
  have buy (a : ℕ) : ∀ᶠ x : ℝ in atTop, test a x := by
    by_cases ha : 4 ≤ a
    · let patch : Patch := ⟨D.L a,a,ha,(D.large a).size,(D.large a).odd⟩
      have h := (Finset.range (a+1)).eventually_all.mpr (fun i _=>
        eventually_ge_atTop (f (Y.profile i) (Y.profile a) patch Y.kernel))
      filter_upwards [h] with x prices
      intro i hi P hP hL
      have eq : P=patch := by cases P; unfold patch; congr
      exact eq ▸ prices i (Finset.mem_range.mpr (by omega))
    · exact .of_forall fun x i hi p hp _=>(ha (hp ▸ p.order_cut)).elim
  obtain ⟨u,_,hu,paid⟩ := collect_upper V.betaEntry test buy
  let W : Delays P := {V with betaEntry:=u}
  refine ⟨W,⟨hu,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' later cost bar wait price B archive shape exchange η q b bt guide J hf hv hw ha div j n
  let a := B.a.clock.J (j+1)
  have profile (i : ℕ) : B.a.params i=Y.profile (B.a.clock.J i) := by
    unfold Levels.params Calendar.params
    rw [B.valid.stage]
  change f (B.a.params j) (B.a.params (j+1)) (B.a.clock.op j n).patch B.a.clock.kernel ≤ _
  rw [profile j,profile (j+1),B.valid.kernel]
  refine paid a _ ((later.beta a).trans (B.valid.pays j)) _ (B.a.fits.mono (Nat.le_succ j))
    (B.a.clock.op j n).patch rfl ?_
  change B.a.S.block j=D.L a
  rw [←B.a.fits.sameFactor,B.valid.lengths]

end YM.Qlocal.Schedule
