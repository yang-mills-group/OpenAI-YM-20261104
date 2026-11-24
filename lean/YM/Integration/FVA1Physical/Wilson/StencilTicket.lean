import YM.Integration.FVA1Physical.Wilson.BareSolenoid

/-! The ticket supplied to the FVA2 solenoid is the Taylor ticket of the
literal product of the physical lattice stencils in the free-link chart. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Filter Function YM.Lattice YM.RG YM.Tree YM.FVA2 YM.FVA2.CityHistory
open YM.FormalOPE.RG10.MultiGauge YM.RGComparison.Core16 YM.RGComparison.Core16.Spool
open YM.RGComparison.Core16.Lumen YM.PertExtension.Chart
open scoped Classical Topology

variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    {ι : Type} [Fintype ι] (J : ι → Lamp G) (y : ι → Site f)

/-- The physical-group and curvature-coordinate versions of the full
multi-insertion stencil have identical Taylor tickets, with every trunk
fixed and all free links exponentiated. -/
theorem group_stencil_ticket (b : Bool) : Stack.rise (stencilSignal S F J y b) =
    Stack.rise (fun w : Future G S F × Pins G c => look b (column J y (F.drape (expLinks G _ w.1)))) := by
  have h (i : F.Free) :
      ∀ᶠ w : Future G S F × Pins G c in 𝓝 0,
        launch (G.curvature (G.lieExp (w.1 i))) = G.lieExp (w.1 i) := by
    have hc : Continuous (fun w : Future G S F × Pins G c => G.lieExp (w.1 i)) :=
      G.lieExp_cont.comp ((continuous_apply i).comp continuous_fst)
    have ht : Tendsto (fun w : Future G S F × Pins G c => G.lieExp (w.1 i)) (𝓝 0) (𝓝 (1 : G.El)) := by
      simpa using hc.tendsto 0
    exact ht.eventually (leaving (G := G))
  have he : stencilSignal S F J y b =ᶠ[𝓝 0] fun w =>
      look b (column J y (F.drape (expLinks G _ w.1))) := by
    filter_upwards [eventually_all.mpr h] with w hw
    unfold stencilSignal sight column
    rw [← exhibition J y (F.drape (expLinks G _ w.1))]
    apply congrArg (fun z => look b (exhibit J z))
    funext j
    unfold Fk.scene earns
    by_cases hi : legs J y j ∈ F.trunks
    · rw [dif_pos hi]
      change launch ((0 : ℝ) • (0 : G.Color)) = F.drape (expLinks G _ w.1) (legs J y j)
      simp only [zero_smul, launch_zero]
      exact (F.on_tree _ ⟨_,hi⟩).symm
    · rw [dif_neg hi]
      change launch (G.curvature (G.lieExp (w.1 ⟨_,hi⟩))) = F.drape (expLinks G _ w.1) (legs J y j)
      exact (hw _).trans (F.off_tree (expLinks G F.Free w.1) ⟨_,hi⟩).symm
  apply Stack.into
  intro u
  rw [Stack.read_real, Stack.read_real, GermLaplace.equal_jet he]

end YM.Integration.FVA1Physical.Wilson
