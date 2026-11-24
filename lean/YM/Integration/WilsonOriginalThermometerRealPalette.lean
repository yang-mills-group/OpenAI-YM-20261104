import YM.Integration.WilsonOriginalThermometerPalette

/-! The same original three-slot course with the real-linear scalar tests
and their actual zero kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerRealPalette
open WilsonOriginalThermometerPalette
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}

theorem attentive (i : Fin 3) : Attn (fun _ : Fin 3=> (⊥:Submodule ℝ ℂ)) disks {i} (probe i):=by
  refine ⟨fun x y eq=>congrArg Subtype.val (eq i (mem_singleton_self _)),?_,?_⟩
  · intro j hj x s t u a b hu
    obtain rfl:= mem_singleton.mp hj
    simpa only [probe,Function.update_self] using hu
  · intro j hj x hx
    obtain rfl:=mem_singleton.mp hj
    exact (Submodule.mem_bot ℝ).mp hx

theorem original (simple : G.Simple) (ε : ℝ) (eps : 0<ε) :
    ∀ᶠ k in atTop,∀ (A:Group R.family 6), A.station.k=k → A.station.checked f H A.horizon →
    ∀ σ Ω : ℝ,1 ≤ Ω →
    let K:=(R.family.path.levels.clock.hatBeta k)^ε * salary R A
    let E:=max 1 ((1+K)*wallet R levels σ)
    let w:=fun _ : Fin 3=>(E*Ω)⁻¹
    ∀ (N p:ℕ), k<N → ∀ o:Fin 3→Site (R.family.side k p),
    let g:=Pert.Asymptotics.regulatorRun R.family N p k
    let P:= R.family.path.rep N p k
    let X:=rows R levels o σ g P.p.threshold (coordinates R A k N p) probe
    ∀ order count stage vac coarse : ℕ, Fintype.card (Fin 3) ≤ count → maximum R levels ≤ order →
      order+1 ≤ stage → order ≤ coarse → tariff R levels ≤ coarse →
      order+Fintype.card (Fin 3)*tariff R levels ≤ AllOrder.Burn.horizon vac+2 →
      Scene.Armada X w (fun _=>tariff R levels) σ Ω⁻¹ order count (Fintype.card (Fin 3)*tariff R levels) ∧
      Mentor.Cruise.Voter X σ order count stage vac coarse ∧
      Tableau (fun _ : Fin 3=> (⊥:Submodule ℝ ℂ)) disks X ∧
      (∀s:(Stock.census (Fin 3)).Mode, Poly.toll w s*(E*Ω)^s.val.card=1) ∧
      WilsonOriginalStarFlagPrice.extent R levels ≤ P.p.B := by
  filter_upwards [WilsonOriginalThermometerPalette.original R (f:=f) (H:=H) simple ε eps]
    with k paid A date checked σ Ω one K E w N p top o g P X order count stage vac coarse load available room future stamp cover
  obtain ⟨crew,votes,_,restored,aperture⟩:=paid A date checked σ Ω one N p top o order count stage vac coarse
    load available room future stamp cover
  exact ⟨crew,votes,WilsonOriginalStarSceneMasked.tests R levels o σ g P.p.threshold _ _ _ probe attentive,
    restored,aperture⟩

end YM.Integration.WilsonOriginalThermometerRealPalette
