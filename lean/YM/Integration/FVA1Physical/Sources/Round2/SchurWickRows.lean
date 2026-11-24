import YM.Integration.FVA1Physical.Sources.Round2.StencilWickChart

/-! Volume-independent exterior removal on the polynomials of the literal
primary field insertions used in the Gaussian and normalized FVA2 steps. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Lis MSbar.Whisk MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Cacao
open MSbar.Bakery MSbar.Bakery.Film MSbar.Mosaic MSbar.Kelvin Push.Uniform Next.SectorChange
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)
variable {c f : Side} (S : StepData c f) (F : Forest S.ratio) (o : ι → Site f)

theorem wires_inside (y : ℝ) (b : Site f) (near : ∀ l : Slice J, 2*separation b (legs J o l).1 ≤ spotN y) :
    ∀ i,slotEdge J S F o i ∈board F (boxX y b) := by
  intro i;apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
  apply halo_spec.mpr;refine ⟨b,mem_singleton_self _,?_⟩
  have n:=near i.val
  change separation b (legs J o i.val).1 ≤ spotN y;omega

def lampBank (b : Bool) (a : Finset (Slice J)) : PowerSeries (Pot (Wire G (↑a))) := PowerSeries.mk (lampRow J b a)

theorem purchased_field_wick (V : Voice G) (clear : Clear G V) (simple : G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (part : Bool) (n Q : ℕ) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x; let X:=boxX y b; let Y:=boxY y b;let idx:=includeX (G:=G) A.F X
      let O:=represent (tint G (Exterior.Body 1 A.c) z); let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      ∀ (o : ι→Site A.f) (near : ∀ l : Slice J, 2*separation b (legs J o l).1≤ spotN y),
      let s:=slotPrices J A.S A.F o X (wires_inside J A.S A.F o y b near)
      let pol:=lampRow J part (activeSlots J A.S A.F o) n
      ∀ U∈hotel A.F X Y V O ν (pillow y) (room y),
      |interiorReading A V y z b U s pol - bulkReading A z (idx ∘ s) pol|≤y^(-(Q:ℝ)) := by
  have offers := eventually_all.mpr (fun m:Finset (Slice J)=>
    purchased_wick_stencil V clear (Next.Foundations.chart G) (Next.Foundations.chart_ok G)
      simple H H' P K branch (lampRow J part m n) Q hD)
  filter_upwards [offers] with x ready
  intro A z b patch kernel season hz y X Y idx O ν o near s pol U inside
  exact ready _ A z b patch kernel season hz s (fun i=>near i.1.val) U inside

/-- All fixed-order normalized Wilson coefficients for a source and action with the
same finite local legs. The action may vary with the fixed trunk mask and has no shell
or period parameter. The vacuum in each column is computed in its own Gaussian. -/
theorem purchased_field_column (V : Voice G) (clear : Clear G V) (simple : G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (f : ∀ m:Finset (Slice J), PowerSeries (Pot (Wire G (↑m)))) (funKind : ∀ m, Kind (f m))
    (part : Bool) (p n Q : ℕ) (hn : n≤p) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x;let X:=boxX y b;let Y:=boxY y b;let idx:=includeX (G:=G) A.F X
      let O:=represent (tint G (Exterior.Body 1 A.c) z);let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      let HM:=mold A.pre A.F A.v
      ∀ (o : ι→Site A.f) (near : ∀ l : Slice J, 2*separation b (legs J o l).1≤ spotN y),
      let s:=slotPrices J A.S A.F o X (wires_inside J A.S A.F o y b near)
      let m:=activeSlots J A.S A.F o
      ∀ U∈hotel A.F X Y V O ν (pillow y) (room y),
      let inside:=fun i=>A.fClock⁻¹*interiorCoordinate A V y z b U (idx (s i))
      let far:=fun i=>A.fClock⁻¹*bulkCoordinate A z (idx (s i))
      |PowerSeries.coeff n (localColumn s inside ((pinch idx HM)⁻¹) (f m) (lampBank J part m) p)-
        PowerSeries.coeff n (localColumn (idx ∘ s) far HM⁻¹ (f m) (lampBank J part m) p)|≤y^(-(Q:ℝ)) := by
  have offers := eventually_all.mpr (fun m:Finset (Slice J)=>
    purchased_wilson_column V clear (Next.Foundations.chart G) (Next.Foundations.chart_ok G) simple H H' P K branch
      (f m) (lampBank J part m) (funKind m) p n Q hn hD)
  filter_upwards [offers] with x ready
  intro A z b patch kernel season hz y X Y idx O ν HM o near s m U inside
  exact ready _ A z b patch kernel season hz s (fun i=>near i.1.val) U inside

end YM.Integration.FVA1Physical.Round2.Curvature
