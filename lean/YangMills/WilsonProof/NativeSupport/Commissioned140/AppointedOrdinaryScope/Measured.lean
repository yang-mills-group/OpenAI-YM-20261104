import YM.GradedFar.Test
import YangMills.WilsonProof.NativeSupport.Commissioned140.AppointedOrdinaryScope.Clock
/-!
# NearFarDelta: the second inequality of (M.2), on Match

The actual output statement, with all the field, grade, log and quantitative bridge arguments.
Use after the previous hypotheses of the proof, in particular
`Trace.Pilot.Coupling G (WilsonPositionHomogeneousFrame.reading F J N)` is the **physical clock
hypothesis** (same reading as there, spelling it in the original project's running-limit form).
SEE `Clock` for the derivation of the bound on the evaluation from it and of it from the costs
of (F.3). Our M2 is relative to supplied hypotheses. Do not infer attainment of physical hypotheses
on any particular Run or from choosing J Leading, or obtain it by renaming some *other* `N`. No
kinetic constraint on an MS_Data input replaces this.

The price is on profiles in x,y units, using the same y throughout. Even all T≥T₀; exercise at,
for example, any T in the moving range of the question with `s_phys = r T`. Valid at ANY d,e
and shapes in those compacta, interpreted using fixed through-cap sec labels -- `Box` is the
norm requirement (choose L 1 for the unit balls in that basis norm, or any bounded costs).
Thus no exemption/cheaper scope for the real star labels, lower components, or subsets. As
formal point estimate it has no viewer or mesh indices. See applications.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Dframe O O.Score Enh FVA2.GradedFar
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {S : Table R.family.book}
    (Fph : Final R.family f S) (J : ℝ → PhysMS.tower S) (N : WilsonPrescription G)
    {hG : G.Simple}
    (Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    (H : Main.Match N hG Z σ true) (ν : ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "F" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G
local notation "t" => WilsonPositionHomogeneousFrame.reading Fph J N

include H
theorem second (ht : Coupling G t) (hd : AppointedH140Through l d) (he : AppointedH140Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S' : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
    (p : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ᶠ r in trail, ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ K, ∀ y ∈ S',
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
      ∀ (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G e), Box u L → Box v L →
        ‖appointedH140Crop p (t r) (fullSeries A F (-Real.log T) hd he x y u v) -
            croppedResponse A F (-Real.log T) hh he y v p (t r) (croppedVector A h p u x (t r))‖ ≤
          C * ((T^(h+1))⁻¹ + (g r)^(p+1)) * (1+Real.log T)^k :=
  clocked N Z H ν ht hd he hh K S' hK hx hS hy p L hL
local notation "W" => WilsonPositionPrescribedFrame.positioned Fph J N.store
local notation "testedReal" => WilsonPositionThermometerReading.tested Fph W N.criterion
local notation "cT" => Rose.cT N.criterion.cut G N.criterion.image
/-- Apply with the (F.3) **continuum** cost hypothesis of the supplied proof. Not a later phase forecast.
See `Clock`. `t'` hypothesis is for the already-voted clock `t'_ℓ`. -/
theorem second_of_poseFit (t' : ℝ → ℝ) (order : ℕ) (ht' : Tendsto (fun r => t' r / g r) trail (𝓝 1))
    {C : ℝ} (hT : ∀ᶠ r in trail, ‖testedReal r - ((cT * t' r : ℝ) : ℂ)‖ ≤ C * (g r)^(order+2))
    (hd : AppointedH140Through l d) (he : AppointedH140Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S' : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
    (p : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ᶠ r in trail, ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ K, ∀ y ∈ S',
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
      ∀ (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G e), Box u L → Box v L →
        ‖appointedH140Crop p (t r) (fullSeries A F (-Real.log T) hd he x y u v) -
            croppedResponse A F (-Real.log T) hh he y v p (t r) (croppedVector A h p u x (t r))‖ ≤
          C * ((T^(h+1))⁻¹ + (g r)^(p+1)) * (1+Real.log T)^k :=
  second Fph J N Z H ν (poseFit_coupling hG Fph J N t' order ht' hT) hd he hh K S' hK hx hS hy p L hL

open MeasureTheory
/-- Same uniform price against any finite signed or complex **joint** test, already
in `(x,y)` units (can program also via continuous positions with extra provenance X). -/
theorem second_test {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ht : Coupling G t) (hd : AppointedH140Through l d) (he : AppointedH140Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S' : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
    (p : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ᶠ r in trail, ∀ T : ℝ, T₀ ≤ T →
      ∀ (x:X→Points n) (y:X→Points m), Continuous x → Continuous y → (∀ i,x i∈K) → (∀ i,y i∈ S') →
      ∀ (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G e), Box u L → Box v L → ∀ μ: VectorMeasure X E,
      ∀ [IsFiniteMeasure μ.variation] (B : ℂ →L[ℝ] E →L[ℝ] ℂ),
      let Y := fun i=> appointedH140Crop p (t r) (fullSeries A F (-Real.log T) hd he (x i) (y i) u v)
      let D := fun i=> croppedResponse A F (-Real.log T) hh he (y i) v p (t r) (croppedVector A h p u (x i) (t r))
      μ.Integrable Y ∧ μ.Integrable D ∧ ‖(∫ᵛ i, Y i ∂[B; μ]) - (∫ᵛ i, D i ∂[B; μ])‖ ≤
          C * ((T^(h+1))⁻¹ + (g r)^(p+1)) * (1+Real.log T)^k * ‖B‖ * μ.variation.real univ := by
  obtain ⟨C,hC,k,T₀,hT₀,hp⟩:= second Fph J N Z H ν ht hd he hh K S' hK hx hS hy p L hL
  refine ⟨C,hC,k,T₀,hT₀,hp.mono ?_⟩
  intro r hr T hT x y hX hY hx' hy' u v hu hv μ Z' B
  apply test_formal (H.separatedOPE ν).wilson hd he hh hX hY μ B (fun i=> hx (hx' i))
    (fun i=>?clear) (fun i=>hy (hy' i)) u v p (t r)
    (fun i=> (hr T hT (x i) (hx' i) (y i) (hy' i)).2.2 u v hu hv)
  rw [squeeze, neg_neg, Real.exp_log (by linarith : 0 < T)]; exact (hr T hT (x i) (hx' i) (y i) (hy' i)).1
end YM.Integration.GradedFar
