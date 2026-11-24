import YM.Integration.WilsonGraphUniformMixedShapeMass
import YM.Integration.WilsonPositionHomogeneousLeading
import YM.PhysMS.Frame.Phases
import YM.RG17.Aperture
import YangMills.WilsonProof.NativeSupport.IssuedBridge.WilsonQ198PostFrankValue
import YM.Integration.WilsonGraphAppointedStationaryPrices
import YM.Integration.WilsonQ198PhysicalPhaseWords

noncomputable section
namespace YM.Integration.WilsonQ198WithinPricePhaseMatrix

open YM YM.Integration YM.FVA2.Dframe YM.FVA2.O.Score

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open Integration.GradedFar.Tariff.Sunshine
open WilsonPositionHomogeneousComparison
open scoped Topology BigOperators Classical ContDiff

universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable (Z : WilsonPrescription g.core) (V : Vision E ξ) (Q : Perspective H Z true)
local notation "t" => V.T Z
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion




open YM.FVA2 YM.FVA2.Register YM.FVA2.Scale YM.FVA2.Scale.Level

theorem prePrice (Z : WilsonPrescription g.core) (V : Vision E ξ)
    (Q : Perspective H Z true) {n : ℕ} (d : Fin n → ℕ) (K : Set (Points n))
    (compact : IsCompact K) (safe : K ⊆ conf n) (a : ℝ) (ha : a < 4) (j : ℕ)
    (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i)) :
    ∀ᶠ r : ℝ in Trace.Pilot.trail, ∀ x ∈ K, ∀ p q : OPE.Viewers V.pupil.last,
      ‖iteratedFDeriv ℝ j (PhysMS.measured V.pupil.last p (V.Pre Z r)
          (fun i => (Maxwell.Free.fields E.paths.family.labels (d i)).symm (v i)) r) x -
        iteratedFDeriv ℝ j (PhysMS.measured V.pupil.last q (V.Pre Z r)
          (fun i => (Maxwell.Free.fields E.paths.family.labels (d i)).symm (v i)) r) x‖ ≤ r ^ a := by
  obtain ⟨M, η, hM, hη, room⟩ := RG17.Profile.finite_venue compact safe
  have price := PhysMS.Frame.within_price V.pupil.last V.pupil.P (V.Pre Z)
    (V.certificate Q).leading H V.sc V.pupil.foundation M η (4-a) j
    (fun i => (Maxwell.Free.fields E.paths.family.labels (d i)).symm (v i))
    (sub_pos.mpr ha) hM hη
  filter_upwards [price] with r paid
  intro x hx p q
  simpa only [sub_sub_cancel] using paid x (room x hx) p q

/-- The actual input to the preframe at this radius, on the filed Maxwell sector. -/
def inputChange (Z : WilsonPrescription g.core) (V : Vision E ξ) (r : ℝ) (d : ℕ)
    (u : (YangMills.maxwellReference g).sector d) : (YangMills.maxwellReference g).sector d :=
  (Maxwell.Free.fields E.paths.family.labels d)
    (WilsonPositionHomogeneousFrame.change V.pupil.last V.pupil.J Z d r
      ((Maxwell.Free.fields E.paths.family.labels d).symm u))

theorem postSlot (Z : WilsonPrescription g.core) (V : Vision E ξ) (r : ℝ) (d : ℕ)
    (u : (YangMills.maxwellReference g).sector d) :
    V.Post Z r d ((Maxwell.Free.fields E.paths.family.labels d).symm u) =
      V.Pre Z r d ((Maxwell.Free.fields E.paths.family.labels d).symm (inputChange Z V r d u)) := by
  simp only [inputChange, LinearEquiv.symm_apply_apply]
  rfl


open YM.FVA2.GradedFar
open YM.Integration.WilsonGraphUniformMixedShapeMass

/-- Every matrix entry of the filed homogeneous change is continuous on the
physical finite-dimensional source of the field. -/
theorem coordinateChangeTends (Z : WilsonPrescription g.core) (V : Vision E ξ)
    (d : ℕ) (u : (YangMills.maxwellReference g).sector d) (i : Toon g.core d) :
    Tendsto (fun r => coord i (inputChange Z V r d u)) Trace.Pilot.trail (𝓝 (coord i u)) := by
  let T := Maxwell.Free.fields E.paths.family.labels d
  let L := (coord i).comp T.toLinearMap
  have cont : Continuous L := L.continuous_of_finiteDimensional
  have moved := WilsonPositionHomogeneousLeading.moved V.pupil.last V.pupil.J Z
    V.pupil.VFrame.2 V.pupil.VFrame.1 H d (T.symm u)
  have atSource := (cont.tendsto (T.symm u)).comp moved
  change Tendsto (fun r => coord i (inputChange Z V r d u)) Trace.Pilot.trail
    (𝓝 (coord i (T (T.symm u)))) at atSource
  simpa only [LinearEquiv.apply_symm_apply] using atSource

/-- There is one bound for every entry of the mixed input change,
before the radius and both basis indices. -/
theorem matrixBound (Z : WilsonPrescription g.core) (V : Vision E ξ)
    {n : ℕ} (d : Fin n → ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r in Trace.Pilot.trail, ∀ σ τ : Picks g.core d,
      ‖multipliers (fun i => inputChange Z V r (d i) (basisWord σ i)) τ‖ ≤ B := by
  classical
  let cap (σ τ : Picks g.core d) (i : Fin n) := ‖coord (τ i) (basisWord σ i)‖ + 1
  let B := ∑ σ : Picks g.core d, ∑ τ : Picks g.core d, ∏ i, cap σ τ i
  have hc (σ τ : Picks g.core d) (i : Fin n) : 0 ≤ cap σ τ i := by dsimp [cap]; positivity
  refine ⟨B, Finset.sum_nonneg (fun σ _ => Finset.sum_nonneg (fun τ _ =>
    Finset.prod_nonneg (fun i _ => hc σ τ i))), ?_⟩
  have entries (σ τ : Picks g.core d) (i : Fin n) : ∀ᶠ r in Trace.Pilot.trail,
      ‖coord (τ i) (inputChange Z V r (d i) (basisWord σ i))‖ ≤ cap σ τ i := by
    exact ((coordinateChangeTends Z V (d i) (basisWord σ i) (τ i)).norm.eventually
      (ge_mem_nhds (show ‖coord (τ i) (basisWord σ i)‖ < cap σ τ i by dsimp [cap]; linarith)))
  have all : ∀ᶠ r in Trace.Pilot.trail, ∀ σ τ : Picks g.core d, ∀ i : Fin n,
      ‖coord (τ i) (inputChange Z V r (d i) (basisWord σ i))‖ ≤ cap σ τ i :=
    Filter.eventually_all.mpr fun σ => Filter.eventually_all.mpr fun τ =>
      Filter.eventually_all.mpr (entries σ τ)
  filter_upwards [all] with r hr
  intro σ τ
  rw [multipliers, norm_prod]
  exact (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hr σ τ i)).trans
    ((Finset.single_le_sum (fun τ _ => Finset.prod_nonneg (fun i _ => hc σ τ i))
      (Finset.mem_univ τ)).trans (Finset.single_le_sum (fun σ _ => Finset.sum_nonneg
        (fun τ _ => Finset.prod_nonneg (fun i _ => hc σ τ i))) (Finset.mem_univ σ)))

/-- Finite Maxwell expansion commutes with the full Fréchet derivative. -/
theorem basisJet {G : Gauge} {C : Family G} {S : Table C.book}
    {e : Extraction.Order} {n : ℕ} {d : Fin n → ℕ} (F : Final C e S)
    (P : ℝ → tower S) (viewer : Viewers F) (o : E4) (r : ℝ) (j : ℕ)
    (x : Points n) (v : Inputs G d)
    (smooth : ∀ τ : Picks G d, ContDiffAt ℝ j
      (fun y => TrueCompact F P viewer r o y (basisWord τ)) x) :
    iteratedFDeriv ℝ j (fun y => TrueCompact F P viewer r o y v) x =
      ∑ τ : Picks G d, multipliers v τ •
        iteratedFDeriv ℝ j (fun y => TrueCompact F P viewer r o y (basisWord τ)) x := by
  classical
  have expand : (fun y => TrueCompact F P viewer r o y v) =
      (fun y => ∑ τ : Picks G d, multipliers v τ • TrueCompact F P viewer r o y (basisWord τ)) :=
    funext fun y => by simpa only [smul_eq_mul] using fieldExpansion F P viewer o r y v
  rw [expand]
  have weighted (τ : Picks G d) : ContDiffAt ℝ j
      (fun y => multipliers v τ • TrueCompact F P viewer r o y (basisWord τ)) x :=
    (contDiffAt_const : ContDiffAt ℝ j (fun _ : Points n => multipliers v τ) x).smul (smooth τ)
  rw [iteratedFDeriv_fun_sum_apply (u := Finset.univ)
    (f := fun (τ : Picks G d) (y : Points n) =>
      multipliers v τ • TrueCompact F P viewer r o y (basisWord τ))
    (fun τ _ => weighted τ)]
  apply Finset.sum_congr rfl
  intro τ _
  exact iteratedFDeriv_const_smul_apply' (smooth τ)

/-- A common coefficient on both viewers preserves the signed derivative
difference in its original operator norm. -/
theorem signedOperatorSum {ι A : Type*} [Fintype ι] [SeminormedAddCommGroup A]
    [NormedSpace ℂ A] (w : ι → ℂ) (p q : ι → A) (M e : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, ‖w i‖ ≤ M) (he : ∀ i, ‖p i - q i‖ ≤ e) :
    ‖(∑ i, w i • p i) - ∑ i, w i • q i‖ ≤ (Fintype.card ι : ℝ) * M * e := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    ‖∑ i, w i • (p i-q i)‖ ≤ ∑ i, ‖w i • (p i-q i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, M * e := Finset.sum_le_sum fun i _ =>
      (norm_smul_le _ _).trans (mul_le_mul (hw i) (he i) (norm_nonneg _) hM)
    _ = (Fintype.card ι : ℝ) * M * e := by simp [nsmul_eq_mul, mul_assoc]


open YM.Integration.GradedFar.Tariff YM.FVA2.GradedFar YM.Trace.Pilot
open YM.Integration.WilsonGraphUniformMixedShapeMass

theorem compactSmooth {G : Gauge} {C : Family G} {S : Table C.book}
    {e : Extraction.Order} {n : ℕ} (F : Final C e S) (A : ℝ → tower S) (viewer : Viewers F)
    (d : Fin n → ℕ) (w : Inputs G d) (o : E4) {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ ∞ (fun y => TrueCompact F A viewer r o y w) (conf n) := by
  apply (kernel_smooth F viewer hr (fun i => ⟨d i, labels A r w i⟩)).congr
  intro y hy
  exact (atTable_within F A viewer d w o hr hy).symm

theorem preBasisAtCentres (Z : WilsonPrescription g.core) (V : Vision E ξ)
    (Q : Perspective H Z true) {n : ℕ} (d : Fin n → ℕ) (K : Set (Points n))
    (compact : IsCompact K) (safe : K ⊆ conf n) (a : ℝ) (ha : a < 4) (j : ℕ) :
    ∀ᶠ r in trail, ∀ (σ : Picks g.core d) (o : E4) (x : Points n), x ∈ K → ∀
        (viewer other : Viewers V.pupil.last),
      ‖iteratedFDeriv ℝ j (fun y => TrueCompact V.pupil.last (V.Pre Z) viewer r o y (basisWord σ)) x -
       iteratedFDeriv ℝ j (fun y => TrueCompact V.pupil.last (V.Pre Z) other r o y (basisWord σ)) x‖ ≤
       r ^ a := by
  classical
  have all := Filter.eventually_all.mpr (fun σ : Picks g.core d =>
    prePrice Z V Q d K compact safe a ha j (basisWord σ))
  filter_upwards [all, (show ∀ᶠ r : ℝ in trail, 0 < r from self_mem_nhdsWithin)]
    with r bound hr σ o x hx viewer other
  have neighborhood := (conf_open n).mem_nhds (safe hx)
  have physical (ν : Viewers V.pupil.last) :
      (fun y => YM.PhysMS.measured V.pupil.last ν (V.Pre Z r)
        (fun i => (Maxwell.Free.fields E.paths.family.labels (d i)).symm (basisWord σ i)) r y) =ᶠ[𝓝 x]
      (fun y => TrueCompact V.pupil.last (V.Pre Z) ν r o y (basisWord σ)) := by
    filter_upwards [neighborhood] with y hy
    exact atTable_within V.pupil.last (V.Pre Z) ν d (basisWord σ) o hr hy
  rw [← ((physical viewer).iteratedFDeriv ℝ j).eq_of_nhds,
    ← ((physical other).iteratedFDeriv ℝ j).eq_of_nhds]
  exact bound σ x hx viewer other

theorem original (Z : WilsonPrescription g.core) (V : Vision E ξ)
    (Q : Perspective H Z true) {n : ℕ} (d : Fin n → ℕ) (K : Set (Points n))
    (compact : IsCompact K) (safe : K ⊆ conf n) (a : ℝ) (ha : a < 4) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in trail, ∀ (o : E4) (x : Points n), x ∈ K → ∀
        (viewer other : Viewers V.pupil.last) (v : Inputs g.core d),
      ‖iteratedFDeriv ℝ j (fun y => TrueCompact V.pupil.last (V.Post Z) viewer r o y v) x -
       iteratedFDeriv ℝ j (fun y => TrueCompact V.pupil.last (V.Post Z) other r o y v) x‖ ≤
       C * r ^ a * inputMass g v := by
  classical
  let I := Picks g.core d
  let N : ℝ := Fintype.card I
  have hN : 0 ≤ N := Nat.cast_nonneg _
  obtain ⟨D, hD, hd⟩ := multipliersMass g d
  obtain ⟨B, hB, hb⟩ := matrixBound Z V d
  refine ⟨N * N * D * B, by positivity, ?_⟩
  filter_upwards [hb, preBasisAtCentres Z V Q d K compact safe a ha j,
    (show ∀ᶠ r : ℝ in trail, 0 < r from self_mem_nhdsWithin)] with r mat pre hr o x hx viewer other v
  let moved (σ : I) : Inputs g.core d := fun i => inputChange Z V r (d i) (basisWord σ i)
  let jet (A : ℝ → tower V.pupil.S) (ν : Viewers V.pupil.last) (w : Inputs g.core d) :=
    iteratedFDeriv ℝ j (fun y => TrueCompact V.pupil.last A ν r o y w) x
  have hpre (σ : I) : ‖jet (V.Pre Z) viewer (basisWord σ) -
      jet (V.Pre Z) other (basisWord σ)‖ ≤ r ^ a := pre σ o x hx viewer other
  have expand (A : ℝ → tower V.pupil.S) (ν : Viewers V.pupil.last) (w : Inputs g.core d) :
      jet A ν w = ∑ σ : I, multipliers w σ • jet A ν (basisWord σ) := by
    unfold jet
    apply basisJet
    intro σ
    exact ((compactSmooth V.pupil.last A ν d (basisWord σ) o hr).contDiffAt
      ((conf_open n).mem_nhds (safe hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have reframe (ν : Viewers V.pupil.last) (σ : I) :
      jet (V.Post Z) ν (basisWord σ) = jet (V.Pre Z) ν (moved σ) := by
    unfold jet
    congr 1
    funext y
    unfold TrueCompact
    congr 1
    funext i
    exact postSlot Z V r (d i) (basisWord σ i)
  have basis (σ : I) : ‖jet (V.Post Z) viewer (basisWord σ) -
      jet (V.Post Z) other (basisWord σ)‖ ≤ N * B * r ^ a := by
    rw [reframe viewer σ, reframe other σ, expand _ viewer, expand _ other]
    apply signedOperatorSum
    · exact hB
    · exact mat σ
    · exact hpre
  change ‖jet (V.Post Z) viewer v - jet (V.Post Z) other v‖ ≤ _
  rw [expand _ viewer, expand _ other]
  calc
    _ ≤ N * (D * inputMass g v) * (N * B * r ^ a) := by
      apply signedOperatorSum
      · apply mul_nonneg hD
        unfold inputMass
        exact Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
      · exact hd v
      · exact basis
    _ = _ := by ring

end YM.Integration.WilsonQ198WithinPricePhaseMatrix


