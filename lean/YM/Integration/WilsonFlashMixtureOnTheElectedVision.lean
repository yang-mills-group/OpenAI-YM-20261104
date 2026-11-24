import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Paired
import YM.Integration.WilsonFlashShopOnTheElectedVision

noncomputable section
set_option autoImplicit false
namespace YM.Answer.ContinuumLimit.AppointedFlashRows

open Lattice RG Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus MS MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS
open OPE OPE.Orbits FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level SignedWilsonExpansion SignedWilsonExpansion.Belle
open SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Election.VaultM Election.VaultM.Till SignedWilsonExpansion.Homes SignedWilsonExpansion.Vault Vision
open Asymptotics Set PowerSeries FVA2.GradedFar259 FVA2.GradedFar259.Pose FVA2.GradedFar259.Comparing
open SignedWilsonExpansion.Belfry SignedWilsonExpansion.Belfry.ScaleFits SignedWilsonExpansion.Belfry.Classroom SignedWilsonExpansion.Dancer
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open FVA2.Dframe FVA2.O.Read
open scoped BigOperators Classical Topology Matrix

universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
  {E : Construction.{u} H ε e O} {ξ : Extraction.Order} (V : Vision E ξ)
  (Z : WilsonPrescription G) {dial : Bool} (Q : Perspective H Z dial)

private theorem leadingTab {ι : Type} (r σ : ι → ℝ) (d : ℕ) (i : ι) :
    Vision.tab Q V r false d σ 0 0 i = Level.Dial d (σ i) := by
  obtain ⟨h₁, h₂, h₃⟩ := Q.matching.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have base := GroupS.true_B 0 Z.scheme Z.criterion Q.MS _ H h₁ h₂ h₃ (σ i) (d := d)
  have one : Levy (GroupS.gaugeB Z.criterion Q.MS 0) (V.T Z ∘ r) σ 0 i d = 1 := by
    simpa [Levy, young, citeS, Tape.facet, coeff_zero_eq_constantCoeff_apply] using base.zero
  change Level.Dial d (σ i) * _ = _
  rw [one, mul_one]

include Q
theorem mixture (d : ℕ) : Quotes.Mixture V.pupil.last (V.Pre Z) Z d := by
  let L := Quotes.together
  have radius : Tendsto (Prod.fst : ℝ × ℝ → ℝ) L trail := tendsto_fst
  have bounded : ∀ᶠ i : ℝ × ℝ in L, i.2 ∈ Icc (1:ℝ) 2 :=
    tendsto_snd.eventually (mem_principal.mpr Subset.rfl)
  have clock := (measuredClock V Z Q).isBigO.comp_tendsto radius
  refine ⟨fun _ => 0, fun _ => 0, 0, V.T Z ∘ Prod.fst, ?_, ?_, clock, ?_⟩
  · simp
    exact tendsto_const_nhds
  · simp
    exact tendsto_const_nhds
  intro a b
  by_cases noRows : L = ⊥
  · apply IsBigO.of_bound 1
    change ∀ᶠ _ in L, _
    simp [noRows]
  letI : L.NeBot := ⟨noRows⟩
  let σ : Fin 2 → ℝ × ℝ → ℝ := ![fun i => -Real.log i.2, fun _ => 0]
  let u : ℝ × ℝ → Tags G d 2 := fun i => ![Level.Dial d (Real.log i.2) (theory a), prism (theory b)]
  have cost : ∀ j, FO L (σ j) := by
    intro j
    fin_cases j
    · apply by_abs (C := Real.log 2)
      filter_upwards [bounded] with i hi
      change |-(Real.log i.2)| ≤ Real.log 2
      rw [abs_neg, abs_of_nonneg (Real.log_nonneg hi.1)]
      exact Real.log_le_log (zero_lt_one.trans_le hi.1) hi.2
    · exact FO.const 0 L
  have salary : ∀ j, SeatsW.Salary ℂ L 1 (fun i => u i j) := by
    intro j f
    fin_cases j
    · apply IsBigO.of_bound ‖f (theory a)‖
      filter_upwards [bounded] with i hi
      change ‖f (Level.Dial d (Real.log i.2) (theory a))‖ ≤ _ * ‖(1:ℝ)‖
      rw [Level.exact₀, map_smul, norm_smul, norm_one, mul_one]
      apply mul_le_of_le_one_left (norm_nonneg _)
      simp only [Extent.token, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.log_nonneg hi.1)))
    · exact isBigO_const_const (f (prism (theory b))) (one_ne_zero : (1 : ℝ) ≠ 0) L
  let estimates := ((Appointment.pricesAll V).2 Z dial Q).estimates
  obtain ⟨C, _, hc⟩ := estimates.manyHomes 0 L Prod.fst radius {Quotes.paired_profile}
    ⟨isCompact_singleton, singleton_subset_iff.mpr Quotes.profile_space⟩ 0 σ u salary cost false
  apply IsBigO.trans _ clock
  apply IsBigO.of_bound C
  filter_upwards [hc, bounded] with i h hi
  have paid := h none Quotes.paired_profile (mem_singleton _)
  have tabs : (fun j => Vision.tab Q V Prod.fst false d (σ j) 0 0 i (u i j)) =
      ![theory a, prism (theory b)] := by
    funext j
    rw [leadingTab]
    fin_cases j
    · exact DFunLike.congr_fun (Level.spring (d := d) (Real.log i.2)) (theory a)
    · exact DFunLike.congr_fun (Level.flat (d := d)) (prism (theory b))
  have physical : Vision.lifeMany σ Z V false Prod.fst u none i Quotes.paired_profile =
      Quotes.team V.pupil.last (V.Pre Z) i.1 i.2 a b := by
    unfold Vision.lifeMany Quotes.team
    congr 1
    funext j
    fin_cases j
    · simp [σ, u, jump, Real.exp_log (zero_lt_one.trans_le hi.1), walk, slotW, Original.frame]
    · simp [σ, u, jump, walk, slotW, Original.frame]
  rw [physical, tabs] at paid
  simpa [Path.mote, Lamplight, array, stand, Function.comp_def] using paid

end YM.Answer.ContinuumLimit.AppointedFlashRows
