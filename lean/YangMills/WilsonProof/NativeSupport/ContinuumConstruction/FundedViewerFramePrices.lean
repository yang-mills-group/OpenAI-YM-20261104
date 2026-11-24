import YM.Integration.WilsonViewerPositionJets
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set Finset MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (bliss : Bliss F ℓ arch Y) (leading : Leading F J)
    (obeys : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (foundation : OPE.Orbits.Foundation F Q)
    (Z : WilsonPrescription G)
    {n : ℕ} {d : Caps n}

open private frames B symbols weight cost expanded from YM.Integration.WilsonViewerPositionJets
local notation "pub" => homogeneous F J Z

include simple bliss leading obeys foundation in
/-- Each slot keeps its own cap, while its actual fitted coefficient may change with r. -/
theorem fundedViewerPrice (v : MaxwellSlots R.family d) (j q : ℕ) (K : Set (Points n))
    (compact : IsCompact K) (separated : K ⊆ conf n) (meter : ℝ → ℝ) (temperature : Coupling G meter)
    {ε : ℝ} (ep : 0<ε) : ∀ᶠ r in trail, ∀ x∈K, ∀ p p' : Viewers F,
    ‖iteratedFDeriv ℝ j (measured F p (pub r) v r) x-
      iteratedFDeriv ℝ j (measured F p' (pub r) v r) x‖ ≤ ε*(meter r)^q := by
  obtain ⟨_,_,X,_,_,_⟩ := bliss.picks (fun i : ℕ => 1/((i:ℝ)+1))
    tendsto_one_div_add_atTop_nhds_zero_nat (fun i => by positivity)
  let w (r : ℝ) : MaxwellSlots R.family d := fun i => active F J Z r (d i) (v i)
  have ready : Tendsto w trail (𝓝 v) := tendsto_pi_nhds.mpr
    fun i => WilsonMacroscopicRichTwoDatePivot.field F J Z leading obeys simple (d i) (v i)
  have mc (i : Fin n) (k : frames R d) : Continuous
      (fun u : MaxwellSlots R.family d => (B R (d i)).coord (k i) (u i)) :=
    ((B R (d i)).coord (k i)).continuous_of_finiteDimensional.comp (continuous_apply i)
  have wc : Continuous (cost (R:=R) (d:=d)) := by unfold cost weight; fun_prop
  let a := cost v+1
  have ap : 0<a := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => norm_nonneg _) one_pos
  have fixed (k : frames R d) := Frame.negligible F Q J leading simple X foundation
    j (symbols k) K compact separated meter temperature (ε/a) (div_pos ep ap) q
  filter_upwards [eventually_all.mpr fixed, ((wc.tendsto v).comp ready).eventually
    (ge_mem_nhds (show cost v<a by dsimp [a]; linarith)),temperature.positive,RG17.positiveLength]
    with r bank limited gp rp x hx p p'
  have hx' := Work.A05.smul_conf rp (separated hx)
  let T := ((Frame.jet F j p d r x)-(Frame.jet F j p' d r x)).compLinearMap
    (fun i => (J r (d i)).toLinearMap)
  have later : T (w r) = iteratedFDeriv ℝ j (measured F p (pub r) v r) x-
      iteratedFDeriv ℝ j (measured F p' (pub r) v r) x := by
    rw [←Frame.jet_from_measure F p r (pub r) v j hx',←Frame.jet_from_measure F p' r (pub r) v j hx']
    change Frame.jet F j p d r x (fun i=> J r (d i) ((J r (d i)).symm _))-
        Frame.jet F j p' d r x (fun i=> J r (d i) ((J r (d i)).symm _))=_
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  rw [←later,expanded T]
  have each (k : frames R d) : ‖T (symbols k)‖ ≤ ε/a*(meter r)^q := by
    have bank_k := bank k x hx p p'
    rw [←Frame.jet_from_measure F p r (J r) (symbols k) j hx',
        ←Frame.jet_from_measure F p' r (J r) (symbols k) j hx'] at bank_k
    exact bank_k
  calc
    _ ≤ ∑ k : frames R d, ‖weight (w r) k • T (symbols k)‖ := norm_sum_le ..
    _ ≤ ∑ k : frames R d, ‖weight (w r) k‖ * (ε/a*(meter r)^q) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (each k) (norm_nonneg _)
    _ = cost (w r) * (ε/a*(meter r)^q) := by rw [cost,Finset.sum_mul]
    _ ≤ a * (ε/a*(meter r)^q) := mul_le_mul_of_nonneg_right limited
      (mul_nonneg (div_pos ep ap).le (pow_nonneg gp.le _))
    _ = _ := by field_simp [ap.ne']


include simple bliss leading obeys foundation in
theorem fundedViewerZero
    (v : MaxwellSlots R.family d) (j : ℕ) (K : Set (Points n))
    (compact : IsCompact K) (separated : K ⊆ conf n) (ε : ℝ) (positive : 0 < ε)
    (meter : ℝ → ℝ) (temperature : Coupling G meter) :
    ∀ᶠ r in trail, ∀ x ∈ K, ∀ p : Viewers F,
      ‖iteratedFDeriv ℝ j (measured F p (pub r) v r) x - iteratedFDeriv ℝ j (WickGoal v) x‖ < ε := by
  have third : 0 < ε/3 := by positivity
  have relative := fundedViewerPrice (simple := simple) bliss leading obeys foundation Z v j 0 K compact separated meter temperature third
  have mean := WilsonPositionHomogeneousLeading.jets F J Z leading obeys simple d v j
    compact separated third
  filter_upwards [relative,mean] with r measuredRows center x hx p
  have comparison := measuredRows x hx p none
  simp only [pow_zero,mul_one] at comparison
  have origin := center x hx
  change ‖iteratedFDeriv ℝ j (measured F none (pub r) v r) x - iteratedFDeriv ℝ j (WickGoal v) x‖ ≤ ε/3 at origin
  exact (norm_sub_le_norm_sub_add_norm_sub _ (iteratedFDeriv ℝ j (measured F none (pub r) v r) x) _).trans_lt
    (lt_of_le_of_lt (add_le_add comparison origin) (by linarith))

end YM.Integration.WilsonViewerElectedHierarchy

end
