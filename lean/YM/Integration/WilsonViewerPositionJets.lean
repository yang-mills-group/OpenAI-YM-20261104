import YM.Integration.WilsonViewerRegulatedPanel

/-! Compact separated position jets of the same finite physical roster in every viewer. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set Finset MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)
    {n : ℕ} {d : Caps n}

private abbrev frames (R : Run G) (d : Caps n) := (i : Fin n) → Fin (Module.finrank ℂ (RG17.Free R.family (d i)))
private abbrev B (R : Run G) (k : ℕ) := Module.finBasis ℂ (RG17.Free R.family k)
private def symbols (k : frames R d) : MaxwellSlots R.family d := fun i => B R (d i) (k i)
private def weight (v : MaxwellSlots R.family d) (k : frames R d) : ℂ :=
  ∏ i, (B R (d i)).coord (k i) (v i)
private def cost (v : MaxwellSlots R.family d) : ℝ := ∑ k : frames R d, ‖weight v k‖

private theorem expanded {O : Type*} [AddCommMonoid O] [Module ℂ O]
    (T : MultilinearMap ℂ (fun i => RG17.Free R.family (d i)) O) (v : MaxwellSlots R.family d) :
    T v = ∑ k : frames R d, weight v k • T (symbols k) := by
  conv_lhs => rw [show v = fun i => ∑ k, ((B R (d i)).coord k (v i)) • B R (d i) k
    from funext fun i => ((B R (d i)).sum_repr (v i)).symm]
  rw [MultilinearMap.map_sum]
  exact Finset.sum_congr rfl fun k _ => T.map_smul_univ ..

local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z

include run in
/-- Each slot keeps its own cap, while its actual fitted coefficient may change with r. -/
theorem Selected.jets (v : MaxwellSlots R.family d) (j q : ℕ) (K : Set (Points n))
    (compact : IsCompact K) (separated : K ⊆ conf n) (temperature : Coupling G θ)
    {ε : ℝ} (ep : 0<ε) : ∀ᶠ r in trail, ∀ x∈K, ∀ p p' : Viewers F,
    ‖iteratedFDeriv ℝ j (measured F p (pub r) v r) x-
      iteratedFDeriv ℝ j (measured F p' (pub r) v r) x‖ ≤ ε*(θ r)^q := by
  obtain ⟨_,_,X,_,_,_⟩ := run.bliss.picks (fun i : ℕ => 1/((i:ℝ)+1))
    tendsto_one_div_add_atTop_nhds_zero_nat (fun i => by positivity)
  let w (r : ℝ) : MaxwellSlots R.family d := fun i => active F J Z r (d i) (v i)
  have ready : Tendsto w trail (𝓝 v) := tendsto_pi_nhds.mpr
    fun i => WilsonMacroscopicRichTwoDatePivot.field F J Z run.leading run.obeys simple (d i) (v i)
  have mc (i : Fin n) (k : frames R d) : Continuous
      (fun u : MaxwellSlots R.family d => (B R (d i)).coord (k i) (u i)) :=
    ((B R (d i)).coord (k i)).continuous_of_finiteDimensional.comp (continuous_apply i)
  have wc : Continuous (cost (R:=R) (d:=d)) := by unfold cost weight; fun_prop
  let a := cost v+1
  have ap : 0<a := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => norm_nonneg _) one_pos
  have fixed (k : frames R d) := Frame.negligible F Q J run.leading simple X run.foundation
    j (symbols k) K compact separated θ temperature (ε/a) (div_pos ep ap) q
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
  have each (k : frames R d) : ‖T (symbols k)‖ ≤ ε/a*(θ r)^q := by
    have bank_k := bank k x hx p p'
    rw [←Frame.jet_from_measure F p r (J r) (symbols k) j hx',
        ←Frame.jet_from_measure F p' r (J r) (symbols k) j hx'] at bank_k
    exact bank_k
  calc
    _ ≤ ∑ k : frames R d, ‖weight (w r) k • T (symbols k)‖ := norm_sum_le ..
    _ ≤ ∑ k : frames R d, ‖weight (w r) k‖ * (ε/a*(θ r)^q) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (each k) (norm_nonneg _)
    _ = cost (w r) * (ε/a*(θ r)^q) := by rw [cost,Finset.sum_mul]
    _ ≤ a * (ε/a*(θ r)^q) := mul_le_mul_of_nonneg_right limited
      (mul_nonneg (div_pos ep ap).le (pow_nonneg gp.le _))
    _ = _ := by field_simp [ap.ne']

end YM.Integration.WilsonViewerElectedHierarchy
end
