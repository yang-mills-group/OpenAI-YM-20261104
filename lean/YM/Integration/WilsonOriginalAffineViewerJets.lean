import YM.Integration.WilsonOriginalAffineShapeJets
import YM.Integration.WilsonOriginalHomogeneousShapeTensor
import YM.Integration.WilsonViewerPositionJets

/-! All appointed viewers on the same affine chart of the one physical hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAffineViewerJets
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)




open scoped ContDiff
local notation "pub" => homogeneous F J Z
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

include run in
theorem original {n m : ℕ} {d : Fin n → ℕ} (v : MaxwellSlots R.family d)
    (clock : Coupling G θ) (origin : Points n) (embed : (Fin m → ℝ) →L[ℝ] Points n)
    (K : Set (Fin m → ℝ)) (compact : IsCompact K)
    (clear : ∀ x ∈ K, origin+embed x ∈ conf n)
    (j q : ℕ) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ∀ p p' : Viewers F,
      ‖iteratedFDeriv ℝ j (fun z => measured F p (pub r) v r (origin+embed z)) x -
        iteratedFDeriv ℝ j (fun z => measured F p' (pub r) v r (origin+embed z)) x‖ ≤ ε*(θ r)^q := by
  let wallet := 1+‖embed‖^j
  have rich : 0 < wallet := add_pos_of_pos_of_nonneg one_pos (pow_nonneg (norm_nonneg _) _)
  have rates := run.jets Z v j q ((fun z => origin+embed z) '' K)
    (compact.image (continuous_const.add embed.continuous))
    (fun _ h => by obtain ⟨x,hx,rfl⟩ := h; exact clear x hx)
    clock (div_pos eps rich)
  have radial : ∀ᶠ r in trail, 0 < r := self_mem_nhdsWithin
  filter_upwards [rates,radial,clock.positive] with r rows hr hw x hx p p'
  have reg (vwr : Viewers F) : ContDiffOn ℝ j (measured F vwr (pub r) v r) (conf n) := by
    intro y hy
    have inc := (S.class_smooth _ (spectate F vwr).smooth (fun i=>⟨d i,pub r (d i) (v i)⟩)).contDiffAt
      ((conf_open n).mem_nhds (Work.A05.smul_conf hr hy))
    exact ((inc.comp y (contDiffAt_id.const_smul r)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
  rw [WilsonOriginalAffineShapeJets.original j _ (conf_open n) (reg p) origin embed (clear x hx),
    WilsonOriginalAffineShapeJets.original j _ (conf_open n) (reg p') origin embed (clear x hx)]
  let A := iteratedFDeriv ℝ j (measured F p (pub r) v r) (origin+embed x)
  let A' := iteratedFDeriv ℝ j (measured F p' (pub r) v r) (origin+embed x)
  change ‖A.compContinuousLinearMap _ - A'.compContinuousLinearMap _‖ ≤ _
  have eqn : (A-A').compContinuousLinearMap (fun _ => embed) =
      A.compContinuousLinearMap (fun _ => embed)-A'.compContinuousLinearMap (fun _ => embed) := by ext t; rfl
  rw [←eqn]
  have salary : ‖A-A'‖ ≤ ε/wallet*(θ r)^q := rows _ ⟨x,hx,rfl⟩ p p'
  calc
    _ ≤ ‖A-A'‖*∏ _ : Fin j, ‖embed‖ := (A-A').norm_compContinuousLinearMap_le _
    _ ≤ (ε/wallet*(θ r)^q)*wallet := by
      apply mul_le_mul salary _ (by positivity) (by positivity)
      simp [wallet]
    _ = ε*(θ r)^q := by field_simp

end YM.Integration.WilsonOriginalAffineViewerJets
