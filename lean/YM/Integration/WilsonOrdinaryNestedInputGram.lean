import YM.Integration.WilsonOrdinaryNestedOutput
import YM.Integration.WilsonPublicOutputFrame

/-! The whole physical reflected two-point at the actual zoom pays for the inverse
position frame, including its scalar and lower channels. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedInputGram
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom
open PhysMS Trace.Pilot GapsContact GapsContact.Seams GapsContact.Ascent
open Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (Z:WilsonPrescription G)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z


open Push.FiniteDetection.Free
open private two_sided pullGram at_one gram_at from YM.PhysMS.Frame.Step

include run in
theorem original (d:ℕ) : ∃ K:ℝ, 0<K ∧ ∀ᶠr in trail,∀y:S.Field d,
    ‖(pub r d).symm y‖^2 ≤ K * ‖OPE.Levy.pair d S (r • detectors) y (OPE.Levy.bar F d y)‖ := by
  obtain ⟨L,U,Lp,_,window⟩ := two_sided F d J run.leading
  refine ⟨4/L,by positivity,?_⟩
  filter_upwards [window 1 one_pos,run.leading.equivariant d,
    WilsonPublicOutputFrame.normalized F J Z run.leading run.obeys simple d] with r rr hr sale y
  let z := (J r d).symm y
  have test := (rr 1 (show (1:ℝ)∈Icc 1 1 from ⟨le_rfl,le_rfl⟩) z).1.1
  rw [pullGram,one_smul,at_one,gram_at,Frame.flip_coupled F d J r hr] at test
  change L*‖z‖^2 ≤ ‖OPE.Levy.pair d S (r • detectors) (J r d z) (OPE.Levy.bar F d (J r d z))‖ at test
  have yz : J r d z = y := LinearEquiv.apply_symm_apply .. 
  rw [yz] at test
  have p := pow_le_pow_left₀ (norm_nonneg _) (sale y) 2
  calc
    _ ≤ (2*‖z‖)^2 := p
    _ = (4/L)*(L*‖z‖^2) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left test (by positivity)
end YM.Integration.WilsonOrdinaryNestedInputGram
