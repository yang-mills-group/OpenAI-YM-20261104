import YM.Integration.WilsonOrdinaryMarch
import YM.RG12.Roof.Layout

/-! The original RG12 free grading aligns with the physical moving frame and intertwines
its engineering dilation exactly. The scale conjugation therefore has the same resonant
diagonal on both the measured and the original free coefficient. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryEngineering
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryGradedShear
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "V" => Desk.Sector F.sector.derivatives d
local notation "X" => Col V

def chart : X ≃ₗ[ℂ] D := LinearEquiv.ofBijective (Roof.glint F d) (Roof.glinted F d)

theorem aligned (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (O : Prescription F.sector.derivatives) (coh : O.Coherent) : ∀ᶠ r in trail,
    triangular V ((Desk.official O coh d).symm.toLinearMap.comp ((chart F d).trans (J r d)).toLinearMap) := by
  let respects (r : ℝ) := ∀ (i : Grade d) (x : (Bel C.book).Field i.val),
    J r d ((Maxwell.Free.scheme C.labels).rise i.is_le x) = F.sector.derivatives.rise i.is_le (J r i x)
  have near : ∀ᶠ r in trail, respects r := eventually_all.mpr (fun i : Grade d => H.raised i.is_le)
  filter_upwards [near] with r hr
  apply Desk.compatible O coh d F.room.kernel.laws.toSymmetric F.phase.transport.injection
  intro i y
  change J r d (Roof.glint F d (put V i y)) ∈ _
  rw [Roof.listL]
  change J r d ((Maxwell.Free.scheme C.labels).rise i.is_le _) ∈ _
  rw [hr i]; exact LinearMap.mem_range_self _ _

theorem scale (s : ℝ) (x : X) : chart F d (dilate s x) = Pert.Scale.gear C.labels d s (chart F d x) :=
  Roof.dim F d s x

/-- An independently given free coefficient in the genuine original prescribed grade
coordinates. No choice is made at a physical radius. -/
def coefficient (U : Module.End ℂ D) : BlockMatrix V :=
  (chart F d).symm.toLinearMap.comp (U.comp (chart F d).toLinearMap)

/-- Engineering factors on the two ends of the actual adjacent physical step. -/
def scored : Module.End ℂ D →ₗ[ℂ] BlockMatrix V where
  toFun U := (dilate (Real.exp 1)⁻¹).comp ((coefficient F d U).comp (dilate (Real.exp 1)))
  map_add' _ _ := by apply LinearMap.ext; intro x; simp [coefficient]
  map_smul' _ _ := by apply LinearMap.ext; intro x; simp [coefficient]

theorem evaluated (U : Module.End ℂ D) (x : X) :
    scored F d U x = (chart F d).symm (Pert.Scale.gear C.labels d (Real.exp 1)⁻¹
      (U (chart F d (dilate (Real.exp 1) x)))) := by
  apply (chart F d).injective
  change chart F d (dilate (Real.exp 1)⁻¹ ((chart F d).symm _)) = _
  rw [scale,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rfl

private lemma scale_block (s : ℝ) (i : Grade d) (v : V i) :
    dilate s (put V i v) = ((s^i.val:ℝ):ℂ) • put V i v := by
  funext j; by_cases h : j=i
  · subst j; rfl
  · change ((s^j.val:ℝ):ℂ) • (Pi.single i v) j = ((s^i.val:ℝ):ℂ) • (Pi.single i v) j
    rw [Pi.single_eq_of_ne h]; simp

/-- The original fixed-ratio engineering conjugation preserves each resonant coefficient
exactly; hence native first-order parity may be spent on the unscaled free coefficient. -/
theorem diagonal (U : Module.End ℂ D) :
    diagonalMap V (scored F d U) = diagonalMap V (coefficient F d U) := by
  apply LinearMap.ext; intro x; funext i
  let s := Real.exp 1
  have hs : s ≠ 0 := (Real.exp_pos _).ne'
  change (dilate s⁻¹ ((coefficient F d U) (dilate s (put V i (x i))))) i =
    (coefficient F d U) (put V i (x i)) i
  rw [scale_block F d, map_smul, dilation, Pi.smul_apply, smul_smul]
  have unity : (((s⁻¹)^i.val:ℝ):ℂ) * ((s^i.val:ℝ):ℂ) = 1 := by
    norm_cast; rw [inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hs)]
  rw [unity,one_smul]

theorem tree : scored F d (LinearMap.id : Module.End ℂ D) = (LinearMap.id : BlockMatrix V) := by
  apply LinearMap.ext; intro x
  change dilate (Real.exp 1)⁻¹ ((chart F d).symm (chart F d (dilate (Real.exp 1) x)))=x
  rw [LinearEquiv.symm_apply_apply]; exact scale_cancel (Real.exp_pos _).ne' x

end YM.Integration.WilsonOrdinaryEngineering
