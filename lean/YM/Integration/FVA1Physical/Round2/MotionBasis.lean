import YM.Integration.FVA1Physical.Round2.VoiceProduct
import YM.Integration.FVA1Physical.Sources.Round2.BasisReadout

/-! Rebase an independently oriented, possibly conjugate physical
insertion onto the calibrated C18 basis at its original placement. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Finset Lattice RG YM.Wilson Source LocalLTE.Sail Extra.Histories Labels Next.Foundations
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} (H : History G) (N n : ℕ) (M : Motion)
    (o : ∀ j,Site (H.S.side j n)) (U : Config G (H.S.side N n))

def placedVoice (d : ℕ) : ((frames G).level d).Coeff →ₗ[ℂ] ℂ :=
  let P := localSection G d
  let ev := (MvPolynomial.aeval (entry (expandAt (o N) U))).toLinearMap
  (ev.comp P.evalC).comp (((frames G).level d).scaled (H.levels.clock.threshold N)⁻¹)

theorem primProbe_rebase (v : ((frames G).level d).Coeff) :
    primProbe H N n v M o U = placedVoice H N n o U d (Motion.patch _ M v) := by
  let a := (H.S.a N:ℂ)^d
  let θ := (H.levels.clock.threshold N)⁻¹
  let P := localSection G d
  let F := (frames G).level d
  have ha : a ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos _).ne')
  have inv : Motion.scalar M a⁻¹ = a⁻¹ := by
    unfold a
    rw [←Complex.ofReal_pow,←Complex.ofReal_inv,Motion.scalar_real]
  change a * Motion.scalar M (a⁻¹ * P.places (F.scaled θ v) 0 (pull M.1 (o N) U)) =
    P.places (F.scaled θ (Motion.patch F M v)) (o N) U
  rw [Motion.scalar_mul,inv,←mul_assoc,mul_inv_cancel₀ ha,one_mul,
    SectionData.placed_signed P (sound G d),←F.scaling]
  have z : affine M.1 (o N) 0 = o N := by simp [affine]
  rw [z]
  unfold Motion.scalar Motion.patch
  split
  · have flip (v : F.Coeff) : F.scaled θ (star v) = star (F.scaled θ v) := funext fun j=>by simp
    rw [flip]
    exact ((sound G d).ordinary_real _ _).symm
  rfl

theorem primProbe_basis (v : ((frames G).level d).Coeff) :
    primProbe H N n v M o U =
      ∑ j, (Motion.patch _ M v) j * primProbe H N n (Size.axis ((frames G).level d) j) Motion.nil o U := by
  let F := (frames G).level d
  let L := placedVoice H N n o U d
  have row (j : F.Index) : primProbe H N n (Size.axis F j) Motion.nil o U = L (Size.axis F j) := by
    rw [primProbe_rebase,Motion.patch_id]
  calc
    _ = L (Motion.patch F M v) := primProbe_rebase H N n M o U v
    _ = ∑ j, (Motion.patch F M v) j * L (Size.axis F j) := by
      have e := congrArg L (Size.sum_axes F (Motion.patch F M v))
      simpa only [map_sum,map_smul,smul_eq_mul] using e.symm
    _ = _ := sum_congr rfl fun j _=>congrArg ((Motion.patch F M v) j * ·) (row j).symm
end YM.Integration.FVA1Physical.Round2
