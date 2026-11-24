import YM.Integration.FVA1Physical.Wilson.BatchFields

/-! The signed microscopic insertion is real linear in the physical voice,
including orientation reversal. Each voice is read on a fixed, finite bank
of admissible real and imaginary basis insertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Lattice RG YM.Wilson Next.Foundations Source LocalLTE.Sail Extra.Histories Labels
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} (F : Frame G d)

abbrev VoiceAxis := F.Index × Bool

def axisVoice (i : VoiceAxis F) : F.Coeff := Pi.single i.1 (if i.2 then Complex.I else 1)

def axisWeight (v : F.Coeff) (i : VoiceAxis F) : ℝ := if i.2 then (v i.1).im else (v i.1).re

theorem voice_axes (v : F.Coeff) : ∑ i, axisWeight F v i • axisVoice F i = v := by
  funext j
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_apply,Pi.smul_apply,
    axisWeight,axisVoice,Bool.false_eq_true,↓reduceIte,Pi.single_apply,smul_ite,smul_zero]
  rw [Finset.sum_add_distrib]
  simp [Complex.real_smul, Complex.re_add_im, add_comm]

theorem axisWeight_bounded {v : F.Coeff} (hv : F.coeffSize v ≤ 1) (i : VoiceAxis F) :
    |axisWeight F v i| ≤ 1 := by
  have h : ‖v i.1‖ ≤ F.coeffSize v := Finset.single_le_sum (f:=fun j=>‖v j‖)
    (fun j _=>norm_nonneg _) (Finset.mem_univ i.1)
  unfold axisWeight
  split
  · exact (Complex.abs_im_le_norm _).trans (h.trans hv)
  exact (Complex.abs_re_le_norm _).trans (h.trans hv)

def motionLinear (M : Motion) : ℂ →ₗ[ℝ] ℂ :=
  if M.2 then (starL ℝ : ℂ ≃L[ℝ] ℂ).toLinearEquiv.toLinearMap else LinearMap.id

variable (H : History G) (N n : ℕ) (M : Motion) (o : ∀ j,Site (H.S.side j n))
  (U : Config G (H.S.side N n))

def voiceLinear : ((frames G).level d).Coeff →ₗ[ℝ] ℂ :=
  let P := localSection G d
  let a := (H.S.a N:ℂ)^d
  let eval := (MvPolynomial.aeval (entry (expandAt 0 (pull M.1 (o N) U)))).toLinearMap
  let read := (eval.comp P.evalC).comp (((frames G).level d).scaled (H.levels.clock.threshold N)⁻¹)
  (a • motionLinear M).comp ((a⁻¹ • read).restrictScalars ℝ)

theorem voiceLinear_read (v : ((frames G).level d).Coeff) :
    voiceLinear H N n M o U v = primProbe H N n v M o U := by
  change (H.S.a N:ℂ)^d * (motionLinear M _) = (H.S.a N:ℂ)^d * Motion.scalar M _
  unfold motionLinear Motion.scalar
  split <;> rfl

theorem wavelength_axes (v : ((frames G).level d).Coeff) :
    primProbe H N n v M o U = ∑ i, axisWeight ((frames G).level d) v i •
      primProbe H N n (axisVoice ((frames G).level d) i) M o U := by
  simp_rw [← voiceLinear_read]
  let L := voiceLinear H N n M o U (d:=d)
  have eqn := congrArg L (voice_axes ((frames G).level d) v)
  simpa only [map_sum,map_smul] using eqn.symm
end YM.Integration.FVA1Physical.Round2
