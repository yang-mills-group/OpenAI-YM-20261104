import YM.Integration.WilsonCenteredFiledGallery
import YM.Integration.FVA1Physical.Round2.CP5GalleryLog
import YM.UVNext.COUPLING_RESET.Probe

/-! Hear the centered product and the one filed counterterm on the actual
identity field. Their scalar survives normalization by the entire
unmarked Wilson packet. It is the zero-angle datum in the detector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureUnit
open Finset Lattice RG Wilson Marker QuadraticLocal Ac Extra.Trajectories Comparison.RG02.Cumulants
open FVA1Physical.Round2.CP5
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {P : Rep G n} {o : V → Site n}

def read (A : Gallery X ι o P R) (x : X) (s : R.Mode) (c : V) :=
  (P.eval (1:Config G n):ℂ)⁻¹ * ((A.density x 1).part s - (A.density x 1).part (R.fire c))

theorem normalized (A : Gallery X ι o P R) (x : X) (s : R.Mode) (c : V) :
    read A x s c = (Poly.pass (A.E.log x 1)).part s - (Poly.pass (A.E.log x 1)).part (R.fire c) := by
  have clear : flags P.p.threshold (1 : Config G n) = ∅ := UVNext.CouplingReset.flags_one P.p
  have vac : P.eval 1 = Real.exp (P.exponent 1) := by
    rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  have nz : (Real.exp (P.exponent 1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [read,Gallery.density,gallery_gas_one A x 1 clear,mul_one,Poly.part_smul,Poly.part_smul,vac]
  change _⁻¹ * (_ * _ - _ * _) = _
  rw [←mul_sub,←mul_assoc,inv_mul_cancel₀ nz,one_mul]

omit [Fintype V] in
theorem physicalDenominator : 0 < P.eval (1 : Config G n) := by
  have clear := UVNext.CouplingReset.flags_one (n:=n) (G:=G) P.p
  rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  exact Real.exp_pos _

variable (L : Lamps X ι G P.p o R) (D : Lamps X μ G P.p o R)
    (K : Hard X P.p P.activities.forced P.activities.K o R)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {α M δ : ℝ} (width : 0 ≤ α)
    (model : L.Paid w P.p.B α M) (debt : D.Paid w P.p.B α δ)
    (a b c : V) (s : R.Mode) (apart : a ≠ b) (pair : s.val = {a,b})

include hw width model debt apart pair

/-- The actual unit invoice includes the mixed face and the genuine
product of singleton means. The scalar of either input may be nonzero. -/
theorem paid (x : X) :
    let A : Gallery X (ι ⊕ μ) o P R := ⟨L.join D,K⟩
    let B : Gallery X ι o P R := ⟨L,K⟩
    let T := L.log x 1
    let E := D.log x 1
    let Z := Poly.pass T
    let Y := Poly.pass (T+E)
    let f := R.fire
    let ea := (w a)⁻¹*δ
    let eb := (w b)⁻¹*δ
    let za := (w a)⁻¹*M
    let yb := (w b)⁻¹*M+eb
    let soft := (Poly.toll w s)⁻¹*δ+(w c)⁻¹*δ+ea*yb+za*eb
    read A x s c - read B x s c =
        E.part s - E.part (f c) + E.part (f a)*Y.part (f b) + Z.part (f a)*E.part (f b) ∧
      ‖read A x s c - read B x s c‖ ≤ soft := by
  intro A B T E Z Y f ea eb za yb soft
  have raw := WilsonCenteredFiledGallery.original L D K w hw width model debt a b c s apart pair x (1:Config G n)
  have clear : flags P.p.threshold (1 : Config G n) = ∅ := UVNext.CouplingReset.flags_one P.p
  have vac : P.eval 1 = Real.exp (P.exponent 1) := by
    rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  have nz : (Real.exp (P.exponent 1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  change ((A.density x 1).part s - (A.density x 1).part (f c)) -
    ((B.density x 1).part s - (B.density x 1).part (f c)) = _ at raw
  rw [gallery_gas_one B x 1 clear] at raw
  have notEmpty (v : V) : R.fire v ≠ R.quiet := by
    intro he
    have eq := congrArg Subtype.val he
    change ({v} : Finset V) = ∅ at eq
    exact Finset.singleton_ne_empty _ eq
  simp only [Poly.one_part,if_true,if_neg (notEmpty a),if_neg (notEmpty b),
    one_mul,mul_zero,zero_mul,add_zero] at raw
  have exactValue : read A x s c-read B x s c =
      E.part s-E.part (f c)+E.part (f a)*Y.part (f b)+Z.part (f a)*E.part (f b) := by
    unfold read
    rw [←mul_sub,raw,vac,←mul_assoc,inv_mul_cancel₀ nz,one_mul]
  refine ⟨exactValue,exactValue ▸ ?_⟩
  exact WilsonCenteredFiledGallery.regular L D w hw width model debt a b c s pair x (1:Config G n)

end YM.Integration.WilsonCenteredCaptureUnit
