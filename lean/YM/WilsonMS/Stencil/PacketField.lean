import YM.WilsonMS.Stencil.ComplexDirection
/-!
# Finite momentum catalogue

Use real cosine/sine copies per vertex argument. Used in proving the Fits-by-jets
condition in NonlinearFit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Packet
open Function Filter Set MeasureTheory
open Complex (I)
open Analysis Tensor TPath Source Paths TaylorRules PlaneGauge Panel Extract MS Plane Heat Flux
open Landau Arts Pilot Tone Local.BV Mach Motif Theater Halo Native Tone.Frame
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [Fintype ι]

abbrev PairK (G : Gauge) :=
  Axis × G.ColorIndex × QP

def vectorD (p : PairK G) : Shore G 0 :=
  (at_g (chair 0 p.1) p.2.1, p.2.2)

def quoteG (p : PairK G) : LightMode G QP :=
  waveForm p.2.2 p.1 p.2.1

lemma sameBill (p : PairK G) : quoteG p = (vectorD p : LightMode G QP) :=
  rfl
variable (B : ι → PairK G)

abbrev packet (i : ι) :=
  vectorD (B i)

abbrev price (i : ι) :=
  (B i).2.2

def eip (p : SectorP 0) (x : E4) :=
  Complex.exp (I * (↑(inner ℝ (fixF p) x) : ℂ))

lemma smooth_p (p : SectorP 0) : Smooth (eip p) :=
  (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (f := fun x : E4 => inner ℝ (fixF p) x)
        ((innerSL ℝ (fixF p)).contDiff))).cexp

@[simp]
lemma zero_p (p : SectorP 0) : eip p 0 = 1 := by simp [eip]

lemma mul_p (p q : SectorP 0) (x : E4) : eip (p + q) x = eip p x * eip q x := by
  unfold eip
  rw [map_add, inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma d_p (p : SectorP 0) (x : E4) (a : Axis) :
    Analysis.D (basis a) (eip p) x = eip p x * Motif.δ (chair 0 a) p := by
  let c := Motif.δ (chair 0 a) p
  let y (t : ℝ) := x + t • basis a
  have he : (fun t : ℝ => eip p (y t)) = fun t => eip p x * Complex.exp (((t : ℝ) : ℂ) * c) := by
    ext1 t
    unfold eip y
    rw [inner_add_right, real_inner_smul_right, lean_axis]
    push_cast
    rw [mul_add, Complex.exp_add]
    rw [show c = I * (p a : ℂ) from rfl]
    congr 2
    ring
  have hp : HasDerivAt (fun t : ℝ => ((t : ℂ) * c)) c 0 := by
    simpa using!
      (show HasDerivAt Complex.ofRealCLM (1 : ℂ) 0 from
            Complex.ofRealCLM.hasFDerivAt.hasDerivAt).mul_const
        c
  have ht : HasDerivAt (fun t : ℝ => eip p (y t)) (eip p x * c) 0 := by
    rw [he]
    simpa using! hp.cexp.const_mul (eip p x)
  have hz : y 0 = x := by simp [y]
  have hy : HasDerivAt y (basis a) 0 := by
    simpa only [one_smul, y] using! ((hasDerivAt_id' (0 : ℝ)).smul_const (basis a)).const_add x
  exact
    (((smooth_p p).differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt_of_eq _ hy hz.symm).unique
      ht

abbrev Inputs (ι : Type) :=
  (ι × Bool) → ℝ

def cosine (i : ι) : Inputs ι :=
  Pi.single (i, false) (1 : ℝ)

def sine (i : ι) : Inputs ι :=
  Pi.single (i, true) (1 : ℝ)

omit [Fintype ι] in
lemma gauge_tag (i : ι) (a : Axis) (c : G.ColorIndex) :
    at_g (chair 0 a) c = (packet B i).1 ↔ (B i).1 = a ∧ (B i).2.1 = c := by
  simp [at_g, packet, vectorD, chair, rises, eq_comm]

def rayPart (z : Inputs ι) (i : ι) (x : E4) :=
  z (i, false) * (eip (price B i) x).re + z (i, true) * (eip (price B i) x).im

def putA (m : Axis) (i : ι) : G.Color :=
  if m = (B i).1 then Theater.cl G (B i).2.1 else 0

def trial (z : Inputs ι) : VectorA G := fun m x => ∑ i : ι, rayPart B z i x • putA B m i

lemma trial_s (m : Axis) : Smooth (fun x : E4 × Inputs ι => trial B x.2 m x.1) := by
  unfold Smooth trial
  refine ContDiff.sum fun i _ => ?_
  unfold rayPart
  let R (z : E4 × Inputs ι) := eip (price B i) z.1
  have hR : Smooth R := (smooth_p _).comp contDiff_fst
  exact
    ((((contDiff_apply ℝ ℝ (i, false)).comp contDiff_snd).mul (Complex.reCLM.contDiff.comp hR)).add
          (((contDiff_apply ℝ ℝ (i, true)).comp contDiff_snd).mul
            (Complex.imCLM.contDiff.comp hR))).smul
      contDiff_const

lemma forever (z : Inputs ι) (m : Axis) : Smooth (trial B z m) :=
  (trial_s B m).comp (f := fun x : E4 => (x, z)) (contDiff_id.prodMk contDiff_const)

def payload (m : Axis) (x : E4) : Inputs ι →L[ℝ] G.Color :=
  LinearMap.toContinuousLinearMap
    { toFun z := trial B z m x
      map_add' p q := by
        unfold trial rayPart
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul]
        congr 1
        simp only [Pi.add_apply, add_mul]
        ring
      map_smul' t p := by
        unfold trial rayPart
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

lemma hits_real (i : ι) (m : Axis) (x : E4) :
    trial B (cosine i) m x = (eip (price B i) x).re • putA B m i := by
  unfold trial
  rw [Finset.sum_eq_single i]
  · simp [rayPart, cosine]
  · intro j _ h
    simp [rayPart, cosine, h]
  simp

lemma hits_imag (i : ι) (m : Axis) (x : E4) :
    trial B (sine i) m x = (eip (price B i) x).im • putA B m i := by
  unfold trial
  rw [Finset.sum_eq_single i]
  · simp [rayPart, sine]
  · intro j _ h
    simp [rayPart, sine, h]
  simp

lemma paid (i : ι) (m : Axis) (c : G.ColorIndex) (x : E4) :
    (((trial B (cosine i) m x) c : ℝ) : ℂ) + I * (((trial B (sine i) m x) c : ℝ) : ℂ) =
      if (packet B i).1 = at_g (chair 0 m) c then eip (price B i) x else 0 := by
  rw [hits_real, hits_imag]
  by_cases H : (packet B i).1 = at_g (chair 0 m) c
  · rw [if_pos H]
    obtain ⟨h, ht⟩ := (gauge_tag ..).mp H.symm
    simp [putA, h, ← ht, cl, mul_comm I]
  rw [if_neg H]
  by_cases h : (B i).1 = m
  · have hp : c ≠ (B i).2.1 := fun hh => H ((gauge_tag ..).mpr ⟨h, hh.symm⟩).symm
    simp [putA, h, hp, cl]
  simp [putA, Ne.symm h]
end YM.WilsonMS.Packet
