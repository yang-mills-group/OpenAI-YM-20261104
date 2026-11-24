import YM.WilsonMS.Stencil.RootTensor
import YM.WilsonMS.Stencil.PureA
/-!
# Wilson dictionary under continuum test. Exact all-rank derivative in front
of `t` jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.PacketInk
open Function Filter Set MeasureTheory
open Analysis Tensor TPath Source Paths TaylorRules PlaneGauge Panel Extract MS Plane Heat Flux
open Landau Arts Pilot Tone Tone.Frame Local.BV Mach Motif Halo Native Cylinder Lab Draft
open Native.Sew Koszul Orient Book Land XSpace Webs Packet RGerm
open Complex (I)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [Fintype ι] (B : ι → PairK G) {H : Hol G} {n : ℕ} (K : Survey G H n)

abbrev edge (i : Wire K) :=
  site K i

def air (t : ℝ) (i : Wire K) :=
  travelV (edge K i) (t, 1 / 2)

def cloud (t : ℝ) : Inputs ι →L[ℝ] Lot G (Wire K) :=
  t • ContinuousLinearMap.pi (fun w => payload B (edge K w).2 (air K t w |>.2))

def diary (p : Labels.Pol G) (x : Lot G (Wire K)) :=
  Webs.reader K p (packetU K x)

lemma costs (p : Labels.Pol G) (y : ℝ × Inputs ι) :
    reader K p (coarse (trial B y.2) y.1) = diary K p (cloud B K y.1 y.2) := by
  rw [photographed K p]
  rfl

lemma price_line (p : QP) (e : Lattice.Edge Lattice.Cover) (t : ℝ) :
    Tone.bill (t • p) (Tone.embed e.1 + Tone.Frame.z e.2) = eip p (travelV e (t, 1 / 2) |>.2) := by
  have ht := Midpt.mid_pair (t • p) e.1 e.2
  rw [map_smul, real_inner_smul_left] at ht
  unfold Tone.bill eip travelV
  congr 2
  rw [ht, real_inner_smul_right]

def wordI (t : ℝ) (j : ι) :=
  Tone.Frame.waveForm (t • price B j) (B j).1 (B j).2.1

namespace FinitePacket
variable {ψ : Type} [Fintype ψ] (K : ψ → Lattice.Edge Lattice.Cover)

def air (t : ℝ) (i : ψ) :=
  travelV (K i) (t, 1 / 2)

def cloud (t : ℝ) : Inputs ι →L[ℝ] Lot G ψ :=
  t • ContinuousLinearMap.pi (fun w => payload B (K w).2 (air K t w |>.2))

omit [Fintype ψ] in
lemma cine (t : ℝ) (i : ι) (x : ψ × Conn G) :
    ((projector x (cloud B K t (cosine i)) : ℝ) : ℂ) +
        I * ((projector x (cloud B K t (sine i)) : ℝ) : ℂ) =
      ((t : ℝ) : ℂ) * paywave (wordI B t i) (knot K x) := by
  let v := K x.1
  let y := air K t x.1 |>.2
  have he (u : Inputs ι) : projector x (cloud B K t u) = t * ((trial B u v.2 y) x.2 : ℝ) :=
    projector_k _ _
  have hp :
    paywave (wordI B t i) (knot K x) =
      if h : (packet B i).1 = at_g (chair 0 v.2) x.2 then eip (price B i) y else 0 := by
    unfold knot wordI
    rw [please]
    unfold matchA
    simp_rw [price_line (_ : QP) (_ : Lattice.Edge Lattice.Cover)]
    by_cases ha : x.2 = (B i).2.1
    · rw [if_pos ha]
      split
      · rename_i hx
        rw [dif_pos ((gauge_tag B i _ _).mpr ⟨hx, ha.symm⟩).symm]
        rfl
      rename_i hx
      rw [dif_neg
          (Ne.symm (show at_g _ _ ≠ (packet B i).1 from fun c => hx ((gauge_tag B i _ _).mp c).1))]
    rw [if_neg ha,
      dif_neg
        (Ne.symm (show at_g _ _ ≠ (packet B i).1 from fun c => ha ((gauge_tag B i _ _).mp c).2.symm))]
  rw [he, he, hp]
  push_cast
  have hc := paid B i v.2 x.2 y
  split
  · rename_i h
    rw [if_pos h] at hc
    rw [← hc]
    ring
  rename_i h
  rw [if_neg h] at hc
  linear_combination ((t : ℂ)) * hc

open Cylinder.Taylor
variable [DecidableEq ψ]

def Report (t : ℝ) (l : List ι) (f : Lot G ψ → ℝ) :=
  Tone.run (art K f) (l.map (wordI B t))

lemma pen (t : ℝ) (l : List ι) {f : Lot G ψ → ℝ} (h : Smooth f) :
    scans cosine sine (fun u => (↑(f (cloud B K t u)) : ℂ)) l 0 =
      ((t : ℂ) ^ l.length) * Report B K t l f := by
  let L := cloud B K t
  induction l generalizing f with
  | nil =>
    simp only [List.length_nil, pow_zero, one_mul, scans, Report, List.map_nil]
    rw [map_zero]
    unfold Sew.art Tone.run
    rw [study, shade_nil]
    rfl
  | cons i l ih =>
    let w := wordI B t i
    let X := Lot G ψ
    let Ω (j : ψ × Conn G) : X → ℝ := layer (priv j) f
    have hΩ (j) : Smooth (Ω j) :=
      contDiff_iff_contDiffAt.mpr fun x => Analysis.dSmooth (h.contDiffAt (x := x)) _ (by simp)
    let T (j : ψ × Conn G) (u : Inputs ι) : ℂ := Ω j (L u)
    let C (j : ψ × Conn G) : ℂ := paywave w (knot K j)
    let v (u : Inputs ι) : ℂ := ↑(f (L u))
    have he : Extract.delta i cosine sine v = ∑ j : ψ × Conn G, ((t : ℂ) * C j) • T j := by
      funext z
      change
        Analysis.D _ v z + I * Analysis.D _ v z = (∑ j : ψ × Conn G, ((t : ℂ) * C j) • T j) z
      have ht (a : Inputs ι) : Analysis.D a v z = ↑(fderiv ℝ f (L z) (L a)) :=
        congr_arg (fun x : Inputs ι →L[ℝ] ℂ => x a)
          (Complex.ofRealCLM.hasFDerivAt.comp z
              (((h.differentiable (by simp) (L z)).hasFDerivAt.comp z L.hasFDerivAt))).fderiv
      rw [Finset.sum_apply, ht, ht]
      rw [← Native.frame (L (cosine i)), ← Native.frame (L (sine i)), map_sum, map_sum,
        Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply]
      unfold C w
      rw [← cine]
      rw [map_smul, map_smul]
      simp only [smul_eq_mul, Complex.ofReal_mul]
      change
        _ =
          ((↑(projector j (cloud _ _ _ _)) : ℂ) + I * ↑(projector j (cloud _ _ _ _))) *
            ↑(fderiv ℝ f _ _)
      unfold L
      ring
    have hz : Report B K t (i :: l) f = ∑ j : ψ × Conn G, C j * Report B K t l (Ω j) := by
      unfold Report Sew.art Tone.run
      simp only [List.map_cons]
      rw [study]
      let Q : Cyl (ψ × Conn G) ℂ := region.symm (ink priv f)
      rw [deriv_lum (fun i j => paywave i (knot K j)) (wordI B t i) Q
          (show Uses (↑(Finset.univ (α := ψ × Conn G)) : Set _) Q.val from by
            simp [Uses.entire])]
      apply Finset.sum_congr rfl
      intro j _
      rw [study]
      rfl
    rw [scans]
    change scans cosine sine (Extract.delta i cosine sine v) l 0 = _
    have hp (j : ψ × Conn G) : Smooth (T j) :=
      Complex.ofRealCLM.contDiff.comp ((hΩ j).comp L.contDiff)
    rw [hz, he,
      sc_sum (F := fun j => ((t : ℂ) * C j) • T j) (fun i _ => (hp i).const_smul ((t : ℂ) * C i)),
      Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [scale_s (hp j), Pi.smul_apply, show scans cosine sine (T j) l 0 = _ from ih (hΩ j),
      smul_eq_mul, List.length_cons, pow_succ]
    ring

end FinitePacket

lemma cine (t : ℝ) (i : ι) (x : Wire K × Conn G) :
    ((projector x (cloud B K t (cosine i)) : ℝ) : ℂ) +
        I * ((projector x (cloud B K t (sine i)) : ℝ) : ℂ) =
      ((t : ℝ) : ℂ) * paywave (wordI B t i) (knot (site K) x) :=
  FinitePacket.cine B (site K) t i x

def Report (t : ℝ) (l : List ι) (f : Lot G (Wire K) → ℝ) :=
  Tone.run (art (site K) f) (l.map (wordI B t))

lemma pen (t : ℝ) (l : List ι) {f : Lot G (Wire K) → ℝ} (h : Smooth f) :
    scans cosine sine (fun u => (↑(f (cloud B K t u)) : ℂ)) l 0 =
      ((t : ℂ) ^ l.length) * Report B K t l f := by
  change scans _ _ (fun u => (↑(f (FinitePacket.cloud B (site K) t u)) : ℂ)) _ _ = _
  exact FinitePacket.pen B (site K) t l h

lemma crystal (p : Labels.Pol G) (l : List ι) (t : ℝ) :
    scans cosine sine (fun z => reader K p (coarse (trial B z) t)) l 0 =
      (t : ℂ) ^ l.length * Tone.run (Webs.symbol K p) (l.map (wordI B t)) := by
  let L := cloud B K t
  let f : Lot G (Wire K) → ℂ := diary K p
  have he : Smooth f := (packet_smooth K p).of_le le_top
  let u : Lot G (Wire K) → ℝ := Complex.re ∘ f
  let v : Lot G (Wire K) → ℝ := Complex.im ∘ f
  have hu : Smooth u := Complex.reCLM.contDiff.comp he
  have hv : Smooth v := Complex.imCLM.contDiff.comp he
  let Q (z : Inputs ι) : ℂ := u (L z)
  let R (z : Inputs ι) : ℂ := v (L z)
  rw [show (fun z => reader K p (coarse (trial B z) t)) = Q + I • R from funext fun x => ?_]
  swap
  · rw [show reader K p (coarse _ _) = f (L x) from costs B K p (t, x)]
    simp only [Pi.smul_apply, Pi.add_apply, Q, R, v, u, Function.comp_apply, smul_eq_mul, mul_comm I]
    exact (Complex.re_add_im _).symm
  have hQ : Smooth Q := Complex.ofRealCLM.contDiff.comp (hu.comp L.contDiff)
  have hR : Smooth R := Complex.ofRealCLM.contDiff.comp (hv.comp L.contDiff)
  rw [sum2 (g := I • R) hQ (hR.const_smul I), scale_s hR, Pi.add_apply, Pi.smul_apply,
    show scans cosine sine Q l 0 = _ from pen B K _ _ hu,
    show scans cosine sine R l 0 = _ from pen B K _ _ hv]
  rw [show Webs.symbol K p = art (site K) u + I • art (site K) v from rfl, map_add, map_smul,
    Pi.add_apply, Pi.smul_apply]
  simp only [smul_eq_mul, Report]
  ring

lemma smoke (p : Labels.Pol G) :
    Smooth (fun x : ℝ × Inputs ι => reader K p (coarse (trial B x.2) x.1)) := by
  rw [funext (costs B K p)]
  refine
    ContDiff.comp (f := fun x : ℝ × Inputs ι => cloud B K x.1 x.2)
      (packet_smooth K p |>.of_le (m := ∞) le_top) ?_
  refine contDiff_pi.mpr fun i => ?_
  have ht : ContDiff ℝ ∞ (fun x : ℝ × Inputs ι => (air K x.1 i).2) :=
    contDiff_snd.comp
      (motion_smooth (e := edge K i) |>.comp (f := fun x : ℝ × Inputs ι => (x.1, (1 / 2 : ℝ)))
        (by fun_prop))
  exact
    contDiff_fst.smul
      ((trial_s B (edge K i).2).comp (f := fun x : ℝ × Inputs ι => ((air K x.1 i).2, x.2))
        (ht.prodMk contDiff_snd))

omit [Fintype ι] in
lemma smooth_ink (F : Dot G Lattice.Cover) (l : List ι) :
    Smooth (fun t : ℝ => Tone.run F (l.map (wordI B t))) := by
  induction l generalizing F with
  | nil => exact contDiff_const
  | cons i l ih =>
    obtain ⟨s, hs⟩ := obliges F
    let A : Landau.Branch G Axis := ((packet B i).1)
    simp only [List.map_cons]
    simp_rw [grows F hs]
    refine ContDiff.sum (fun j _ => ?_)
    exact (MS.Lifting.bankForm (price B i) (bornv (A, j))).mul (ih (enter (A, j) F))
end YM.WilsonMS.PacketInk
