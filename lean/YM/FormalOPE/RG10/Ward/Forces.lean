import YM.FormalOPE.RG10.Ward.Meet
import YM.Wilson.Symmetry

/-! Euler gradients and locality before gating the orb Ward identity to the kframe geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric
open PertExtension PertExtension.Orb Function
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) (b : Edge (Site n))

def inversion : Signed := ⟨Equiv.refl _, fun _ => true⟩

lemma all_down (x : Site n) : affine inversion 0 x = -x := by unfold affine; rw [add_zero]; rfl
lemma all_reversed (k : Edge (Site n)) (U : Config G n) : pull inversion 0 U k = (U (Orb.reflect k))⁻¹ := by
  unfold pull; rw [all_down]; rfl

def retained (U : Config G n) := pull inversion 0 U=U
include hn in
lemma mirrors (A : Antes G n) : retained (liftLinks A) := by
  funext i
  rw [all_reversed, lift_flip hn,inv_inv]

private def both (a v : G.Color) (U : Config G n) (k : Edge (Site n)) := if k=b then G.lieExp a * U k
  else if k=Orb.reflect b then U k * (G.lieExp v)⁻¹ else U k
private lemma diagonal (U : Config G n) (a) : both b a a U = tilt b U a := rfl
private lemma single (U : Config G n) (a) : both b a 0 U = WardBin.slide b U a := by
  funext i; by_cases he:i=b <;> simp [both, he, WardBin.slide]
include hn in
private lemma only_mirror (U : Config G n) (h : retained U) (a) :
    both b 0 a U = pull inversion 0 (both b a 0 U) := by
  have hv (i : Edge (Site n)) : U i = (U (Orb.reflect i))⁻¹ := by rw [← all_reversed, h]
  funext i; rw [all_reversed]
  by_cases he:i=b
  · subst i; simp only [both, mat_lieExp_zero, if_neg (no_fixed_edge hn _), ↓reduceIte,
      one_mul, inv_one, mul_one]; exact hv _
  by_cases hi:i=Orb.reflect b
  · subst i; rw [reflect_reflect]
    simp only [both, if_neg he, ↓reduceIte, mul_inv_rev]
    conv_lhs => lhs; rw [hv,reflect_reflect]
  unfold both; rw [if_neg he, if_neg hi]
  have h₁ : Orb.reflect i ≠ b := fun h => hi (by rw [← h, reflect_reflect])
  rw [if_neg h₁]; split
  · rename_i h₁; exact False.elim (he (by simpa using congr_arg Orb.reflect h₁))
  exact hv _

private lemma jointly (U : Config G n) : ContDiff ℝ ∞ fun p:G.Color × G.Color => invoice (both b p.1 p.2 U) := by
  obtain ⟨A,h,hg⟩:= invoice_proxy (G:=G) (n:=n)
  rw [hg]; apply ContDiff.comp (g:=A) h
  apply contDiff_pi.mpr; intro i; unfold image both; split
  · simp only [mat_mul]; exact ((G.exp_jet.of_le le_top).comp contDiff_fst).mul contDiff_const
  split
  · simp only [mat_mul, mat_inv]
    exact contDiff_const.mul ((starL' ℝ).contDiff.comp ((G.exp_jet.of_le le_top).comp contDiff_snd))
  exact contDiff_const

private lemma projection (U : Config G n) (a : G.Color) :
    HasDerivAt (fun t : ℝ => invoice (both b (t • a) 0 U)) (⟪a, WardBin.euler U b⟫_ℝ / 2) 0 := by
  unfold invoice; simp_rw [single]; exact (WardBin.slide_energy ..).div_const _

include hn in
lemma twiceAt (U : Config G n) (h : retained U) (a : G.Color) :
    vary b invoice U a = ⟪a, WardBin.euler U b⟫_ℝ := by
  let I := fun p : G.Color × G.Color => invoice (both b p.1 p.2 U)
  let D := fderiv ℝ I 0
  have hi (p : G.Color×G.Color) : HasDerivAt (fun t : ℝ => I (t • p)) (D p) 0 :=
    (((jointly b U).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0
      (show HasDerivAt (fun t : ℝ => t • p) p 0 from by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const p) (by simp)
  have h1 : D (a,0) = ⟪a, WardBin.euler U b⟫_ℝ / 2 := (hi (a,0)).unique (by
    simp only [I, Prod.smul_fst,Prod.smul_snd,smul_zero]; exact projection b U a)
  have h2 : D (0,a) = ⟪a, WardBin.euler U b⟫_ℝ / 2 := (hi (0,a)).unique (by
    simp only [I, Prod.smul_fst,Prod.smul_snd,smul_zero];
    simp_rw [only_mirror hn b U h, invoice, energy_pull]; exact projection b U a)
  have hz := (show vary b invoice U a = D (a,a) from (invoice_proxy.derivative b U a).unique (hi (a,a)))
  rw [hz, show (a,a) = (a,0)+(0,a) by simp, map_add,h1,h2]; ring

include hn in
lemma agrees (U : Config G n) (h : retained U) (X : Config G n → G.Color) :
    effort b X U = ⟪X U,WardBin.euler U b⟫_ℝ := twiceAt hn b U h _

lemma force_unit : WardBin.euler (1:Config G n) b = 0 := by
  apply Finset.sum_eq_zero; intro i hi; simp [WardBin.wheel, oriented]

include hn in
lemma flat_effort (X : Config G n → G.Color) : effort b X 1=0 := by
  rw [agrees hn, force_unit, inner_zero_right]; funext i; rw [all_reversed]; simp

/-- Turn a torus-only variation into its orbit stencil when the mirror is outside the aperture of
reads. `exp`/transport in the spectator/contact calculation are otherwise retained rather than
silently replacing the orbit with a periodic array. -/
def avoids (s : Set (Site n)) := (Orb.reflect b).1∉s ∨ (Orb.reflect b).1 + step (Orb.reflect b).2∉s

variable {E : Type*} {s : Set (Site n)}
lemma tilt_isolated {X : Config G n → E} (h : LocalOn s X) (ha : avoids b s) (v) (U) :
    X (tilt b U v) = X (WardBin.slide b U v) := by
  apply h; intro k h₁ h₂
  by_cases h:k=b
  · subst k; simp [tilt, WardBin.slide]
  simp [tilt, WardBin.slide, h, push, show k ≠ Orb.reflect b from fun he => ha.elim (fun hv=> hv (he ▸ h₁)) (fun hv=> hv (he ▸ h₂))]

lemma singlyDiv {X : Config G n → G.Color} (h : LocalOn s X) (ha : avoids b s) (hz : Proxy X) (U) :
    fallout b X U = ∑ i : G.ColorIndex, WardBin.slope b (WardBin.dirs G i)
      (fun u => ⟪WardBin.dirs G i,X u⟫_ℝ) U := by
  rw [fallout_deriv b hz]; unfold WardBin.slope;
  apply Finset.sum_congr rfl; intro i _
  simp_rw [← tilt_isolated b h ha]
  exact (Proxy.deriv_eq _ (hz.after _ (innerSL ℝ (WardBin.dirs G i)).contDiff) _ _).symm
end YM.FormalOPE.RG10.InversionWard
