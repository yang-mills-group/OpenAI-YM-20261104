import YM.FormalOPE.RG10.Ward.Pair
import YM.PertExtension.Normalized
import YM.Source.Local

/-!
# All finite even mirror derivatives of lattice PT cylinder inputs

Keep matrix representatives near the orbit so that the contact versions are defined. These aren't
limits! We work with ordinary observables (real and complex) and true commutative derivative
identities only on physical even-gauge objects. A Gaussian-only integration by parts would not
prove the normalization used by this prescription.
-/
set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric
open PertExtension PertExtension.Orb Function Source
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {n : Side}
abbrev ArrayOf (G : Gauge) (n : Side) := Edge (Site n) → G.Mat

def image (U : Config G n) : ArrayOf G n := fun k => G.mat (U k)
@[fun_prop] lemma cont_image : Continuous (image (G:=G) (n:=n)) := continuous_pi fun _ => by unfold image; fun_prop
lemma contdiff_image : ContDiff ℝ ∞ (image (G:=G) ∘ representative (n:=n)) := by
  apply contDiff_pi.mpr
  exact fun k => (matrix_smooth k).of_le le_top

variable {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    {f g : Config G n → E}

/-- All-matrix-space test (sufficient, not necessary, for formal Ward uses). Holds in
particular without requiring any differentiability proof in a moving tree/gauge system. -/
def Proxy (f : Config G n → E) := ∃ F : ArrayOf G n → E, ContDiff ℝ ∞ F ∧ f = F ∘ image

namespace Proxy
lemma cont (h : Proxy f) : Continuous f := by obtain ⟨a,ha,rfl⟩:=h; exact ha.continuous.comp cont_image
lemma after (h : Proxy f) (A : E → L) (hA : ContDiff ℝ ∞ A) : Proxy fun U => A (f U) := by
  obtain ⟨a,ha,rfl⟩:=h; exact ⟨A ∘ a,hA.comp ha,rfl⟩
lemma pair (h : Proxy f) {φ : Config G n → L} (ha : Proxy φ) : Proxy fun U => (f U, φ U) := by
  obtain ⟨a,ha',rfl⟩:=ha; obtain ⟨b,hb,rfl⟩:=h; exact ⟨fun x => (b x,a x),hb.prodMk ha',rfl⟩
lemma const (x : E) : Proxy (fun _ : Config G n => x) := ⟨_,contDiff_const,rfl⟩
lemma add (h : Proxy f) (k : Proxy g) : Proxy (f+g) := (h.pair k).after _ (contDiff_fst.add contDiff_snd)
lemma sub (h : Proxy f) (k : Proxy g) : Proxy (f-g) := (h.pair k).after _ (contDiff_fst.sub contDiff_snd)
lemma mul {K : Type*} [NormedRing K] [NormedAlgebra ℝ K] {f g : Config G n → K} (h : Proxy f) (k : Proxy g) :
    Proxy (f*g) := (h.pair k).after _ (contDiff_fst.mul contDiff_snd)
lemma sum {I : Type*} (s : Finset I) {f : I → Config G n → E} (h : ∀ i∈s, Proxy (f i)) : Proxy (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Proxy.const 0
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih (fun i' h' => h i' (by simp [h'])))
lemma prod {K I : Type*} [NormedCommRing K] [NormedAlgebra ℝ K] (s : Finset I) {f : I → Config G n → K}
    (h : ∀ i∈s, Proxy (f i)) : Proxy (∏ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact Proxy.const 1
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (h i (by simp)).mul (ih (fun i' h' => h i' (by simp [h'])))
lemma const_smul (c : ℝ) (hf : Proxy f) : Proxy (c • f) := hf.after _ (contDiff_id.const_smul c)
lemma germ (h : Proxy f) : ContDiff ℝ ∞ (f ∘ representative) := by obtain ⟨a,ha,rfl⟩:=h; exact ha.comp contdiff_image
end Proxy

def respects {M : Type*} (f : Config G n → M) :=
  ∀ t : Site n → G.El, evenAt t → ∀ U, f (Lattice.gauge t U) = f U

/-- Urgent requirement BEFORE annihilating a BRST or equation label by this tree prescription. -/
lemma Proxy.active {f : Config G n → ℝ} (h : Proxy f) (hr : respects f) : PreTest f :=
  ⟨hr, ⟨h.cont.comp continuous_links, h.germ.contDiffAt⟩, h.cont⟩

variable (b : Edge (Site n))

lemma proxy_mat : Proxy (fun U : Config G n => G.mat (U b)) :=
  ⟨fun A : ArrayOf G n => A b, contDiff_apply .., rfl⟩
lemma proxy_inv {a : Config G n → G.El} (h : Proxy fun U => G.mat (a U)) :
    Proxy fun U => G.mat (a U)⁻¹ := h.after _ (starL' ℝ).contDiff
lemma proxy_path (o : Site n) (w : Walk) : Proxy (fun U : Config G n => G.mat (travel U o w)) := by
  induction w generalizing o with
  | nil => exact Proxy.const _
  | cons d w ih =>
    have h : Proxy (fun U : Config G n => G.mat (d.read U o)) := by
      unfold Step.read; split; exact proxy_inv (proxy_mat _); exact proxy_mat _
    exact h.mul (ih _)
lemma proxy_curvature {X : Config G n → G.El} (h : Proxy (fun U => G.mat (X U))) :
    Proxy fun U => G.curvature (X U) := ((h.sub (proxy_inv h)).const_smul (1/2:ℝ)).after
      _ G.projectColor.toContinuousLinearMap.contDiff

/-- Full Wilson half-action. We'll use its gauge-link derivative in the original torus at `b`
AND at its inversion mirror. -/
def invoice (U : Config G n) : ℝ := energy U / 2
lemma invoice_proxy : Proxy (invoice (G:=G) (n:=n)) := by
  have hf (p : Face (Per n)) : Proxy fun U : Config G n => G.price (faceValue U p) := by
    let L := Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap
    exact (proxy_path (n:=n) (G:=G) p.1 (square ..)).after (fun x => 1 - L x / G.repDim)
      (contDiff_const.sub (L.contDiff.div_const _))
  have h := Proxy.sum _ (f:=fun p (U:Config G n) => G.price (faceValue U p)) (fun (i : Face (Per n)) (_ : i ∈ Finset.univ) => hf i)
  have he : energy (G:=G) (n:=n) = (∑ p, fun U : Config G n => G.price (faceValue U p)) := by funext U; rw [energy,Finset.sum_apply]
  unfold invoice; simp_rw [he]; exact h.after _ (contDiff_id.div_const _) -- simp rw?

lemma invoice_even : respects (invoice (G:=G) (n:=n)) := by
  intro t ht U; rw [invoice, energy_gauge, invoice]

variable {d : ℕ} (F : Labels.Frame G d) (S : SectionData F)

lemma field_proxy (v : F.Coeff) (o : Site n) : Proxy (S.places v o) := by
  have he (k : Source.Index G S.stencil) : Proxy (fun U : Config G n => Source.entry (expandAt o U) k) := by
    unfold Source.entry; split
    · exact ((proxy_mat _).after _ ((Matrix.entryLinearMap ℝ ℂ ..).toContinuousLinearMap.contDiff)).after
        _ (starL' ℝ (A:=ℂ)).contDiff
    exact (proxy_mat _).after _ (Matrix.entryLinearMap ℝ ℂ ..).toContinuousLinearMap.contDiff
  have hp (p : Formula G S.stencil) : Proxy fun U => MvPolynomial.aeval (Source.entry (expandAt o U)) p := by
    induction p using MvPolynomial.induction_on with
    | C a => simp only [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]; exact Proxy.const a
    | add => simp only [map_add]; apply Proxy.add <;> assumption
    | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact Proxy.mul hp (he _)
  exact hp _
end YM.FormalOPE.RG10.InversionWard
