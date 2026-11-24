import YM.FormalOPE.RG10.Ward.Proxies

/-! Directional Ward data, INCLUDING spectator differentiation and mirrored moves.
Right versions needed already when reorienting the falling links. `invoice/effort` here address
the same plaquette action and multiplicities as the independent orbit regulator. This is not
the external-scheme equation rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (b : Edge (Site n))

/-- Move in arbitrary matrices, to differentiate then forget extension. -/
def matrixTilt (A : ArrayOf G n) (v : G.Color) : ArrayOf G n := fun i => if i=b then
    G.mat (G.lieExp v) * A i else if i=Orb.reflect b then A i * star (G.mat (G.lieExp v)) else A i
lemma faithful (U : Config G n) (v : G.Color) : matrixTilt b (image U) v = image (tilt b U v) := by
  funext i; unfold matrixTilt image tilt InversionWard.push; split_ifs <;> rfl

lemma full_smooth : ContDiff ℝ ∞ (uncurry (matrixTilt (G:=G) b)) := by
  apply contDiff_pi.mpr; intro i
  unfold uncurry matrixTilt
  have he : ContDiff ℝ ∞ fun x : ArrayOf G n × G.Color => G.mat (G.lieExp x.2) :=
    ((G.exp_jet.of_le le_top).comp contDiff_snd)
  have ha : ContDiff ℝ ∞ fun x : ArrayOf G n × G.Color => x.1 i := (contDiff_apply ..).comp contDiff_fst
  split; exact he.mul ha
  split; exact ha.mul ((starL' ℝ).contDiff.comp he); exact ha

variable {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- Real linearly parameterized all color directions. (Also for ℂ-valued words interpreted as
modules over ℝ.) -/
def vary (f : Config G n → E) (U : Config G n) : G.Color →L[ℝ] E := fderiv ℝ (fun v => f (tilt b U v)) 0

namespace Proxy

private lemma moved (A : ArrayOf G n → E) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (uncurry fun M c => A (matrixTilt b (G:=G) M c)) := hA.comp (full_smooth b)

variable {f : Config G n → E}
lemma line (h : Proxy f) (U : Config G n) : ContDiff ℝ ∞ (fun v => f (tilt b U v)) := by
  obtain ⟨A,hA,rfl⟩:=h
  simp_rw [Function.comp_apply, ← faithful]
  exact (moved b A hA).comp (f:=fun v => (image U,v)) (contDiff_const.prodMk contDiff_id)

lemma proxy_vary (h : Proxy f) : Proxy (vary b f) := by
  obtain ⟨A,hA,rfl⟩:=h
  refine ⟨fun M => fderiv ℝ (fun v => A (matrixTilt b M v)) 0,
    ContDiff.fderiv (moved b A hA) (g:=fun _ => 0) contDiff_const (by simp),?_⟩
  funext M; unfold vary; simp_rw [Function.comp_apply, faithful]

lemma derivative (h : Proxy f) (U : Config G n) (a : G.Color) :
    HasDerivAt (fun t : ℝ => f (tilt b U (t • a))) (vary b f U a) 0 := by
  have he : HasDerivAt (fun t : ℝ => t • a) a 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const a
  exact (((h.line b U).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0 he (by simp)

lemma tangent (h : Proxy f) (U : Config G n) (a : G.Color) (t : ℝ) :
    HasDerivAt (fun r : ℝ => f (tilt b U (r • a))) (vary b f (tilt b U (t • a)) a) t := by
  have hv : HasDerivAt (fun s : ℝ => f (tilt b (tilt b U (t • a)) (s • a)))
      (vary b f (tilt b U (t • a)) a) (t-t) := by rw [sub_self]; exact derivative _ h _ _
  simpa only [point_combine, sub_add_cancel] using! hv.comp_sub_const t t

lemma deriv_eq (h : Proxy f) (U : Config G n) (a : G.Color) :
    deriv (fun t:ℝ => f (tilt b U (t • a))) 0 = vary b f U a := (derivative b h U a).deriv
end Proxy

variable {X : Config G n → G.Color}

def coupled (X : Config G n → G.Color) (f : Config G n → E) (U : Config G n) := vary b f U (X U)
lemma Proxy.couple {f : Config G n → E} (hx : Proxy X) (h : Proxy f) :
    Proxy (coupled b X f) := by
  unfold coupled
  exact ((h.proxy_vary b).pair hx).after (fun p : (G.Color→L[ℝ] E) × G.Color => p.1 p.2) (contDiff_fst.clm_apply contDiff_snd)

def effort (X : Config G n → G.Color) := coupled b X invoice
lemma Proxy.effort (h : Proxy X) : Proxy (effort b X) := h.couple b invoice_proxy

local notation "dirs" => WardBin.dirs
lemma coupled_components (f : Config G n → E) (U : Config G n) (X : Config G n → G.Color) : coupled b X f U =
    ∑ i : G.ColorIndex, Inner.inner ℝ (dirs G i) (X U) • vary b f U (dirs G i) := by
  unfold coupled; conv_lhs => arg 2; rw [← (dirs G).sum_repr (X U)] -- check
  rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul, OrthonormalBasis.repr_apply_apply]

/-- For scalar Ward uses extend products literally. -/
lemma leibniz {f g : Config G n → ℝ} (h : Proxy f) (k : Proxy g) (U : Config G n) (X : Config G n → G.Color) :
    coupled b X (f*g) U = coupled b X f U * g U + f U * coupled b X g U := by
  unfold coupled; rw [← Proxy.deriv_eq b (h.mul k)]; simpa only [Pi.mul_apply, zero_smul, home] using!
    ((Proxy.derivative b h U (X U)).fun_mul (Proxy.derivative b k U (X U))).deriv

/-- Haar divergence of `X` ON INDEPENDENT ORBITS. -/
def fallout (X : Config G n → G.Color) (U : Config G n) := ∑ i : G.ColorIndex,
  Inner.inner ℝ (dirs G i) (vary b X U (dirs G i))
lemma Proxy.fallout (h : Proxy X) : Proxy (fallout b X) := by
  let a := fun i : G.ColorIndex => fun U => Inner.inner ℝ (dirs G i) (vary b X U (dirs G i))
  have ha (i : G.ColorIndex) : Proxy (a i) := (h.proxy_vary b).after
    (fun x : G.Color→L[ℝ] G.Color => Inner.inner ℝ (dirs G i) (x (dirs G i)))
    (contDiff_const.inner ℝ (contDiff_id.clm_apply contDiff_const))
  rw [show InversionWard.fallout b X = ∑ i, a i by funext; rw [Finset.sum_apply]; rfl]
  exact Proxy.sum _ fun i _ => ha i

lemma commute (f : Config G n → E) (h : Proxy f) (L : E →L[ℝ] ℝ) (U a) :
    vary b (fun U => L (f U)) U a = L (vary b f U a) := by
  rw [← Proxy.deriv_eq b (h.after L L.contDiff)]
  exact (L.hasFDerivAt.comp_hasDerivAt 0 (Proxy.derivative b h U a)).deriv
lemma fallout_deriv (h : Proxy X) (U) : fallout b X U = ∑ i : G.ColorIndex,
    vary b (fun A => Inner.inner ℝ (dirs G i) (X A)) U (dirs G i) := by
  unfold fallout
  apply sum_congr rfl; intro i _; exact (InversionWard.commute b X h (innerSL ℝ (dirs G i)) U (dirs G i)).symm
end YM.FormalOPE.RG10.InversionWard
