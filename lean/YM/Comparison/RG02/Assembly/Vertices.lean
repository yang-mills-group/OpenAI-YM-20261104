import YM.Comparison.RG02.Order.Polar
import YM.PertExtension.Exponent
/-!
# Primitive microscopic vertices

Polarized through any finite degree, real Lie fields. Use the radial perturbation variable (positive)
chosen per step, other variables can be inserted **within** this protocol. Around the common
rescaled vacuum include all physical gradients exactly. Taylor `n` means through degree n,
 divide by n! also on mixed rows *before* the marker substitution. Some source vertices already
 carry explicit negative grade. Preserve their shift exactly. Use the bounds from
 `YM.PertExtension.Series.Radial` (same radial convention; not using other scheme results).
 These constants work at *fixed finite dimensional geometry* not in a changing volume. Use e.g.
 for finite-period gauge independence; the step remainder still has its actual norm & domain
 estimates to prove separately by analytic tasks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Finset Filter MeasureTheory
open YM.Marker YM.Multi
open YM.PertExtension.Series YM.Comparison.RG02.Order
open scoped Topology BigOperators Classical ContDiff
variable {E U W Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] {c : ℝ}

section maps
variable (Z : Zone Y) (V : Y→ℝ)
lemma built_map {f : ℝ→Y→U} {a : ℕ→Y→U} (h : Z.Built V f a) (L : U→L[ℝ] W) :
    Z.Built V (fun t u=> L (f t u)) (fun n u=>L (a n u)) := by
  constructor
  · intro n
    obtain ⟨C,k,hc,H⟩ := (h.invoice n).exists_bound
    refine ⟨‖L‖*C,k,mul_nonneg (norm_nonneg _) hc,fun y=>?_⟩
    rw [mul_assoc]; exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (H y) (norm_nonneg _))
  intro n
  let d : ℝ→Y→W := (fun t u=> L (f t u))-Zone.eval (fun n u=> L (a n u)) n
  let p := f-Zone.eval a n
  have hv : d=fun t y=>L (p t y):= by funext t y; simp [d,p,Zone.eval,map_sub,map_sum]
  change Z.Fits _ _ d; rw [hv]; exact (h.fits n).shift_a (h.fits n).envelope ⟨1,‖L‖,0,zero_lt_one,norm_nonneg _,fun x t _ _=>
    ⟨by rw [pow_zero,mul_one]; exact L.le_opNorm _, le_rfl⟩⟩

variable {f : ℝ → Y → U} {a : ℕ→ Y → U} (l : ℕ)

def divided (f : ℝ → Y → U) (t : ℝ) (y : Y) : U := (t^l)⁻¹ • f t y

lemma shift_value (a : ℕ→Y→U) (n : ℕ) (u : Y) (t : ℝ) (he : ∀ i < l, a i u=0) :
    Zone.eval a (l+n) t u = t^l • Zone.eval (fun i=> a (l+i)) n t u := by
  unfold Zone.eval
  rw [Finset.smul_sum]
  simp_rw [smul_smul, ← pow_add]
  rw [show l+n+1=l+(n+1) by omega,sum_range_add,sum_eq_zero fun i hi=> ?_,zero_add]
  rw [he i (mem_range.mp hi),smul_zero]

lemma divided_built (h : Z.Built V f a) (he : ∀ i < l,∀ y,a i y=0) :
    Z.Built V (divided l f) (fun i=>a (l+i)) := by
  refine ⟨fun n=>h.invoice _,fun n=>?_⟩
  let k:=l+n
  obtain ⟨δ,C,p,hd,hC,H⟩:= (h.fits k).cost
  refine ⟨(h.fits k).envelope,δ,C,p,hd,hC,fun x t ht hT=> ?_⟩
  have hK : 0 < t^l := pow_pos ht _
  have hF : f t x = t^l • divided l f t x := by unfold divided; rw [smul_smul,mul_inv_cancel₀ hK.ne',one_smul]
  have Hx:= H x t ht hT
  simp only [Pi.sub_apply,k] at *
  rw [show l+n+1=l+(n+1) by omega,pow_add, shift_value l _ n x t (fun i hi=> he i hi x), hF,← smul_sub,norm_smul, Real.norm_of_nonneg hK.le,mul_left_comm (C * Z.w x^p * V x)] at Hx
  exact (mul_le_mul_iff_right₀ hK).mp Hx
end maps

abbrev jet (F : E→W) (k : ℕ) (x : E) := (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => x)
@[simp] lemma jet_zero (F : E→W) (x : E) : jet F 0 x=F 0 := by simp [jet]

lemma jet_eq (f : E→ℝ) : jet f=Radial.jet f := rfl
lemma jet_apply_left (L : U→L[ℝ] W) (f : E→U) (i : ℕ) (H : ContDiffAt ℝ i f 0) (u) :
    L (jet f i u)=jet (L ∘ f) i u := by
  rw [jet,map_smul,jet, L.iteratedFDeriv_comp_left H le_rfl]; rfl

lemma jet_real {f : E→ℂ} {i} (H : ContDiffAt ℝ ∞ f 0) (u : E) :
    jet f i u=↑(jet (Complex.re ∘ f) i u )+Complex.I*↑(jet (Complex.im ∘ f) i u) := by
  let g := jet f i u; have ht : ContDiffAt ℝ i f 0:= H.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [← show g.re=jet (Complex.re ∘ f) i u from jet_apply_left Complex.reCLM f i ht u,
      ← show g.im=jet (Complex.im ∘ f) i u from jet_apply_left Complex.imCLM f i ht u,mul_comm Complex.I]; exact (Complex.re_add_im ..).symm

local notation "Z" => Radial.zone (E:=E)

lemma built_jet [FiniteDimensional ℝ E] {f : E→ℂ} (H : ContDiffAt ℝ ∞ f 0) :
    (Z).Built 1 (fun t x=>f (t • x)) (jet f) := by
  let X := Complex.re ∘ f; let Y := Complex.im ∘ f
  have he := Radial.ordinary X (H.continuousLinearMap_comp Complex.reCLM)
  have hg := Radial.ordinary Y (H.continuousLinearMap_comp Complex.imCLM)
  let i : ℝ→L[ℝ]ℂ := Complex.I • Complex.ofRealCLM
  have hv:= (built_map _ _ he Complex.ofRealCLM).add (built_map _ _ hg i)
  convert hv using 1
  · funext t x
    change f _ = ↑(f (t•x)).re + Complex.I*↑(f (t•x)).im
    rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
  exact funext fun n=> funext fun u=> jet_real H u

/-- Explicit shift cost at fixed field horizon and valuation; the estimate here doesn't
     silently multiply by `g^l` before testing. -/
theorem shifted [FiniteDimensional ℝ E] (F : E→ℂ) (H : ContDiffAt ℝ ∞ F 0)
    (l : ℕ) (h : ∀ i < l,∀ x, jet F i x=0) :
    (Z).Built 1 (fun t x=> (t^l)⁻¹ • F (t • x)) (fun i=> jet F (l+i)) :=
  divided_built _ _ l (built_jet H) h

end YM.Comparison.RG02.Assembly
