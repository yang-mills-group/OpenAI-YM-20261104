import YM.SchemeConversionRG11.Read.Tensor

/-! First-order vertical tangent of the tensor action. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Tape

open Pert.Position Affine Orbit Series Filter Function
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {m d : ℕ}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
local notation "T" => Tape F d m W
local notation "U" => Buffer F d

/-- Vertical derivative at the identity frame. -/
def vary (A : Tape F d m W) (B : Buffer F d) : Tape F d m W :=
  fderiv ℝ (fun p : Buffer F d × Tape F d m W ↦ put p.1 p.2) (0,A) (B,0)

private lemma tangent_curve (B : Buffer F d) : HasDerivAt (fun t : ℝ ↦ t • B) B 0 := by
  convert! (hasDerivAt_id' (0:ℝ)).smul_const B using 1; simp

private lemma tangent_apply (p : Tape F d m W) (g : ℝ → Buffer F d × Tape F d m W) (v) (h : HasDerivAt g v 0)
    (hp : g 0 = (0,p)) :
    HasDerivAt (fun t : ℝ ↦ put (g t).1 (g t).2)
      (fderiv ℝ (fun q : U × T ↦ put q.1 q.2) (0,p) v) 0 := by
  have he := (placing (F:=F) (d:=d) (W:=W) (m:=m)).differentiable (by simp)
  let Z := fun q : U × T ↦ put q.1 q.2
  have hk : HasFDerivAt Z (fderiv ℝ Z (0,p)) (g 0) := hp.symm ▸ (he (0,p)).hasFDerivAt
  exact hk.comp_hasDerivAt (𝕜:=ℝ) (F:=U × T) (E:=T) 0 h

private lemma tangent (p : T) (B : U) : HasDerivAt (fun t : ℝ ↦ put (t • B) p) (vary p B) 0 := by
  let g (t : ℝ) := (t • B,p)
  have hc : HasDerivAt (fun _ : ℝ ↦ p) 0 0 := hasDerivAt_const (0:ℝ) p
  have hp : HasDerivAt g (B,0) 0 := HasDerivAt.prodMk (𝕜:=ℝ) (F:=U) (G:=T) (tangent_curve B) hc
  exact tangent_apply p g _ hp (by simp [g])

lemma vary_at (p : T) (B : U) (v : Fin m → E F d) :
    vary p B v = ∑ i, p (Function.update v i (B.val (v i))) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ E F d) W v
  have hs : HasDerivAt (fun t : ℝ ↦ put (t • B) p v) (L (vary p B)) 0 := by
    let f := fun t : ℝ ↦ put (t • B) p
    have hL : HasFDerivAt L L (f 0) := ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) (E:=T) L
    have H := hL.comp_hasDerivAt (𝕜:=ℝ) (F:=T) (E:=W) 0 (tangent p B)
    exact H
  let w (i : Fin m) := B.val (v i)
  have ht : HasDerivAt (fun t : ℝ ↦ v + t • w) w 0 := by
    apply HasDerivAt.const_add
    convert! (hasDerivAt_id' (0:ℝ)).smul_const w using 1; simp
  have hq : HasFDerivAt p (p.linearDeriv v) (v + (0:ℝ) • w) := by rw [zero_smul, add_zero]; exact p.hasFDerivAt v
  change L (vary p B) = _
  rw [hs.unique (hq.comp_hasDerivAt 0 ht),ContinuousMultilinearMap.linearDeriv_apply]

private lemma horizontal (p p' : T) :
    fderiv ℝ (fun q : U × T ↦ put q.1 q.2) (0,p) (0,p')=p' := by
  let f (t : ℝ) := p + t • p'
  have ht : HasDerivAt f p' 0 := by
    change HasDerivAt (fun t : ℝ ↦ p + t • p') p' 0
    have hu : HasDerivAt (fun t : ℝ ↦ t • p') p' 0 := by
      convert! HasDerivAt.smul_const (hasDerivAt_id' (0:ℝ)) p' using 1; simp
    exact HasDerivAt.const_add (F:=T) (𝕜:=ℝ) p hu
  let g (t : ℝ) := ((0:U),f t)
  have hc : HasDerivAt (fun _ : ℝ ↦ (0:U)) 0 0 := hasDerivAt_const (0:ℝ) (0:U)
  have hD : HasDerivAt g (0,p') 0 := HasDerivAt.prodMk (𝕜:=ℝ) (F:=U) (G:=T) hc ht
  have he := tangent_apply p g _ hD (by simp [g,f])
  have h : (fun t ↦ put (g t).1 (g t).2) = f := funext (fun t ↦ put_zero (f t))
  rw [h] at he; exact HasDerivAt.unique (𝕜:=ℝ) (F:=T) he ht

lemma lift_one {K N : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup N] [NormedSpace ℝ N] {v : K → N} (Hv : ContDiff ℝ ω v) (s : Series K) :
    liftJet v s 1 = fderiv ℝ v (s 0) (s 1) := by
  have h := trunc_represents s 1
  have hk := h.regular.differentiableAt (by simp) |>.hasDerivAt
  rw [h.first le_rfl] at hk
  have hp := (Hv.differentiable (by simp) (trunc s 1 0)).hasFDerivAt
  have he := hp.comp_hasDerivAt (l:=v) (f:=trunc s 1) 0 hk
  rw [← (h.lift (Hv.contDiffAt)).first le_rfl, he.deriv,h.value]

/-- Does not assume a physical coupling is tracked by either series. -/
theorem leading (A : Series T) (B : Series U) (h : B 0 = 0) :
    hinge B A 1 = vary (A 0) (B 1) + A 1 := by
  rw [hinge, lift_one placing]
  let f := fun p : U × T ↦ put p.1 p.2
  have hL := horizontal (A 0) (A 1)
  have hz : fderiv ℝ f (0,A 0) ((B 1,(0:T)) + ((0:U),A 1)) = _ :=
    map_add (fderiv ℝ f (0,A 0)) (B 1,(0:T)) ((0:U),A 1)
  change fderiv ℝ f (B 0,A 0) (B 1,A 1) = _
  rw [h, show (B 1,A 1) = (B 1,(0:T)) + ((0:U),A 1) by simp, hz]
  exact congr_arg ((vary (A 0) (B 1)) + ·) hL
end YM.SchemeConversionRG11.Tape
