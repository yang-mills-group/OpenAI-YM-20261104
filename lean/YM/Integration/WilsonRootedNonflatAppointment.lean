import YM.Integration.WilsonRootedNonflatResponse
import YM.Juniper.Caret.Regular

/-! A true coarse field with nonzero curvature inside any genuine open
Wilson appointment, with the same source-coordinate argument. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatAppointment
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Marker Multi Exterior Tree
open Matrix Pressure Next.SectorChange AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine
open Comparison.RG02
open WilsonRootedHeldNonflat (needle selected)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (n:Side)

theorem face (hn:2≤n.val)(a:G.El):faceValue (needle n a) (selected n)=a:=by
  have away:(step (1:Axis):Site n)≠0:=by
    intro h
    have hw:(1:Per n).val=1:=(ZMod.val_eq_one hn _).2 rfl
    have hk:=congr_fun h (1:Axis)
    simp only [step_apply,if_true,Pi.zero_apply] at hk
    rw [hk] at hw
    simp at hw
  rw [selected,Push.Corrected.Torus.square_identity]
  simp [needle,away]

def seed (v:G.Color):fieldDir G n 1:=fun b=>if b=((0:Site n),coord (0:Axis)) then v else 0

theorem needle_ray (v:G.Color)(t:ℝ):
    represent (decode (t • flatten (seed n v)))=needle n (G.lieExp (t • v)):=by
  have rail:decode (t • flatten (seed n v))=t • seed n v:=
    calc _=plain G n 1 (t • flatten (seed n v)):=rfl
         _=t • plain G n 1 (flatten (seed n v)):=map_smul ..
         _=_:=rfl
  rw [rail]
  funext e
  obtain ⟨x,i⟩:=e
  change G.lieExp (t • (if (x,coord i)=((0:Site n),coord (0:Axis)) then v else 0))*1=
      if (x,i)=((0:Site n),(0:Axis)) then G.lieExp (t • v) else 1
  simp only [Prod.mk.injEq,coord_iff,mul_one]
  split <;> simp [*]

/-- The ray can meet any finite set of already paid local requirements.
It also meets the source sampling convention at every nonzero g. -/
theorem original (simple:G.Simple)(hn:2≤n.val){θ:ℝ}(hθ:0<θ)
    (𝒜:Gaussian.Vec (Raw G n)→Prop)(accepted:∀ᶠ B in 𝓝 0,𝒜 B):
    ∃B:Gaussian.Vec (Raw G n),𝒜 B ∧ flags θ (represent (decode B))=∅ ∧
      G.curvature (faceValue (represent (decode B)) (selected n))≠0 ∧
      ∀{g:ℝ},g≠0→Integral.sample g (g⁻¹ • decode B)=represent (decode B):=by
  haveI:=simple.nontrivial_color
  obtain ⟨v,hv⟩:=exists_ne (0:G.Color)
  let ray:=fun t:ℝ=>t • flatten (seed n v)
  have near:Tendsto ray (𝓝 0) (𝓝 0):=by
    have c:Continuous (fun t:ℝ=>t • flatten (seed n v)):=continuous_id.smul continuous_const
    simpa only [zero_smul] using c.tendsto (0:ℝ)
  have arrive:Tendsto (fun t:ℝ=>represent (decode (ray t))) (𝓝 0) (𝓝 1):=by
    have needleCont:Continuous (fun t:ℝ=>needle n (G.lieExp (t • v))):=by
      apply continuous_pi
      intro e
      by_cases he:e=((0:Site n),(0:Axis)) <;> simp only [needle,he,if_true,if_false] <;> fun_prop
    have eq:(fun t:ℝ=>represent (decode (ray t)))=fun t:ℝ=>needle n (G.lieExp (t • v)):=funext (needle_ray n v)
    rw [eq]
    have origin:needle n (1:G.El)=(1:Config G n):=by funext i;simp [needle]
    simpa only [zero_smul,G.mat_lieExp_zero,origin] using needleCont.tendsto (0:ℝ)
  have all:= (near.eventually accepted).and (arrive.eventually (Juniper.Caret.flat_flags n θ hθ))
  have material (B:Gaussian.Vec (Raw G n)) {g:ℝ}(hg:g≠0):
      Integral.sample g (g⁻¹ • decode B)=represent (decode B):=by
    unfold Integral.sample
    rw [smul_smul,mul_inv_cancel₀ hg,one_smul]
  by_contra absent
  have vanishes:(fun t:ℝ=>G.curvature (G.lieExp (t • v)))=ᶠ[𝓝 0] (fun _=>0):=by
    filter_upwards [all] with t ht
    by_contra h
    exact absent ⟨ray t,ht.1,ht.2,by simpa [ray,needle_ray,face n hn] using h,fun hg=>material _ hg⟩
  have hz:HasDerivAt (fun t:ℝ=>G.curvature (G.lieExp (t • v))) 0 0:=
    (hasDerivAt_const (0:ℝ) (0:G.Color)).congr_of_eventuallyEq vanishes
  exact hv ((G.leading_curvature v).unique hz)

end YM.Integration.WilsonRootedNonflatAppointment
