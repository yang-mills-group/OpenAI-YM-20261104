import YM.SchemeRG11.Saddle.Top
import YM.PertExtension.GaussianIBP

/-! The actual Gaussian on the Landau slice of the finite inversion quotient.
Coordinate convention for BV slots K c: one-half torus inner product. The
remaining K slots for the Wick expectation therefore use gradients of ghosts
dual to Flow in that same pairing with the free determinant. This fixes the
free Grassmann matrix to identity without a sign/gauge/basis ambiguity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Pert.Orb Finset Function PertExtension GaussianScore SchemeRG11.Sway

abbrev ScalarGhost (G:Gauge) (n:Side) := ↥(Mean G n)

variable {G:Gauge}{n:Side}
local notation "X" => Land G n
local notation "U" => ScalarGhost G n
local notation "⟪" x "," y "⟫" => inner ℝ x y

def restrictedHessian (G:Gauge) (n:Side) : Land G n →ₗ[ℝ] Module.Dual ℝ (Land G n) :=
  LinearMap.compl₂ ((formL G n).comp (TransV G n).subtype) (TransV G n).subtype

lemma LANDjet (u:X) : Series.Radial.jet (LAND (G:=G) (n:=n)) 2 u = form u.val u.val /2 := by
  rw [LAND_eq, Local.jetLinear]
  exact VF_heavy _
  exact VF_stable.smooth

def landLaw (G:Gauge)(n:Side) : Law (Land G n) where
  P := restrictedHessian G n
  turns x y := form_symm ..
  slope := by
    obtain ⟨c,hc,h⟩ := LAND_go (G:=G) (n:=n)
    exact ⟨c,hc,fun x=> (h x).trans_eq (LANDjet x)⟩
  smooth := by
    have h := Series.Radial.Smooth.continuousJet (LAND (G:=G) (n:=n)) 2
    have hm(x : Land G n) : (restrictedHessian G n) x x=2*Series.Radial.jet (LAND (G:=G) (n:=n)) 2 x:=by
      rw [LANDjet]; change form x.val x.val=2*_; ring
    simp_rw [hm]; exact continuous_const.mul h

lemma LANDkernel (u:X) : Series.Radial.kernel LAND u=(landLaw G n).kern u := by
  unfold Series.Radial.kernel
  rw [LANDjet]; unfold Law.kern; change _ = Real.exp (_/2); rw [neg_div]; rfl

def siteTest (v u:ScalarGhost G n):ℝ:= ∑ x, ⟪v.val x, u.val x⟫ / 2

lemma siteTest_comm (v u:ScalarGhost G n): siteTest v u= siteTest u v:=by
  unfold siteTest; simp only [real_inner_comm]
lemma siteTest_add (v u w:ScalarGhost G n): siteTest (v+u) w=siteTest v w+siteTest u w:= by
  simp only [siteTest, Submodule.coe_add, Pi.add_apply, inner_add_left, add_div, sum_add_distrib]
lemma siteTest_smul (r:ℝ)(v u:ScalarGhost G n): siteTest (r•v) u=r*siteTest v u:= by
  unfold siteTest; rw [Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; change ⟪r•v.val i,u.val i⟫/2=_ ; rw [real_inner_smul_left]; ring

def duality (G:Gauge)(n:Side) : ScalarGhost G n →ₗ[ℝ] Module.Dual ℝ (ScalarGhost G n) :=
  LinearMap.mk₂ ℝ siteTest siteTest_add siteTest_smul
    (fun x y z=>by rw [siteTest_comm x,siteTest_add,siteTest_comm y x,siteTest_comm z])
    (fun r x y=>by rw [siteTest_comm x,siteTest_smul,siteTest_comm x]; rfl)

lemma duality_injective (G:Gauge)(n:Side): Injective (duality G n) := by
  rw [←LinearMap.ker_eq_bot]; apply bot_unique; intro a ha
  have he : siteTest a a=0 := LinearMap.congr_fun (LinearMap.mem_ker.mp ha) a
  apply Subtype.ext; funext i
  change a.val i=0; apply inner_self_eq_zero (𝕜:=ℝ) |>.mp
  have h := (sum_eq_zero_iff_of_nonneg (fun x (_:x ∈ Finset.univ)=> show 0 ≤ ⟪a.val x,a.val x⟫/2 from div_nonneg real_inner_self_nonneg (by norm_num))).mp he i (mem_univ _)
  linarith

def dualGhost (G:Gauge)(n:Side) : ScalarGhost G n ≃ₗ[ℝ] Module.Dual ℝ (ScalarGhost G n) :=
  LinearEquiv.ofBijective (duality G n) ⟨duality_injective ..,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp (duality_injective ..)⟩

/- A c-basis can be chosen arbitrarily. Choose its partnering **antighost** basis
so that K_c-free Hessian becomes `-1` in antighost then ghost order.
The Actual embedding of antighost as a K field is by `gM`. -/
variable {ι:Type} [Fintype ι] [DecidableEq ι]

def barBasis (b : Module.Basis ι ℝ U) : Module.Basis ι ℝ U :=
  ((b.map (paneLap G n).toLinearEquiv).dualBasis).map (dualGhost G n).symm

lemma ghost_dual (b : Module.Basis ι ℝ U)(i:ι)(v:U):
    siteTest (barBasis b i) v=b.coord i ((paneLap G n).symm v):= by
  let e := paneLap G n; let d:=dualGhost G n
  let c := b.map e.toLinearEquiv
  change d ((barBasis b) i) v= _
  rw [show barBasis b i=d.symm (c.dualBasis i) from Module.Basis.map_apply ..,
     LinearEquiv.apply_symm_apply]
  simp [c,e]

lemma ghost_start (b: Module.Basis ι ℝ U) (i j:ι) :
    siteTest (barBasis b i) (paneGhost G n 0 (b j)) = if i=j then 1 else 0 := by
  rw [pane_flat, ContinuousLinearEquiv.coe_coe, ghost_dual, ContinuousLinearEquiv.symm_apply_apply]; simp [Finsupp.single_apply,eq_comm]

end YM.FVAAlt2
