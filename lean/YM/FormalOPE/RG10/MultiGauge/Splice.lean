import YM.FormalOPE.RG10.StationaryMarks.CurtainTop
import Mathlib.MeasureTheory.Group.Measure
/-!
 # dynamic gaussian split for finite inversion trusses (not a uniform covariance bound)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F K : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
 [NormedAddCommGroup K][NormedSpace ℝ K][FiniteDimensional ℝ K]

-- Hessian polarization from actual Cred.
namespace Splice
local notation "v" => Module.Dual
 def raw (a:E→ℝ)(x:E): E→L[ℝ] ℝ:= fderiv ℝ (fderiv ℝ a) 0 x
 def q (a:E→ℝ) : E →ₗ[ℝ] Module.Dual ℝ E where
  toFun x:= (raw a x).toLinearMap
  map_add' x y:= by unfold raw; ext v'; simp
  map_smul' r x:= by unfold raw; ext v'; simp
 def polar (a:E→ℝ): E →ₗ[ℝ] Module.Dual ℝ E := ((2:ℝ)⁻¹) • (q a + (q a).flip)
omit [FiniteDimensional ℝ E] in
lemma side_p (a:E→ℝ) (x y:E) : polar a x y= ((q a x y + q a y x)/2):= by simp [polar,div_eq_inv_mul,mul_add]
omit [FiniteDimensional ℝ E] in
lemma origin_p (a:E→ℝ)(x:E): polar a x x / 2 = jet a 2 x:= by
 rw [side_p]; unfold jet; rw [iteratedFDeriv_two_apply]; change (q a x x+q a x x)/2/2= _ * q a x x; norm_num [Nat.factorial]; ring
variable {G:Gauge} {I:Type}[Fintype I]
 def evidence (A:Spending G I) (H:Credential A): Law (Direction G I) where
 P:= polar (A ∘ expLinks G I)
 turns x y:= by rw [side_p,side_p,add_comm]
 slope:= by simp_rw [origin_p]; exact H.boundedBy
 smooth:= by
  let a:= A ∘ expLinks G I
  rw [show (fun x=> polar a x x) = fun x=>2 * jet a 2 x from funext (fun i=> (by rw [← origin_p]; ring))]; exact continuous_const.mul (Smooth.continuousJet a 2)
lemma evidence_law (A:Spending G I) (H:Credential A): (evidence A H).kern= Radial.kernel (A ∘ expLinks G I):= by ext1 x; unfold Radial.kernel Law.kern; rw [show (evidence A H).P= polar _ from rfl, neg_div,(show polar _ x x / 2 = jet (A ∘ expLinks G I) 2 x from origin_p ..)] -- orientation

variable (Λ: Law E)
-- inLaw.Focused.
def focusWith (p:F→ₗ[ℝ] E) (h: Injective p) : Law F where
 P:= (LinearMap.compl₂ (Λ.P.comp p) p) -- equivalent
 turns x y:= Λ.turns (p x) (p y)
 slope:= by
   obtain ⟨c,hc,H⟩:= Λ.slope
   obtain ⟨K,hk,hp⟩:= (p.injective_iff_antilipschitz).mp h
   have hk': (0:ℝ)< K:=hk
   refine ⟨c/(K:ℝ)^2,by positivity,fun x=>?_⟩
   apply le_trans _ (H (p x))
   have he: ‖x‖ ≤ (K:ℝ)*‖p x‖:= ZeroHomClass.bound_of_antilipschitz p hp x
   calc
     _ ≤ (c/(K:ℝ)^2)*((K:ℝ)*‖p x‖)^2:= by gcongr
     _ = _:= by field_simp
 smooth:= Λ.smooth.comp p.continuous_of_finiteDimensional

-- here d reconstructs joint variable as frame of elementary locations (x,B)
variable (d:(F × K) ≃ₗ[ℝ] E)
 def fine : F→ₗ[ℝ] E := d.toLinearMap ∘ₗ (LinearMap.inl ℝ F K)
 def coarse : K→ₗ[ℝ] E := d.toLinearMap ∘ₗ (LinearMap.inr ℝ F K)
 def fast : Law F:= focusWith Λ (fine d) (by intro x y h; exact congr_arg Prod.fst (d.injective h))
 def mixed : K→ₗ[ℝ] Module.Dual ℝ F:= (LinearMap.compl₂ (Λ.P.comp (coarse d)) (fine d))
 def pin : K→ₗ[ℝ] F:= -((fast Λ d).inverse.comp (mixed Λ d))
 def shaft : K →ₗ[ℝ] E := coarse d + LinearMap.comp (fine d) (pin Λ d)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ K] in
lemma namely (y) : shaft Λ d y=d (pin Λ d y,y):= by
 change d (0,y)+d (pin Λ d y,0)=_
 rw [←map_add]; simp
 def rest : Law K := focusWith Λ (shaft Λ d) (by intro x y h; simp_rw [namely Λ d] at h; exact congr_arg Prod.snd (d.injective h))
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ K] in
lemma orthogonal (x y): Λ.P (shaft Λ d y) (fine d x)=0:= by
 change Λ.P (coarse d y+fine d (- ((fast Λ d).inverse (mixed Λ d y)))) _=0
 rw [map_neg,_root_.map_add]; simp only [map_neg,←sub_eq_add_neg]
 change mixed Λ d y x- (fast Λ d).P ((fast Λ d).inverse (mixed Λ d y)) x=0; simp
 def chart (q:F×K) : F × K:= (q.1+ pin Λ d q.2,q.2)
 def fusion : (F×K)≃ₗ[ℝ] E := LinearEquiv.trans
  { toFun:=chart Λ d
    invFun:=fun z=> (z.1-pin Λ d z.2,z.2)
    map_add':=fun x y=> by ext1 <;> simp [chart]; abel
    map_smul':=fun r u=> by ext1<;>simp [chart,smul_add]
    left_inv:=fun x=>by simp [chart]
    right_inv:=fun x=>by simp [chart] } d
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ K] in
lemma fusion_eq (x y): fusion Λ d (x,y)=fine d x + shaft Λ d y:= by
 rw [namely]; change d (_+_,y)= d _ + d _; rw [←map_add]; simp
omit [FiniteDimensional ℝ E]
lemma matchPrice (x y) : Λ.P (fusion Λ d (x,y)) (fusion Λ d (x,y)) = (fast Λ d).P x x + (rest Λ d).P y y:= by
 rw [fusion_eq]; simp only [map_add,LinearMap.add_apply]; rw [Λ.turns (fine d x) (shaft Λ d y),orthogonal,zero_add,add_zero]; rfl -- inspect
lemma stamp (x y): Λ.kern (fusion Λ d (x,y))= (fast Λ d).kern x * (rest Λ d).kern y:= by unfold Law.kern; rw [matchPrice,neg_add,add_div,Real.exp_add]
end Splice
end YM.FormalOPE.RG10.MultiGauge
