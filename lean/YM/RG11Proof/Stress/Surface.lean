import YM.RG11Proof.Fields.Winding
import YM.RG11Proof.Stress.Mandate
import YM.Next.MAXWELL.System
import YM.Work.A01.Conserve

/-!
# Mandates from smooth separated kernels

The linear functionals on `Test` dual used below are algebraic extensions
of linear operations on SMOOTH REPRESENTED kernels on Conf. Exact extension
on possibly nontangible arrays makes no prediction for such inputs; USE WITH
that representation hypothesis. Dilation tests can likewise be expressed.
Not continuous operators for point measurements. All placements on full
conf.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.RG11.Stress
open scoped Classical ContDiff Topology BigOperators
open YM.RG11.Fields YM.RG11.Nodes YM.RG11.Jets
open MeasureTheory Set Function TopologicalSpace Filter Table Work.A01 Analysis
open PowerSeries
variable {G:Gauge}{F:Labels.Frames G}{n:ℕ}

/-- Smooth on Conf representative, with trivial 0 convention outside conf. -/
def clean (n:ℕ):Submodule ℂ (Points n→ℂ) where
   carrier:={K| ContDiffOn ℝ ∞ K (conf n) ∧ ∀ x:Points n,x ∉ conf n → K x=0}
   zero_mem':=⟨contDiffOn_const,fun _ _=>rfl⟩
   add_mem':=by rintro x y ⟨h,j⟩ ⟨h',j'⟩; exact ⟨h.add h',fun u hu=>by rw [Pi.add_apply,j _ hu,j' _ hu,add_zero]⟩
   smul_mem':=by rintro c _ ⟨h,j⟩; exact ⟨contDiffOn_const.smul h,fun u hu=>by rw [Pi.smul_apply,j _ hu,smul_zero]⟩

def dress (K:Points n→ℂ)(h:ContDiffOn ℝ ∞ K (conf n)):clean n:=by
  refine ⟨indicator (conf n) K,⟨?_,fun _ hu=>indicator_of_notMem hu _⟩⟩
  exact h.congr fun _ hu=>indicator_of_mem hu _

abbrev spot (n:ℕ):= Test n→ₗ[ℂ] ℂ

def pour (n:ℕ):clean n→ₗ[ℂ] spot n where
   toFun K:={
      toFun f:= f.applyTo K.val
      map_add' x y:=by change (∫ p,(x p+y p)*K.val p)=_; simp_rw [add_mul,integral_add (x.smearing K.property.1.continuousOn) (y.smearing K.property.1.continuousOn)]; rfl
      map_smul' c f:=by change (∫ p,(c*f p)*K.val p)=c*_; simp_rw [mul_assoc,integral_const_mul]; rfl }
   map_add' x y:=by ext1 f; change (∫ p,f p*(x.val p+y.val p))= _+_; simp_rw [mul_add,integral_add (f.smearing x.property.1.continuousOn) (f.smearing y.property.1.continuousOn)]; rfl
   map_smul' c f:=by ext1 t; change (∫ p,t p*(c*f.val p))= c*_; simp_rw [mul_left_comm _ c,integral_const_mul]; rfl

 theorem mixes (K:Points n→ℂ)(h:ContDiffOn ℝ ∞ K (conf n))(f:Test n): pour n (dress K h) f=f.applyTo K:=f.apply_eq (fun _ hu=>indicator_of_mem hu _)

private theorem faith (n:ℕ):Injective (pour n):=by
   intro x y he
   have H:= (Test.unique_kernel x.property.1.continuousOn y.property.1.continuousOn).mp (LinearMap.ext_iff.mp he)
   apply Subtype.ext; funext i; by_cases h:i∈conf n
   · exact H h
   rw [x.property.2 i h,y.property.2 i h]

private theorem supplies (n:ℕ):∃ f:spot n→ₗ[ℂ] clean n,f.comp (pour n)=LinearMap.id:=LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.mpr (faith n))

def lift (f:clean n→ₗ[ℂ] ℂ):spot n→ₗ[ℂ] ℂ:= f.comp ((supplies n).choose)

@[simp] theorem lift_at (f:clean n→ₗ[ℂ] ℂ)(x:clean n):lift f (pour n x)=f x:=congrArg f (LinearMap.congr_fun (supplies n).choose_spec x)

-- Mandate by a position derivative. Use `dress` to select arbitrary extension,
-- prove result independent of its outside-Conf values.

def directional (i:Fin n)(a:Axis){x:Points n}(hx:x∈conf n): clean n→ₗ[ℂ] ℂ where
   toFun u:=Points.gradient i a u.val x
   map_add' u v:=by
      have he(y:clean n):DifferentiableAt ℝ y.val x:=y.property.1.differentiableOn (by simp) x hx |>.differentiableAt ((conf_open _).mem_nhds hx)
      change fderiv ℝ (u.val+v.val) x _=_
      rw [fderiv_add (he u) (he v)]; rfl
   map_smul' c u:=by
      have he : DifferentiableAt ℝ u.val x:=u.property.1.differentiableOn (by simp) x hx |>.differentiableAt ((conf_open _).mem_nhds hx)
      change fderiv ℝ (c • u.val) x _ = c • _
      rw [fderiv_const_smul he]; rfl

@[simp] theorem on_at (K:Points n→ℂ)(h:ContDiffOn ℝ ∞ K (conf n))(i:Fin n)(a:Axis){x:Points n}(hx:x∈conf n):
    directional i a hx (dress K h)=Points.gradient i a K x:=by
   change fderiv ℝ ((conf n).indicator K) x _= fderiv ℝ K x _
   rw [Filter.EventuallyEq.fderiv_eq]
   filter_upwards [(conf_open _).mem_nhds hx] with y hy; exact indicator_of_mem hy _

section shell
variable {x:Points (n+1)}(hx:x∈conf _){χ:E4→ℝ}(w:Window x χ)(a:Axis)

include hx w
private theorem integrable_drop (u:clean (n+2)):
     Integrable (fun y:E4=>((D (basis a) χ y:ℝ):ℂ)*u.val (Points.cons y x)):=by
   simp_rw [← Complex.real_smul]
   refine cutoff_integrable (w.2.1.fderiv_apply ℝ _) ((w.1.continuous_fderiv (by simp)).clm_apply continuous_const) (fun y hy=>?_)
   refine (u.property.1.continuousOn.continuousAt ((conf_open _).mem_nhds (window_separated hx w ((tsupport_comp_subset (g:=fun L:E4→L[ℝ]ℝ=> L (basis a)) rfl _ ) hy)))).comp (f:=fun z:E4=>Points.cons z x) (show ContinuousAt _ y from ?_)
   unfold Points.cons points; fun_prop

/-- Matches Table.shellGrad sign. -/
-- likely hx auto? use explicit in proof
def run : clean (n+2) →ₗ[ℂ] ℂ where
   toFun f:= -(∫ y:E4, ((D (basis a) χ y:ℝ):ℂ)*f.val (Points.cons y x))
   map_add' v z:=by
     change -(∫ y:E4, ((_:ℝ):ℂ)*(v.val (Points.cons y x)+z.val (Points.cons y x)))= -_ + -_
     simp_rw [mul_add,integral_add (integrable_drop hx w a _) (integrable_drop hx w a _),neg_add]
   map_smul' c u:=by
      change -(∫ y:E4, ((_:ℝ):ℂ)*(c*u.val (Points.cons y x)))= c* -_
      simp_rw [mul_left_comm _ c,integral_const_mul,mul_neg]

@[simp] theorem run_at (K:Points (n+2)→ℂ)(h:ContDiffOn ℝ ∞ K (conf (n+2))):
   run hx w a (dress K h) = -(∫ y:E4,((D (basis a) χ y:ℝ):ℂ)*K (Points.cons y x)):=by
   refine congrArg Neg.neg (integral_congr_ae (Eventually.of_forall (fun y=>show _ * (conf _).indicator K (Points.cons y x) = _* K (Points.cons y x) from ?_)))
   by_cases he : D (basis a) χ y = 0
   · simp [he]
   rw [indicator_of_mem (separated_of_D hx w he) _]
end shell
end YM.RG11.Stress
