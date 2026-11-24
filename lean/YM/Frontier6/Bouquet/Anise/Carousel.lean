import YM.Frontier6.Bouquet.Geometry.Eclipsed

/-!
# Cylindrical operators reading at zero in one slot, others untouched
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q:Place}[FiniteDimensional ℝ P][FiniteDimensional ℝ Q] (h:P≤Q)
variable (g:Full P) (f: Full Q)
-- multipliers on otherwise arbitrary slots
section
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](g:X→ℂ)
def screen (hg: Smooth g): Full X→ₗ[ℂ] Full X where
   toFun f:= ⟨g*(f:X→ℂ), hg.mul f.contDiff, f.hasCompactSupport.mul_left,subset_univ _⟩
   map_add' _ _:= by ext1 x; change g x * (_+_)= _*_+ _*_; exact mul_add ..
   map_smul' c f:=by ext1 x; change g x*(c*f x)=c*(g x*f x); ring
lemma screened (hg:Smooth g)(f:Full X)(x:X): screen g hg f x=g x*f x:=rfl
lemma screen_subset (hg:Smooth g)(f:Full X): tsupport (screen g hg f) ⊆ tsupport f:=tsupport_mul_subset_right
end
abbrev paneM (u:P→ℂ)(hg:Smooth u) : Full Q →ₗ[ℂ] Full Q:= screen (u ∘ floorOf P Q) (hg.comp (floorOf P Q).contDiff) -- h argument absent! fix later
private def slideP (g:Full P)(f:Full Q) :=fun x:Q=> g (floorOf P Q x)* f (centerless h x)
lemma slide_compact : HasCompactSupport (slideP h g f):=by
   letI:= FiniteDimensional.proper ℝ P; letI:= FiniteDimensional.proper ℝ Q
   obtain ⟨r,hr⟩:= (f.hasCompactSupport.isBounded.subset_closedBall (0:Q)); obtain ⟨s,hs⟩:=g.hasCompactSupport.isBounded.subset_closedBall (0:P)
   have he: Function.support (slideP h g f)⊆ Metric.closedBall 0 (r+s):=by
       intro x hx; have hx':g (floorOf P Q x)≠0:=fun hw=> hx (by unfold slideP; rw [hw,zero_mul]); have hv:f (centerless h x)≠0:=fun hw=>hx (by unfold slideP; rw [hw,mul_zero])
       apply mem_closedBall_zero_iff.mpr
       nth_rw 1 [← centerless_self h x]; exact (norm_add_le ..).trans (add_le_add (mem_closedBall_zero_iff.mp (hr (subset_closure hv))) (mem_closedBall_zero_iff.mp (hs (subset_closure hx')))) -- defeq
   exact (isCompact_closedBall ..).of_isClosed_subset (isClosed_tsupport _) (closure_minimal he isClosed_closedBall)

def readCenter : Full Q →ₗ[ℂ] Full Q where
  toFun f:= ⟨slideP h g f, (g.contDiff.comp (floorOf P Q).contDiff).mul (f.contDiff.comp (centerless h).contDiff), slide_compact h g f,subset_univ _⟩
  map_add' a b:= by ext1 x; change g _*(a _+b _)=_*_+_*_; exact mul_add ..
  map_smul' c a:=by ext1 x; change g (floorOf P Q x)*(c*a (centerless h x))=c*(g _*a _); ring
lemma center_value (x:Q): readCenter h g f x=g (floorOf P Q x)* f (centerless h x):=rfl
lemma center_support : tsupport (readCenter h g f)⊆(floorOf P Q ⁻¹' tsupport g) ∩ (centerless h ⁻¹' tsupport f):=by
   have hr:(readCenter h g f:Q→ℂ)=(g ∘ floorOf P Q) * (f ∘ centerless h):=rfl
   rw [hr]; exact subset_inter (tsupport_mul_subset_left.trans (tsupport_comp_subset_preimage _ (floorOf P Q).continuous)) (tsupport_mul_subset_right.trans (tsupport_comp_subset_preimage _ (centerless h).continuous))
-- specialize to one slot
variable (z:Loft Q P)
def atLoft : Full Q →ₗ[ℂ] Full P := restrictS h (insideCL loft_le z)
lemma origin_cast (x:P): (forward h (insideCL loft_le z) x).val=z.val+x.val:=rfl
lemma floor_chart (x:P): floorOf P Q (forward h (insideCL loft_le z) x)=x:= by rw [forward, map_add,(attendance h).of_left,(attendance h).of_right,zero_add]
lemma beam_chart (x:P): centerless h (forward h (insideCL loft_le z) x)= (insideCL loft_le z):=by rw [forward,map_add,centerless_traces, centerless_paths,add_zero]
lemma loft_zero : atLoft h z f 0= f (insideCL loft_le z):=by rw [atLoft,restrict_at,forward,map_zero,add_zero]
lemma specialization : atLoft h z (readCenter h g f)=(atLoft h z f 0) • g := by
    ext1 x; rw [show atLoft h z (readCenter h g f) x= readCenter h g f (forward h (insideCL loft_le z) x) from rfl, center_value, floor_chart, beam_chart,loft_zero]; exact mul_comm ..
lemma specializes (u:P→ℂ)(he:Smooth u): atLoft h z (paneM u he f)= screen u he (atLoft h z f):=by ext1 x; unfold paneM atLoft; rw [restrict_at,screened,Function.comp_apply, floor_chart]; rfl
end YM.Frontier6.Bouquet
