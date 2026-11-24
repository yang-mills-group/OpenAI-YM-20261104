import YM.Integration.WilsonPublicForkIndependentWindow
import YM.Integration.WilsonMacroscopicRichTestGeometry

/-! The independently prescribed coefficients at the genuine two-scale
placement use the same measuring coupling and the relative reflected profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentPlacement
open Filter Function Set MeasureTheory FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open FVA2.O.Project FVA2.Scale FVA2.Register Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater MS.Rake PhysMS Trace.Pilot
open WilsonPublicForkIndependentWindow WilsonPublicForkIndependentDecay WilsonMacroscopicRichTestGeometry
open scoped Classical Topology BigOperators
variable {G:Gauge}{n m:ℕ}
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

def age (A:ℕ)(z:ℝ):ℝ:=(2*(A:ℝ))*(-Real.log z)
def slope (A:ℕ):ℝ:=(2*(A:ℝ))⁻¹

theorem same_clock {A:ℕ}(ap:0<A){z:ℝ}(zp:0<z):
    measuring (slope A) (age A z)=z ∧ Real.exp (age A z)=((z^A)^2)⁻¹:=by
  have pos:0<(A:ℝ):=by exact_mod_cast ap
  constructor
  · have eq:-(slope A)*age A z=Real.log z:=by unfold slope age;field_simp
    rw [measuring,eq,Real.exp_log zp]
  · have eq:age A z=Real.log ((z^A)^2)⁻¹:=by
      unfold age;rw [Real.log_inv,Real.log_pow,Real.log_pow];push_cast;ring
    rw [eq,Real.exp_log (by positivity)]

theorem outside (φ:Test 2):(relative '' tsupport φ)⊆Outside 1:=by
  have no:=(WilsonMacroscopicRichTestGeometry.support φ).2
  intro y hy i j eq
  fin_cases i <;> fin_cases j <;> first | rfl | exfalso;apply no y hy;first | exact eq | exact eq.symm

include ν ms in
theorem original (g:ℝ→ℝ)(physical:Coupling G g)(h q P A:ℕ)(reserve:P<A)(order:P+A*(2*h+1)<q+1)
    (u:Scan G n)(v:Scan G m)(K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)
    (L:Set (Points m))(far:IsCompact L)(spread:L⊆Outside m):
    ∀ᶠ r in trail,let t:=r/((g r)^A)^2;
      0<t ∧ Real.exp (age A (g r))=t/r ∧ measuring (slope A) (age A (g r))=g r ∧
      ∀x∈K,∀y∈L,‖contrast Z h q (slope A) u v x y (age A (g r))‖≤(g r)^(P+A*(2*h+1)):=by
  have ap:0<A:=by omega
  have ap':0<(A:ℝ):=by exact_mod_cast ap
  have tp:0<slope A:=inv_pos.mpr (by positivity)
  have logtime:Tendsto (fun r=>-Real.log (g r)) trail atTop:=tendsto_neg_atTop_iff.mpr
    (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨physical.conforms simple,physical.positive⟩))
  have route:Tendsto (fun r=>age A (g r)) trail atTop:=logtime.const_mul_atTop (by positivity)
  have feasible:slope A*(↑(P+A*(2*h+1)):ℝ)<(h:ℝ)+1:=by
    have res:(P:ℝ)<A:=by exact_mod_cast reserve
    unfold slope;rw [inv_mul_eq_div,div_lt_iff₀ (by positivity)];push_cast;nlinarith
  have wage:=route.eventually (rate Z M ν ms h q _ _ tp feasible order u v K closed inside L far spread)
  filter_upwards [wage,physical.positive,self_mem_nhdsWithin] with r paid gp rp
  have rpos:0<r:=rp
  have ⟨temperature,position⟩:=same_clock ap gp
  dsimp only
  refine ⟨by positivity,?_,temperature,?_⟩
  · rw [position];field_simp
  · simpa only [temperature] using paid

include ν ms in
theorem reflected (g:ℝ→ℝ)(physical:Coupling G g)(h q P A:ℕ)(reserve:P<A)(order:P+A*(2*h+1)<q+1)
    (u:Scan G n)(v:Scan G 1)(K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)(φ:Test 2):
    ∀ᶠ r in trail,∀x∈K,∀z∈tsupport φ,
      ‖contrast Z h q (slope A) u v x (relative z) (age A (g r))‖≤(g r)^(P+A*(2*h+1)):=by
  filter_upwards [original Z M ν ms g physical h q P A reserve order u v K closed inside
    _ (WilsonMacroscopicRichTestGeometry.support φ).1 (outside φ)] with r paid x hx z hz
  exact paid.2.2.2 x hx _ ⟨z,hz,rfl⟩

end YM.Integration.WilsonPublicForkIndependentPlacement
