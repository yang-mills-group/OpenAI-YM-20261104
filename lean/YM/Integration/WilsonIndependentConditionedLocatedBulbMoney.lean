import YM.Integration.WilsonIndependentConditionedLocatedBulb
import YM.Integration.WilsonIndependentConditionedLocatedMesh

/-! Variation of the actual normalized Mer quadrature, including the change
from the measuring lattice unit to the physical test radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedBulbMoney
open Function Set MeasureTheory Metric Lattice Extraction Wilson Maxwell XSpace XSpace.Cirrus
open Table.Pairing WilsonMaxwellThermometerReflectedIncidence
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Layout
open WilsonIndependentConditionedGramBulbProfile (chart profile)
open scoped Classical Topology ContDiff BigOperators
variable {a:Axis}{x:E4}(B:Bulb (site x) a)

theorem ruled {D:ℕ}(φ:Rarity D){t s r:ℝ}(hs:0<s)(hr:0<r)(ratio:1≤r/s)(h:Lattice.Cover)(o:CellR):
    (t/s)^4*(farther ratio φ).ψ.val (Mer.position (t/s) 0 o h)=
      (t/r)^4*φ.ψ.val ((t/r) • actualW h):=by
  rw [show (farther ratio φ).ψ=zoom φ (r/s) from rfl,zoom_at]
  have mul:(r/s)⁻¹*(t/s)=t/r:=by field_simp [ne_of_gt hs,ne_of_gt hr]
  simp only [Mer.position,zero_smul,sub_zero,smul_smul,mul]
  rw [←mul_assoc,←mul_pow,mul_comm (t/s) (r/s)⁻¹,mul]

def mode (D E:ℕ)(δ:ℝ)(o:Fin 2 → Cover):ℂ:=
  ((profile B D true).ψ.val (δ • actualW (o 0))*(profile B E false).ψ.val (δ • actualW (o 1)):ℝ)

theorem bounded:∃M:ℝ,0≤M ∧ ∀y:Points 1,‖B.r y‖≤M:=by
  have con:Continuous B.r:=(B.bump.contDiff_normed (n:=⊤) (μ:=volume)).continuous
  obtain ⟨b,cap⟩:=B.bump.hasCompactSupport.exists_bound_of_continuousOn con.continuousOn
  refine ⟨max 0 b,le_max_left ..,?_⟩
  intro y
  by_cases active:B.r y=0
  · rw [active,norm_zero];exact le_max_left ..
  · have inside:y∈Function.support (B.bump.normed volume):=active
    rw [B.bump.support_normed_eq] at inside
    have supp:y∈tsupport B.bump:=by
      rw [B.bump.tsupport_eq]
      exact Metric.ball_subset_closedBall inside
    exact (cap y supp).trans (le_max_right ..)

theorem original:∃C:ℝ,0≤C ∧ ∀{δ:ℝ},0<δ → 8*δ≤1 → ∀(D E:ℕ)(film:Finset (Fin 2 → Cover)),
    ∑o∈film,‖((δ^8:ℝ):ℂ)*mode B D E δ o‖ ≤ C:=by
  obtain ⟨M,mp,cap⟩:=bounded B
  refine ⟨(M*M)*volume.real (cthickening 1 (WilsonIndependentConditionedLocatedBulb.region B)),by positivity,?_⟩
  intro δ positive fits D E film
  apply WilsonIndependentConditionedLocatedMesh.samples (WilsonIndependentConditionedLocatedBulb.compact B) positive
    (by norm_num at ⊢;exact fits) film (mode B D E δ)
  · intro o _ active
    exact WilsonIndependentConditionedLocatedBulb.located B D E δ o
      (fun zero=>active (by simp [mode,zero]))
  · exact mul_nonneg mp mp
  · intro o _
    simp only [mode,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      WilsonIndependentConditionedGramBulbProfile.value]
    exact mul_le_mul (cap _) (cap _) (abs_nonneg _) mp
end YM.Integration.WilsonIndependentConditionedLocatedBulbMoney
end
