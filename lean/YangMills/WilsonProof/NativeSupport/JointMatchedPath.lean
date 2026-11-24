import YangMills.WilsonProof.NativeSupport.JointStageWord
import YangMills.WilsonProof.NativeSupport.JointContinuousPath

/-! Scalar recursion and terminal mass polynomial for the same frozen Wilson
law. Only interior blocking lags enter the kinetic interpolation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset Lattice RG Wilson Tree RGComparison.Core16 Push.BetaTransport Push.SectorMeasure YM.Pressure MeasureTheory
open WilsonUniformUnmarkedInletEnergySites
open scoped Classical BigOperators Topology
variable {G:Gauge} {n c f:Side}
def fieldTest (d:Descent n c) (δ:ℕ → ℝ) (σ:sites n d → ℝ) (h z:ℝ) (q:sites n d) (u:ℝ):ℝ:=
  Real.exp (-(δ (lag d q)*u))*(1+z*h*σ q*u)

def law (d:Descent n c) (β:ℕ → ℝ) (g:Config G n → ℝ) (δ:ℕ → ℝ) (σ:sites n d → ℝ) (h z:ℝ)
    (V:Config G c):ℝ:=markedOutput d β g (WilsonUniformUnmarkedInletEnergySites.interior d) (fieldTest d δ σ h z) V

theorem law_push (S:StepData c f) (T:Forest S.ratio) (d:Descent n f) (β:ℕ→ℝ) (g:Config G n→ℝ) (δ:ℕ→ℝ)
    (σ:sites n (Descent.push S T d)→ℝ) (h z:ℝ) (V:Config G c) :
    let u:=if 0<d.depth then δ 1 else 0
    let sign (b:Bond c):=if 0<d.depth then σ (.inl b) else 0
    law (.push S T d) β g δ σ h z V =
      JointPhysical.push S univ (fun b e=>Real.exp (-(u*e))*(1+z*h*sign b*e)) (β 1)
        (law d (Descent.upβ β) g (Descent.upβ δ) (σ ∘ Sum.inr) h z) V := by
  intro u sign
  change JointPhysical.push S (Finset.toLeft (interior (Descent.push S T d))) _ _ _ _=_
  rw [middle_head d,middle_tail d]
  by_cases deep:0<d.depth
  · rw [if_pos deep]
    simp only [u,sign,if_pos deep]
    rfl
  · rw [if_neg deep]
    simp only [u,sign,if_neg deep]
    unfold JointPhysical.push
    apply sum_congr rfl;intro k _
    apply integral_congr_ae
    filter_upwards with X
    simp [JointPhysical.integrand,JointPhysical.sample]
    exact Or.inl rfl

theorem scalar_push (S:StepData c f) (β:ℝ) (kTest:Bond c→ℝ→ℝ) (A:Config G f→ℂ) (m lower:Config G f→ℝ)
    (read:∀ X,(m X:ℂ)*A X=(lower X:ℂ)) (Z:Config G c):
    (∑ k:S.Choices,∫ X,(taggedKernel S β k X Z:ℂ)*(A X*((m X*JointPhysical.sample S k univ kTest X Z:ℝ):ℂ)) ∂prior G f)
    =(JointPhysical.push S univ kTest β lower Z:ℝ) := by
  unfold JointPhysical.push
  rw [Complex.ofReal_sum]
  apply sum_congr rfl;intro k _
  rw [←integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with X
  unfold JointPhysical.integrand
  push_cast
  rw [←read X];ring

theorem law_moments (d:Descent n c) (ok:d.OK G) (B Y:ℕ→ℝ) (endValue:Y d.depth=B d.depth)
    {φ:Config G n→ℝ} (ct:Continuous φ) (sym:GaugeInvariant φ) (σ:sites n d→ℝ) (h z:ℝ) (V:Config G c) :
    (law d B φ (fun j=>Y j-B j) σ h z V:ℂ) =
      (d.scalar G B:ℂ)*polynomial (interior d) (moment d Y V (fun q=>h*σ q) φ) (z:ℂ) := by
  let I:=interior d
  let P:=fieldTest d (fun j=>Y j-B j) σ h z
  have kin:kineticOnly d I:=strictly_interior_kinetic d I (fun q mem=>(inside d q).mp mem |>.2)
  have cont (q:sites n d):Continuous (P q):=by unfold P fieldTest;fun_prop
  change (markedOutput d B φ I P V:ℂ)=_
  rw [continuous_path d ok B ct sym I kin P cont V,Complex.ofReal_mul,polynomial_product d ok Y V (fun q=>h*σ q) ct]
  congr 1
  rw [Complex.ofReal_sum]
  apply sum_congr rfl;intro k _
  rw [←integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with X
  rw [pathwise_tilt d B Y endValue k V X φ]
  have cancel (a:ℝ):1+(a-1)=a:=by ring
  simp only [I,P,payload,fieldTest,prod_mul_distrib,cancel,Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_add,Complex.ofReal_one,mul_assoc]
  ring

end YM.Integration.InletSusceptibility.JointMoments
