import YM.Integration.WilsonMarkedGaugeCurves
import YM.RegulatorIR.Ward.Eddy

/-! The native orbifold regulator uses one coordinate per edge orbit on its
enlarged torus. Both of its actual coupled rays are lifted before the gauge
identity is applied to the original filed marked coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedRegulatorGaugeRays
open Function Filter Finset Lattice RG Laurent Wilson PertExtension Orb
open FormalBulk08 Reef Jets Kemp Stationary AllOrder AllOrder.Haiku
open WilsonCoeffUV WilsonCoeffUV.Mer RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Laplace RegulatorIR.Binding RegulatorIR.Ward
open AllOrder.Response AllOrder.Laplace.SigmaP PositionX.Jet PertExtension.Series
open WilsonFormalGaugeCurve
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{k:ℕ}{K:Era G V}

def lift: (Horizon G n)→L[ℝ](Link G n):= edgeColor.symm.toContinuousLinearMap.comp
  (LinearMap.toContinuousLinearMap {
    toFun:=RegulatorIR.Binding.fire
    map_add' x y:=by funext e;by_cases h:eR e=e <;> simp [fire,h,Pi.add_apply,add_comm]
    map_smul' t x:=by funext e;by_cases h:eR e=e <;> simp [fire,h,Pi.smul_apply] })

theorem lifted (v:ℝ→ Horizon G n)(t:ℝ):life (lift ∘ v) t=orbLift (climb (t • v t)):=by
  ext1 e
  change input G n (t • lift (v t)) e=_
  rw [input_color,← lift.map_smul t (v t)]
  have asColor:edgeColor (lift (t • v t))=fire (t • v t):=edgeColor.apply_symm_apply _
  rw [asColor]
  unfold fire orbLift liftLinks
  split
  · rfl
  · rw [Work.F03.exp_neg_color];rfl

theorem original (bought:Auth k K)(o:Loc G 1)(f:V→L[ℝ]ℝ)
    (x y:ℝ→ Horizon G n)(hx:ContDiffAt ℝ ω x 0)(hy:ContDiffAt ℝ ω y 0)
    (meeting:reel_prop x y)(i:ℕ):
    let v:=lift ∘ y
    let w:=lift ∘ x
    let paid:=tuftV f K
    let live:=WilsonCoeffUV.Blue.flash (paid.1 n)
    let folded:=Kemp.banner k paid.2 n
    weigh v (evaluation live) i=weigh w (evaluation live) i ∧
    weigh v (evaluation folded) i=weigh w (evaluation folded) i:=by
  intro v w paid live folded
  have reads:∀ᶠ t in 𝓝 (0:ℝ),∃q:Site n→G.El,life w t=Lattice.gauge q (life v t):=by
    filter_upwards [meeting] with t ht
    obtain ⟨q,hq,eq⟩:=ht
    exact ⟨q,by rw [show life w t=orbLift (climb (t • x t)) from lifted x t,show life v t=orbLift (climb (t • y t)) from lifted y t,eq,goat_lift _ _ hq]⟩
  have hv:ContDiffAt ℝ ω v 0:=lift.contDiff.contDiffAt.comp 0 hy
  have hw:ContDiffAt ℝ ω w 0:=lift.contDiff.contDiffAt.comp 0 hx
  exact ⟨WilsonMarkedGaugeCurves.original live (WilsonPointChildFullGauge.submitted bought n f.toLinearMap) v w hv hw reads i,
    WilsonMarkedGaugeCurves.original folded (WilsonMarkedCoveredGauge.published bought o f n) v w hv hw reads i⟩

end YM.Integration.WilsonMarkedRegulatorGaugeRays
end
