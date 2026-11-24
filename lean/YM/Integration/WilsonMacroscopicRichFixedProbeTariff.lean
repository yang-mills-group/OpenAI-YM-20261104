import YM.Integration.WilsonMacroscopicRichIssuedCurrency
import YM.Integration.WilsonMacroscopicRichMeasuredProbe

/-! A fixed finite family of true nonlinear probes prices the physical class of any submitted lower germ. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFixedProbeTariff
open Function Set Filter Spec OPE OPE.Orbits PhysMS Lattice Wilson RG
open Trace.Physical.GermGraph RG16 RG16.Literal Next.UVStress Push.Local
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}

def issued (H:C.Makes)(S:Table C.book){h u N p:ℕ}(door:Opened C h u p)(uN:u≤N):
    C.label h→ₗ[ℂ] S.Field h:=
  (S.project h).comp ((C.factory h N p).terminal.toLinearMap.comp
    (fitting h N p u H door uN).symm.toLinearMap)

theorem purchased (H:C.Makes)(S:Table C.book)(h:ℕ):
    ∃P:Finset (Probe G h),∀u:ℕ,∀doors:∀p,Opened C h u p,∃L:ℝ,0≤L ∧
    ∀N p (uN:u≤N) (x y:C.label h)(c:ℝ),0≤c →
    (∀t∈P,‖runProbe (C.labels.level h) t x-runProbe (C.labels.level h) t y‖≤c) →
    ‖issued H S (doors p) uN x-issued H S (doors p) uN y‖≤L*c:=by
  obtain ⟨P,K,kk,enough⟩:=probe_budget (C.labels.level h)
  let π:=(S.project h).toContinuousLinearMap
  refine ⟨P,?_⟩
  intro u doors
  obtain ⟨A,nn,buy⟩:=quota_stop C H (doors 0).post
  refine ⟨‖π‖*(A*2*K),mul_nonneg (π.opNorm_nonneg) (mul_nonneg (mul_nonneg nn zero_le_two) (zero_le_one.trans kk)),?_⟩
  intro N p uN x y c hc tested
  rw [←map_sub]
  let f:=fitting h N p u H (doors p) uN
  let b:=f.symm (x-y)
  let T:=(C.factory h N p).terminal
  have lim: (C.labels.level h).coeffSize (x-y)≤K*c:=enough _ _ hc (fun t ht=>by rw [map_sub];exact tested t ht)
  have cost:quota C h u N p (T b)≤2*((C.labels.level h).coeffSize (x-y)):=by
    unfold quota
    change (C.labels.level h).coeffSize ((C.factory h N p).entries u (T.symm (T b))).x ≤ _
    rw [T.symm_apply_apply]
    have source: (C.labels.level h).coeffSize ((C.factory h N p).entries u b).x≤2*((C.labels.level h).coeffSize (f b)):=
      (size_gap h N p u H (doors p) uN b).2
    simpa only [b,f.apply_symm_apply] using source
  change ‖π (T b)‖≤_
  calc
    _ ≤ ‖π‖*(A*(2*(K*c))) := (π.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((buy N p (T b) uN).trans (mul_le_mul_of_nonneg_left (cost.trans
        (mul_le_mul_of_nonneg_left lim zero_le_two)) nn)) (π.opNorm_nonneg))
    _ = _ := by ring

end YM.Integration.WilsonMacroscopicRichFixedProbeTariff
