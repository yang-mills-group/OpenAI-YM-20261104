import YM.Integration.WilsonPositionCorrectedCap
import YM.Integration.WilsonPositionPrescribedNested
import YM.Integration.WilsonPositionOriginalDiagnosticPurse

/-! The elected position change is an admissible physical leading frame on the old
funded hierarchy. Its independent root comparison asks only for signed film values
on the original finite nested test panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositivePursePosition
open Function Filter Set Finset Spec Climb Next.UVStress OPE OPE.Orbits PhysMS Trace.Pilot RG17
open PhysicalNext.Repeat.Legato XSpace XSpace.Normalize Maxwell FVA2 FVA2.Arrival
open MS MS.Land MS.Local.Physical MS.Menus MS.Theater
open WilsonPositionPrescribedScreen WilsonPositionPrescribedFrame WilsonPositionPrescribedFormalTest
open WilsonPositionOriginalDiagnosticRead WilsonPositionOriginalDiagnosticPurse
open Asymptotics
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (V : Store G)
    (lead : PhysMS.Leading F J) {H : (Bel R.family.book).Hierarchy}
    (paid : ∀ d, ∀ᶠ r in trail, PhysMS.Frame.obedient F H (J r) d)

include lead paid in
theorem leading : PhysMS.Leading F (positioned F J V) := by
  constructor
  · intro d
    filter_upwards [lead.equivariant d] with r old
    have new := WilsonPositionCorrectedCap.signed F J V (Maxwell.Free.spin_free R.family.labels) d r
    exact ⟨fun s v => (congrArg (J r d) (new.signed s v)).trans (old.1 s _),
      fun v => (congrArg (J r d) (new.stars v)).trans (old.2 _)⟩
  · intro d e de
    let X := Maxwell.Free.scheme R.family.labels
    let Y := F.sector.derivatives
    induction e,de using Nat.le_induction with
    | base =>
      refine Eventually.of_forall fun r v => ?_
      have hi : X.rise (le_refl d) v = v :=
        Maxwell.Free.address_inj R.family.labels d (Maxwell.Free.address_rise R.family.labels d _ v)
      rw [hi,Y.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection]
    | succ e de ih =>
      filter_upwards [ih,WilsonPositionPrescribedNested.transported F J lead V (positioned F J V)
        (fun d r h v => congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J V h v)) e] with r prior adj v
      have hi : X.rise (Nat.le_succ e) (X.rise de v) = X.rise (de.trans (Nat.le_succ e)) v := by
        apply Maxwell.Free.address_inj R.family.labels (e+1)
        simp only [X,Maxwell.Free.address_rise]
      rw [←hi,adj,prior,Y.transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]
  · intro d
    filter_upwards [lead.unit d] with r ok
    exact (congrArg (J r d) (WilsonPositionThermometerCorrectedUnit.corrected_unit F J V d r)).trans ok
  · intro n d v j K hK hs
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [WilsonPositionPrescribedLeading.jets F J V lead paid d v j hK hs (half_pos hε)]
      with r hr x hx
    rw [dist_comm,dist_eq_norm]
    exact (hr x hx).trans_lt (half_lt_self hε)

variable (Z : Deck G) (ν : ℝ) (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (d q : ℕ) (g : ℝ → ℝ)

def checked : Prop :=
  ∀ (i : Fin (V.survey d).n) (k : Fin ((V.survey d).scope i).n → Pin G d)
    (a : Fin ((V.survey d).scope i).n → Glyph Z d),
    (fun r => reading Z (hierarchy F J d r) (fixed V i k) a -
      reading Z (raw ν T d q (g r)) (fixed V i k) a) =o[trail] (fun r => g r^q)

include lead in
theorem root (small : Tendsto g trail (𝓝 0)) (samples : checked F J V Z ν T d q g) :
    (fun r => guide G d (correction F J V d r) -
      WilsonPositionPrescribedRootPrice.native V ν T d q (g r)) =o[trail] (fun r => g r^q) := by
  have invoices : (fun r => invoice Z V (hierarchy F J d r) (raw ν T d q (g r)))
      =o[trail] (fun r => g r^q) := by
    apply IsLittleO.sum
    intro i _
    apply IsLittleO.sum
    intro k _
    apply IsLittleO.sum
    intro a _
    exact (samples i k a).norm_left.const_mul_left _
  obtain ⟨L,A,hL,hA,price⟩ := WilsonPositionOriginalDiagnosticPurse.original Z V ν T q F J lead small (d:=d)
  have higher : (fun r => |g r|^(q+1)) =o[trail] (fun r=>g r^q) := by
    apply IsLittleO.of_bound
    intro ε hε
    have h₀ : Tendsto (fun r => |g r|) trail (𝓝 0) := by simpa using small.abs
    filter_upwards [(tendsto_order.mp h₀).2 ε hε] with r hr
    simpa only [Real.norm_eq_abs,abs_pow,abs_abs,pow_succ,abs_mul,mul_comm (|g r|^q)] using
      (mul_le_mul_of_nonneg_right hr.le (pow_nonneg (abs_nonneg (g r)) q))
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [price,((invoices.const_mul_left L).add (higher.const_mul_left A)).bound hε] with r h hsum
  exact h.trans ((Real.le_norm_self _).trans hsum)

end YM.Integration.WilsonPositivePursePosition
