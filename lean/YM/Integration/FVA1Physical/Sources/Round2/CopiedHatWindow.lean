import YM.Integration.FVA1Physical.Wilson.FluctuationPurchase
import YM.Integration.FVA1Physical.Round2.StageThreshold

/-! The actual local gauge copy is uniformly in the logarithmic coordinate
window used by the measured source reset. The cutoff for the chart witness is
paid with the two native stage profiles, before the background or period. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Set Finset Lattice RG YM.Wilson Precision Exterior MSbar MSbar.Bulk MSbar.Heath MSbar.Heath.Cottage
open MSbar.Heath.Stock MSbar.Mosaic MSbar.Lis MSbar.Midpoint Push.Uniform Tree Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G:Gauge}

theorem purchased_hat_window (V:Voice G) (cle:Clear G V) (simple:G.Simple) (H H':Stage)
    (P:Patch) (K:KernelChoices) (branch:P.Branches K G) {D:ℝ} (hD:0 ≤ D) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Issue G),A.S.patch=P → A.S.kernel=K →
    Season V H H' x A.pre A.post A.S (courage G P.L x) →
    ∀ (Z:Positions (Primary A.c G)) (b:Site A.f), ‖Z‖ ≤ D*room (tip G P.L x) →
    let y:=tip G P.L x;let X:=boxX y b;let Y:=boxY y b
    let O:=represent (tint G (Body 1 A.c) Z);let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) Z
    ∀ W∈hotel A.F X Y V O μ (pillow y) (room y),
    ‖chartLog A.fClock (chambers A.F Y V O μ W)‖ ≤ hatW y/32 := by
  obtain ⟨pal,buy⟩:=purchased_fluctuation_chance V cle simple H H' P K branch hD 0
  have cost:0 ≤ fluctuationFee pal V D:=by
    unfold fluctuationFee ceilingP; have:= zero_le_one.trans cle.cost; have:0 ≤ shade G:=(shade_pos G).le; positivity
  filter_upwards [buy,(Work.E09.betaF_growth G P.L).eventually (hotel_scalar 0 _ le_rfl cost)] with x offer cap
  intro A hp hk season Z b width y X Y O μ W live
  have radius:=(offer A hp hk season Z b width).2.2.1 W live
  have pc:=season.case_
  rw [hp] at pc
  have pos:=zero_lt_one.trans pc.enough
  have hg:0 < A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos pos).trans_le pc.beta))
  have wood:=cap A.fClock (ever pos pc.beta pc.upper)
  apply radius.2.trans ((div_le_iff₀ hg).mpr ?_)
  simpa only [zero_mul,zero_add,vol,mul_comm A.fClock] using wood

def copyHatGate (V:Voice G) (cle:Clear G V) (simple:G.Simple) : StageThreshold :=
  fun H H' P K=>if b:P.Branches K G then (eventually_atTop.mp
    (purchased_hat_window V cle simple H H' P K b (Nat.cast_nonneg H.order))).choose else 0

abbrev copyHatInvoice (V:Voice G) (cle:Clear G V) (simple:G.Simple) : Goal G :=
  selectedThreshold (G:=G) (copyHatGate V cle simple)

theorem copyHat_obtainable (V:Voice G) (cle:Clear G V) (simple:G.Simple) :
    Obtainable (copyHatInvoice V cle simple) := selectedThreshold_obtainable _

end YM.Integration.FVA1Physical.Round2.Curvature
