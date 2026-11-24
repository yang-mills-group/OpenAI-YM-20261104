import YM.Integration.FVA1Physical.Wilson.PacketTail
import YM.Integration.FVA1Physical.Wilson.PacketOn

/-! Pass the true normalized resampling estimate to the entire, uncut
physical Haar conditional. All distant exterior fields and all local
failure modes are integrated against the original incoming vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Lis MSbar.Mosaic MSbar.Bulk
open MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Midpoint Push.Uniform
open Qlocal.Schedule YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem full_packet_release (V:Voice G) (cle:Clear G V) (simple:G.Simple) (H H':Stage) (P:Patch)
    (K:KernelChoices) (branch:P.Branches K G) (p m s:ℕ) {D η:ℝ} (hD:0 ≤ D) (hη:0<η) (hp:η<(p:ℝ)+1) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Issue G),A.S.patch=P → A.S.kernel=K →
    Season V H H' x A.pre A.post A.S (courage G P.L x) →
    let y:=tip G P.L x;let g:=A.fClock
    ∀ (Z:Positions (Primary A.c G)) (b:Site A.f),‖g•Z‖ ≤ D*room y →
    ∀ (T:Nesting G A.f) (δ W:ℝ),δ ≤ 1/2 → BankPaid b y s p m δ T →
    (∀ (pal:Palisade) (U:Config G A.f),U∈A.regionX y b Z V pal →
      |A.modelP y b Z pal V (fun v=>clockReading p g T (chartLog g (packetConfig A V y b Z true v))) U-W| ≤
        g^((p:ℝ)+1-(η/2)/2)) →
    |expect A.S A.pre (postcard G A.c g Z) (fun v=>clockReading p g T (chartLog g (canoe (S:=A.S) A.F v)))-W| ≤
      g^((p:ℝ)+1-η) := by
  have hhalf:η/2<(p:ℝ)+1:=(half_lt_self hη).trans hp
  let debit:ℝ:=-((p+2:ℕ):ℝ)
  let pal:=(purchased_fluctuation_chance V cle simple H H' P K branch hD debit).choose
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [packet_tail_season V cle simple H H' P K branch p m s hD debit,
    cut_bank_sharp V cle simple H H' P K branch p m hD (half_pos hη) hhalf,
    rise.eventually (posterior_clock p hη hp),rise.eventually_gt_atTop 0]
    with x uncut cut spend warm
  intro A hp' hk season y g Z b width T δ W small bank point
  have law:=season.case_
  rw [hp'] at law
  have clock:lensT y g:=Mosaic.ever warm law.beta law.upper
  have move:=uncut A hp' hk season Z b width δ (small.trans (by norm_num)) T bank
  have paid:=cut A hp' hk season Z b width T s δ W small bank pal (point pal)
  have a:=Real.rpow_nonneg warm.le debit
  have b0:=Real.rpow_nonneg ((half_pos (inv_pos.mpr (Real.sqrt_pos.mpr warm))).trans_le clock.1).le
    ((p:ℝ)+1-η/2)
  exact ((abs_sub_le _ _ _).trans (add_le_add ((abs_sub_comm _ _).le.trans move) paid)).trans
    ((show 2*y^debit+g^((p:ℝ)+1-η/2) ≤ 2*g^((p:ℝ)+1-η/2)+10*y^debit by linarith only [a,b0]).trans (spend g clock))

def fullPacketGate (V:Voice G) (cle:Clear G V) (simple:G.Simple) (p s m:ℕ) (hm:1 ≤ m)
    {D η:ℝ} (hD:0 ≤ D) (hη:0<η) (hp:η<(p:ℝ)+1) : StageThreshold :=
  fun H H' P K=>max
    (sharpPacketGate V cle simple p s m hm hD (half_pos (half_pos hη))
      ((half_lt_self (half_pos hη)).trans ((half_lt_self hη).trans hp)) H H' P K)
    (if br:P.Branches K G then (eventually_atTop.mp
      (full_packet_release V cle simple H H' P K br p m s hD hη hp)).choose else 0)

end YM.Integration.FVA1Physical.Wilson
