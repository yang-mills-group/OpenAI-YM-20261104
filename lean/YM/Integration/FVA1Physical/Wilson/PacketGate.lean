import YM.Integration.FVA1Physical.Wilson.PacketSharp
import YM.Integration.FVA1Physical.Wilson.PacketRealized
import YM.Integration.FVA1Physical.Wilson.FluctuationMenu

/-! One threshold pays the complete inherited-packet comparison and the
physical chart simultaneously. Only the order, input degree, weight,
fluctuation multiple and requested loss are fixed before the construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Wave
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.Midpoint MSbar.Bakery
open MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Tramp Push.Uniform Next.SectorChange
open Qlocal.Schedule Next.Foundations YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge}

def sharpPacketGate (V:Voice G) (cle:Clear G V) (hG:G.Simple)
    (p s m:ℕ) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1) : StageThreshold :=
  fun H H' P K=>if br:P.Branches K G then
    max (eventually_atTop.mp (fluctuation_hull G hG P.L hD)).choose
      (eventually_atTop.mp (packet_sharp_two (chart G) (chart_ok G) V cle hG H H' P K br p s m hm hD hη hp)).choose
    else 0

theorem InheritedPort.restrict_degree (A:Issue G) (χ:ChartRatio G) (V:Voice G) {p m M:ℕ}
    {y E:ℝ} (b:Site A.f) (Z:Positions (Primary A.c G)) (port:InheritedPort A χ V p M y E b Z)
    (fit:m ≤ M) : InheritedPort A χ V p m y E b Z :=
  fun pal copied T paid=>port pal copied T (paid.enlarge_degree fit)

theorem gate_packet (V:Voice G) (cle:Clear G V) (hG:G.Simple)
    (p s m:ℕ) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (br:P.Branches K G) {x:ℝ}
    (buy:sharpPacketGate V cle hG p s m hm hD hη hp H H' P K ≤ x)
    (A:Issue G) (b:Site A.f) (Z:Positions (Primary A.c G)) (T:Nesting G A.f)
    (patch:A.S.patch=P) (kern:A.S.kernel=K) (season:Season V H H' x A.pre A.post A.S (courage G P.L x)) :
    let y:=tip G P.L x;let g:=A.fClock;let n:=p+2
    0<y → ‖g•Z‖ ≤ D*room y → Kind A.T → Expanse A.T 1 n → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s n →
    Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ → (mold A.pre A.F A.v).PosDef →
    BankPaid b y s p m (packetReserve n m (div_pos hη (by norm_num : 0<(8:ℝ)))) T → (PowerSeries.coeff 0 T).totalDegree=0 →
    (‖Z‖ ≤ hull x → InheritedPort A (chart G) V n m y (y^pawn n) b Z) →
    ∀ (pal:Palisade) (copied:Bool) (U:Config G A.f), U∈A.regionX y b Z V pal →
    |A.modelP y b Z pal V (fun v=>clockReading p g T (chartLog g (packetConfig A V y b Z copied v))) U -
      clockReading p g (emittedRows A (chart G) (enterRows A T) p) Z| ≤ g^((p:ℝ)+1-η) := by
  rw [sharpPacketGate,dif_pos br] at buy
  intro y g n yp hz kind plane wedge prem crit pd bank flat port
  have law:=season.case_
  rw [patch] at law
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos yp).trans_le law.beta))
  have roomCap:=(eventually_atTop.mp (fluctuation_hull G hG P.L hD)).choose_spec x ((le_max_left ..).trans buy)
    g (Mosaic.ever yp law.beta law.upper)
  have bounded:‖Z‖ ≤ hull x:=by
    apply (mul_le_mul_iff_right₀ gp).mp
    simpa only [norm_smul,Real.norm_of_nonneg gp.le] using hz.trans roomCap
  exact (eventually_atTop.mp (packet_sharp_two (chart G) (chart_ok G) V cle hG H H' P K br p s m hm hD hη hp)).choose_spec x
    ((le_max_right ..).trans buy) A Z b T patch kern season hz kind plane wedge prem crit pd bank flat (port bounded)

end YM.Integration.FVA1Physical.Wilson
