import YM.Integration.FVA1Physical.Wilson.PacketBulk
import YM.Integration.FVA1Physical.Wilson.PacketSubpower

/-! Nonbare physical projection of an incoming distributed Wilson observable,
in the stationary full-volume geometry of the next emitted coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.Midpoint MSbar.Bakery
open MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Tramp Push.Uniform Next.SectorChange
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem packet_emission (χ:ChartRatio G) (charts:LocalRatio χ) (V:Voice G) (clear:Clear G V)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p s degree q:ℕ) {D δ:ℝ} (hD:0 ≤ D) (hδ:δ<1) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Mosaic.Issue G) (Z:Positions (Primary A.c G)) (b:Site A.f) (T:Nesting G A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x;let g:=A.fClock
      ‖g • Z‖ ≤ D*room y → Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ →
      (mold A.pre A.F A.v).PosDef → BankPaid b y s p degree δ T → (PowerSeries.coeff 0 T).totalDegree=0 →
      ∀ E:ℝ, InheritedPort A χ V p degree y E b Z → ∀ (pal:Palisade) (copied:Bool) (U:Config G A.f), U∈A.regionX y b Z V pal →
      |A.modelP y b Z pal V (fun v=>clockReading p g T (chartLog g (packetConfig A V y b Z copied v))) U -
        clockReading p g (emittedRows A χ (enterRows A T) p) Z| ≤
        y^δ*E+(p+1:ℕ)*y^(-(q:ℝ)) := by
  filter_upwards [packet_bulk χ charts V clear simple H H' P K branch p s degree q hD hδ,
    (Work.E09.betaF_growth G P.L).eventually_gt_atTop 0] with x outer high
  intro A Z b T patch kernel season y g hz kind span wedge prem crit pd paid flat E port pal copied U hit
  exact (abs_sub_le _ _ _).trans (add_le_add
    (subpower_port A p degree high b Z V χ kind pd port pal copied T (paid.weaken_weight (Nat.zero_le _)) flat U hit)
    (outer A Z b T patch kernel season hz kind span wedge prem crit pd paid pal U hit))

end YM.Integration.FVA1Physical.Wilson
