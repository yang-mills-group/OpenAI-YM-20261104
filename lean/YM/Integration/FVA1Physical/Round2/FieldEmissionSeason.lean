import YM.Integration.FVA1Physical.Wilson.ExactOrder
import YM.Integration.FVA1Physical.Wilson.CoarseFieldSchedule

/-! The outgoing polynomial banks for a physical field can be bought on the
same scene that purchases the actual reading. The incoming action is needed
only through the requested order. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Tree Precision
open MSbar MSbar.Mosaic MSbar.Heath MSbar.Heath.Stock MSbar.Whisk MSbar.Lis MSbar.Cacao
open MSbar.CrossH MSbar.Bakery.Film MSbar.Bulk MSbar.Rolling MSbar.Kelvin MSbar.Midpoint
open Exterior RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Push.Uniform
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι]

theorem field_emission_season (J : ι→Lamp G) (V:Voice G) (clear:Clear G V)
    (χ:ChartRatio G) (hχ:LocalRatio χ) (simple:G.Simple) (M:MapPrices)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G) (p s q L:ℕ)
    (part:Bool) {D ε:ℝ} (hD:0≤D) (hε:0<ε) :
    ∀ᶠ x:ℝ in atTop, ∀ A:Issue G, A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ →
      (mold A.pre A.F A.v).PosDef →
      (0≤αm y → αm y≤railWidth M P →
        Syrup (address A.F G) (MSbar.Tramp.path A.S.ratio G) (αm y) s
          (poring A.F A.ρ) (railFee G M P s)) →
      ∀ (b:Site A.c) (z:Positions (Primary A.c G)), ‖z‖≤D → ∀ o:ι→Site A.f,
      (∀ t:Slice J,separation (A.S.ratio.embed b) (legs J o t).1 ≤ L*closeN y) →
      ∀ i≤p, Vault (MSbar.Measuring.chart A.c G) {b} (αm x) s q z
        (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p)) (x^ε) := by
  have half : 0<ε/2 := half_pos hε
  filter_upwards [rail_sale simple M P s q half,
    same_order_field_rows J V clear χ hχ simple H H' P K branch p s q L part hD half,
    (Work.E09.betaF_growth G P.L).eventually_gt_atTop (0:ℝ)] with x sale offers warm
  intro A patch kernel season y kind plane wedge prem crit pd bought b z hz o near i hi
  have stage:A.S.patch.Branches A.S.kernel G :=by simpa only [patch,kernel] using branch
  have beta:=season.case_.beta
  rw [patch] at beta
  have pos : 0<A.fClock := by
    change 0 < (Real.sqrt A.pre.beta)⁻¹
    exact inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos warm).trans_le beta))
  have scaled : ‖A.fClock • z‖ ≤ A.fClock*D := by
    rw [norm_smul,Real.norm_of_nonneg pos.le];exact mul_le_mul_of_nonneg_left hz pos.le
  have fund:=offers A (A.S.ratio.embed b) patch kernel season kind plane wedge (A.fClock•z) scaled o near i hi
  have rail:=bought sale.1 sale.2.1
  have rate : αm x≤αm y*A.S.ratio.count.val := by
    change αm x≤αm (tip G P.L x)*A.S.patch.L.val
    rw [patch]
    exact sale.2.2.1
  have bill:=emitted_rows A χ (jointFieldBank J A o part) p i s q stage prem crit pd b (A.fClock•z)
    sale.1 rate rail fund
  rw [inv_smul_smul₀ pos.ne'] at bill
  exact Quote.widen bill ((sale.2.2.2 q le_rfl).trans_eq (by rw [show 2*(ε/2)=ε by ring])) le_rfl

end YM.Integration.FVA1Physical.Round2.Curvature
