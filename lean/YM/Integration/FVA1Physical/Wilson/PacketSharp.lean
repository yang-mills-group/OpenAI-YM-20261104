import YM.Integration.FVA1Physical.Wilson.PacketEmission
import YM.Integration.FVA1Physical.Wilson.PacketThermal
import YM.Integration.FVA1Physical.Wilson.PacketCrop
import YM.Integration.FVA1Physical.Sources.Round2.ReclockedTwoReserve
import YM.Integration.FVA1Physical.Round2.FieldOrderStability

/-! Compare the physical truncation at exactly the requested order with a
further full normalized Wilson emission. The two reserve orders are used
only to estimate the remainder. No extra incoming source coefficients are
requested. Every background on the fluctuation scale and every period is allowed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Wave
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.Midpoint MSbar.Bakery
open MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Tramp Push.Uniform Next.SectorChange
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem packet_sharp_two (χ:ChartRatio G) (charts:LocalRatio χ) (V:Voice G) (clear:Clear G V)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p s m:ℕ) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0<η) (hp:η<(p:ℝ)+1) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Mosaic.Issue G) (Z:Positions (Primary A.c G)) (b:Site A.f) (T:Nesting G A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x;let g:=A.fClock;let n:=p+2
      ‖g • Z‖ ≤ D*room y → Kind A.T → Expanse A.T 1 n → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s n →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ →
      (mold A.pre A.F A.v).PosDef → BankPaid b y s p m (packetReserve n m (div_pos hη (by norm_num : 0<(8:ℝ)))) T →
      (PowerSeries.coeff 0 T).totalDegree=0 → InheritedPort A χ V n m y (y^pawn n) b Z →
      ∀ (pal:Palisade) (copied:Bool) (U:Config G A.f), U∈A.regionX y b Z V pal →
      |A.modelP y b Z pal V (fun v=>clockReading p g T (chartLog g (packetConfig A V y b Z copied v))) U -
        clockReading p g (emittedRows A χ (enterRows A T) p) Z| ≤ g^((p:ℝ)+1-η) := by
  let n:=p+2
  let hε:0<η/8:=div_pos hη (by norm_num)
  let δ:=packetReserve n m hε
  have small:δ ≤ 1/4:=min_le_left .. 
  have gy:=Work.E09.betaF_growth G P.L
  filter_upwards [packet_emission χ charts V clear simple H H' P K branch n s m (p+2) hD
      (lt_of_le_of_lt small (by norm_num : (1/4:ℝ)<1)),
    packet_thermal_caps V clear χ charts simple H H' P K branch n m s hm hD hε,
    gy.eventually (reclocked_two_reserve p (n+1:ℕ) (by positivity) hη hp),gy.eventually_ge_atTop 2] with x transfer cap clock high
  intro A Z b T eq K0 season y g _ hz kind plane wedge prem crit pd bank flat port pal copied U live
  let Q:=cropAction p T
  have law:=season.case_
  rw [eq] at law
  have y1:1 ≤ y:=by linarith only [high]
  have yp:0<y:=zero_lt_one.trans_le y1
  have budget:=bank.pad yp.le n
  have flatQ:(PowerSeries.coeff 0 Q).totalDegree=0:=by simpa only [Q,cropAction,PowerSeries.coeff_mk,zero_le,if_true] using flat
  have delivered:=transfer A Z b Q eq K0 season hz kind plane wedge prem crit pd budget flatQ _ port pal copied U live
  change |A.modelP y b Z pal V (fun v=>clockReading (p+2) g (cropAction p T) (chartLog g (packetConfig A V y b Z copied v))) U - _| ≤ _ at delivered
  simp_rw [crop_bank_read] at delivered
  have tails:=cap A b eq K0 season kind plane wedge prem crit pd Z Q hz budget
  have β:1 ≤ A.pre.beta:=by linarith only [law.beta,high]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le β))
  have g1:g ≤ 1:=inv_le_one_of_one_le₀ (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt β)
  let top:=picture Z (emittedRows A χ (enterRows A Q) n)
  let bot:=picture Z (emittedRows A χ (enterRows A T) p)
  have lo (i:ℕ)(hi:i ≤ p): PowerSeries.coeff i top=PowerSeries.coeff i bot:=by
    simp only [top,bot,picture,PowerSeries.coeff_map,Q,n,crop_emission_prefix A χ T kind pd p 2 i hi]
  have discarded:=price_after_truncating top bot p 2 gp.le g1 lo (fun i _ hi=>tails i hi)
  have band:lensT y g:=ever yp law.beta law.upper
  have reserve:y^δ*y^(pawn n) ≤ y^(1/4:ℝ)*y^(pawn n) :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le y1 small) (Real.rpow_nonneg yp.le _)
  exact ((abs_sub_le _ _ _).trans (add_le_add delivered discarded)).trans
    ((add_le_add (add_le_add reserve le_rfl) le_rfl).trans (clock g band))

end YM.Integration.FVA1Physical.Wilson
