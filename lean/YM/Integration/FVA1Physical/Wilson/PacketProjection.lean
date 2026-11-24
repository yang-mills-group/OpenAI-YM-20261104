import YM.Integration.FVA1Physical.Wilson.RenderedPort
import YM.Integration.FVA1Physical.Sources.Round2.FieldProjection

/-! The genuine Mosaic projection for the vacuum pays a distributed rooted
Wilson insertion uniformly in period and in its finite coefficient bank.
A constant free coefficient cancels the recoil in the normalized Schur step. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open MSbar.Jade MSbar.Lapaz MSbar.Parma MSbar.Tramp Push.Uniform Next.SectorChange Further.GaussianScalar
open MeasureTheory Matrix Metric YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}

theorem packet_inner (A:Issue G) (T:Nesting G A.f) (V:Voice G) (χ:ChartRatio G)
    (y:ℝ) (b:Site A.f) (U:Config G A.f) (Z:Positions (Primary A.c G)) (p:ℕ)
    (cut:ℝ→ℝ) (color:Site A.f→G.Color) (pos:(mold A.pre A.F A.v).PosDef)
    (kind:Kind A.T) (hg:A.fClock ≠ 0) (flat:(PowerSeries.coeff 0 T).totalDegree=0) :
    Lapaz.localW A.F A.pre A.v V χ (boxX y b) (boxY y b) U A.fClock Z A.T p cut color (enterRows A T) =
      taste p (innerColumn A χ V y (A.fClock•Z) b U (enterRows A T) p) A.fClock := by
  have hseed : (PowerSeries.coeff 0 (enterRows A T)).totalDegree=0 := by
    simp only [enterRows,PowerSeries.coeff_map]
    exact Nat.eq_zero_of_le_zero ((Rolling.clearD ..).trans flat.le)
  have hc : ((pinch (includeX (G:=G) A.F (boxX y b)) (mold A.pre A.F A.v))⁻¹).PosDef :=
    (pos.submatrix (secureY A.F (boxX y b) G)).inv
  unfold Lapaz.localW
  rw [recoil_of_constant_seed _ hc _ _ (Rolling.well A.F A.v χ A.T kind) _ _ _ hseed,add_zero]
  simp only [innerColumn,innerPoint,berth,Matrix.mulVec_zero,add_zero,inv_smul_smul₀ hg]
  rfl

def packetSalary (G:Gauge) (p k:ℕ) : ℝ := max 1 (enterFee G 0^(k*(p+2)))

theorem packetSalary_le {n:Side} (b:Site n) (p k rad:ℕ) (hk:1 ≤ k) {y:ℝ} (ha:0 ≤ αm y) :
    enterFee G 0^(k*(p+2)) ≤ (plateD b (αm y) p 0 (k*(p+2)) k rad (packetSalary G p k))^k := by
  let C:=packetSalary G p k
  let σ:=k*(p+2)
  have hC:1 ≤ C:=le_max_left ..
  have hC0:0 ≤ C:=zero_le_one.trans hC
  have hw:1 ≤ liftW (αm y) 0 rad:=w_start ha 0 _
  have paid:C ≤ plateD b (αm y) p 0 σ k rad C := by
    unfold plateD
    calc C ≤ liftW (αm y) 0 rad*C := le_mul_of_one_le_left hC0 hw
         _ ≤ 2^σ*(liftW (αm y) 0 rad*C):=le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
         _ ≤ ((p+1:ℕ):ℝ)*(2^σ*(liftW (αm y) 0 rad*C)):=le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.succ_pos p)
         _ ≤ 2^k*(((p+1:ℕ):ℝ)*(2^σ*(liftW (αm y) 0 rad*C))):=le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
         _ ≤ 1+_ := le_add_of_nonneg_left zero_le_one
  exact (le_max_right 1 _).trans (paid.trans ((le_of_eq (pow_one _).symm).trans
    (pow_le_pow_right₀ (hC.trans paid) hk)))

theorem packet_projection (χ:ChartRatio G) (charts:LocalRatio χ) (V:Voice G) (clear:Clear G V)
    (P:Palisade) (K:Patch) (H H':RG.Stage) (m p k:ℕ) (hk:1 ≤ k) (u:ℝ) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Issue G) (b:Site A.f) (T:Nesting G A.f) (Z:Positions (Primary A.c G)) (copied:Bool)
      {i:G.ColorIndex} (ages:Ages) (pay:Salary) (cutoff:ℝ→ℝ) {D0 e d B amount cost fund:ℝ},
      let σ:=k*(p+2);let g:=A.fClock;let y:=tip G K.L x;let X:=boxX y b;let Y:=boxY y b
      let O:=postcard G A.c g Z;let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
      K=A.S.patch → Season V H H' x A.pre A.post A.S (courage G K.L x) →
      A.Festival χ p i → Suite V χ A.F X Y O A.v A.pre ν (pillow y) (room y)
        (rot P y) (maxZ G P y) (topP V P y) D0 (linCash A.F (g•Z)) →
      Mosaic.Issue.Calibrate A V P X Y (g•Z) y e d → Lodge.Hat k ages.w B cutoff → m≤σ →
      (∀ n ≤ p,Tokew (address A.F G) (αm y) 0 σ 0 (PowerSeries.coeff n (barbed A.F A.v χ A.T)) amount ∧
        (PowerSeries.coeff n (barbed A.F A.v χ A.T)).totalDegree ≤ σ) →
      Mosaic.Issue.Projection A χ P V ages pay Z p k b y amount (packetSalary G p k) cost fund D0 →
      BankPaid b y 0 p m 0 T → (PowerSeries.coeff 0 T).totalDegree=0 →
      ∀ U∈A.regionX y b Z V P,
      |A.modelP y b Z P V (fun U=>clockReading p g T (chartLog g (packetConfig A V y b Z copied U))) U -
        taste p (innerColumn A χ V y (g•Z) b U (enterRows A T) p) g| ≤
        y^u+Salary.stamp pay p (Fintype.card (Lake A.F X G)) g cost fund := by
  filter_upwards [rendered_packet_port χ charts V clear P K H H' m 0 p 0 u] with x paid
  intro A b T Z copied i ages pay cutoff D0 e d B amount cost fund σ g y X Y O ν patch season fest suite cal hat deg action proj bank flat U hit
  have laws:=season.case_
  rw [←patch] at laws
  have hβ:0<A.pre.beta:=(half_pos (zero_lt_one.trans laws.enough)).trans_le laws.beta
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have ha:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have funded:0 ≤ fund:= (pow_nonneg gp.le (p+1)).trans (by simpa only [Emark,pow_zero,mul_one] using proj.payQ 0 (Nat.zero_le _))
  obtain ⟨_,trend⟩:=fest.preT
  rw [←packet_inner A T V χ y b U Z p cutoff (Ruby.crownP A.F A.M Z) suite.positivity trend.bond gp.ne' flat]
  apply paid A b T Z copied k σ 0 k ages pay cutoff (Ruby.crownP A.F A.M Z) patch season fest suite cal proj.epic hat
    ha le_rfl deg action bank _ funded proj.funds U hit
  simpa only [Real.rpow_zero,mul_one] using packetSalary_le (G:=G) b p k (A.S.patch.L.val*closeN y) hk ha

end YM.Integration.FVA1Physical.Wilson
