import YM.Integration.FVA1Physical.Round2.FieldPacketLinearity
import YM.Integration.FVA1Physical.Wilson.IteratedBankGate
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock

/-! Homogeneity of both readings uses the original measured vacuum and the
independently normalized formal action. It allows a subpower priced input. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Set Filter Finset Matrix MeasureTheory MvPolynomial Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Rolling MSbar.Kelvin MSbar.Lapaz MSbar.Tramp Push.Uniform
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge}

theorem bank_paid_normalize {f:Side} (b:Site f) {y δ:ℝ} (hy:0<y) {s p m:ℕ} {T:Nesting G f}
    (bank:BankPaid b y s p m δ T) : BankPaid b y s p m 0 ((y^δ)⁻¹ • T) := by
  have pos:=Real.rpow_pos_of_pos hy δ
  intro i hi
  rw [PowerSeries.coeff_smul]
  refine ⟨(MvPolynomial.totalDegree_smul_le ..).trans (bank i hi).1,?_⟩
  have eqn: |(y^δ)⁻¹| * (y^δ)=y^(0:ℝ):=by rw [Real.rpow_zero,abs_of_pos (inv_pos.mpr pos),inv_mul_cancel₀ pos.ne']
  exact eqn ▸ Quote.mulR (bank i hi).2 _

theorem bank_clock_smul {σ:Type} (p:ℕ) (a g:ℝ) (T:PowerSeries (Pot σ)) (Z:View σ) :
    clockReading p g (a • T) Z = a*clockReading p g T Z := by
  unfold clockReading taste picture
  simp only [PowerSeries.coeff_map,PowerSeries.coeff_smul,eval_real_smul,Finset.mul_sum]
  apply sum_congr rfl;intro i _;ring

theorem model_smul (A:Issue G) (y:ℝ) (b:Site A.f) (Z:Positions (Primary A.c G))
    (P:Palisade) (V:Voice G) (φ:Config G A.f→ℝ) (a:ℝ) (U:Config G A.f) :
    A.modelP y b Z P V (fun v=>a*φ v) U=a*A.modelP y b Z P V φ U := by
  unfold Mosaic.Issue.modelP Rota.resample
  rw [←integral_const_mul];apply integral_congr_ae
  filter_upwards with t;unfold Rota.ghat;ring

theorem enter_smul (A:Issue G) (T:Nesting G A.f) (a:ℝ) : enterRows A (a • T)=a • enterRows A T := by
  apply PowerSeries.ext;intro i
  simp only [enterRows,PowerSeries.coeff_map,PowerSeries.coeff_smul]
  exact (rail (taps A.F G)).toLinearMap.map_smul a (PowerSeries.coeff i T)

theorem inner_smul (A:Issue G) (V:Voice G) (χ:ChartRatio G) (y:ℝ) (b:Site A.f)
    (U:Config G A.f) (Z:Positions (Primary A.c G)) (p:ℕ) (g a:ℝ) (T:Nesting G A.f)
    (kind:Kind A.T) (pos:(mold A.pre A.F A.v).PosDef) :
    taste p (innerColumn A χ V y Z b U (enterRows A (a • T)) p) g =
      a*taste p (innerColumn A χ V y Z b U (enterRows A T) p) g := by
  have hp:= (pos.submatrix (secureY A.F (boxX y b) G)).inv
  let K:=vene (boxX y b) A.F G
  let D:=(pinch (includeX (G:=G) A.F (boxX y b)) (mold A.pre A.F A.v))⁻¹
  let Q:=barbed A.F A.v χ A.T
  let src:=enterRows A T
  have linear (i:ℕ)(hi:i≤p) : PowerSeries.coeff i (growP Q (a • src) (K*D*K.transpose) (p+1))=
        a • PowerSeries.coeff i (growP Q src (K*D*K.transpose) (p+1)) := by
    simpa only [D,MSbar.Kelvin.pinch,Finset.sum_singleton] using grown_packet_sum K hp Q (Rolling.well A.F A.v χ A.T kind)
      p i hi {()} (fun _ : Unit=>src) (fun _=>a)
  rw [enter_smul]
  unfold innerColumn Lapaz.owes taste picture
  simp only [PowerSeries.coeff_map,Finset.mul_sum]
  apply sum_congr rfl;intro i hi
  rw [linear i (Nat.lt_succ_iff.mp (mem_range.mp hi)),eval_real_smul];ring

end YM.Integration.FVA1Physical.Wilson
