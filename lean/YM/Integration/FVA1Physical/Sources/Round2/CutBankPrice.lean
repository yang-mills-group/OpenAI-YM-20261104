import YM.Integration.FVA1Physical.Sources.Round2.BankHatPrice
import YM.Integration.FVA1Physical.Sources.Round2.CopiedSourcePosterior
import YM.Integration.FVA1Physical.Sources.Round2.CopiedHatWindow

/-! Price the true marked outer posterior by the independently iterated
coefficient bank once its copied, normalized Schur conditional has been
priced. The crop and its physical failure probability are paid at this step. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Matrix MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Bulk MSbar.Wave
open MSbar.Rolling MSbar.Mosaic MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal MSbar.Midpoint Push.Uniform
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem posterior_clock (p:ℕ) {η:ℝ} (hη:0<η) (hp:η<(p:ℝ)+1) :
    ∀ᶠ y:ℝ in atTop,∀ g:ℝ,lensT y g →
    2*g^((p:ℝ)+1-η/2)+10*y^(-((p+2:ℕ):ℝ)) ≤ g^((p:ℝ)+1-η) := by
  let a:ℝ:=(1/3:ℝ)^(2/η)
  have a0:0<a:=Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [field_sharp_clock p 10 (by norm_num) (half_pos hη) (by linarith only [hp,hη]),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (2/a),eventually_gt_atTop (0:ℝ)] with y base sy y0
  intro g band
  have root:0<Real.sqrt y:=Real.sqrt_pos.mpr y0
  have g0:0<g:=(half_pos (inv_pos.mpr root)).trans_le band.1
  have gbound:g≤a:=band.2.trans (by
    change 2*(Real.sqrt y)⁻¹ ≤ a
    rw [←div_eq_mul_inv]
    exact (div_le_iff₀ root).mpr ((div_le_iff₀ a0).mp sy |>.trans_eq (mul_comm ..)))
  have small:g^(η/2) ≤ 1/3:=by
    apply (Real.rpow_le_rpow g0.le gbound (half_pos hη).le).trans_eq
    rw [show a^(η/2)=(1/3:ℝ)^((2/η)*(η/2)) from (Real.rpow_mul (by norm_num : (0:ℝ)≤1/3) ..).symm,
      show 2/η*(η/2)=1 by field_simp,Real.rpow_one]
  have up:=base g band
  have tail:10*y^(-((p+2:ℕ):ℝ)) ≤ g^((p:ℝ)+1-η/2):=by
    nlinarith only [up,Real.rpow_nonneg y0.le (pawn (p+2)),mul_nonneg (pow_nonneg g0.le (p+1)) (Real.rpow_nonneg y0.le (η/2/8))]
  have loss:=mul_le_mul_of_nonneg_left small (Real.rpow_nonneg g0.le ((p:ℝ)+1-η))
  rw [←Real.rpow_add g0,show (p:ℝ)+1-η+η/2=(p:ℝ)+1-η/2 by ring] at loss
  linarith only [loss,tail]

theorem cut_bank_sharp (V:Voice G) (cle:Clear G V) (simple:G.Simple) (H H':Stage) (P:Patch)
    (K:KernelChoices) (br:P.Branches K G) (p m:ℕ) {D η:ℝ} (hD:0 ≤ D) (hη:0<η) (hp:η<(p:ℝ)+1) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Issue G),A.S.patch=P → A.S.kernel=K →
    Season V H H' x A.pre A.post A.S (courage G P.L x) →
    let y:=tip G P.L x;let g:=A.fClock
    ∀ (Z:Positions (Primary A.c G)) (b:Site A.f), ‖g•Z‖ ≤ D*room y →
    let O:=postcard G A.c g Z;let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
    let X:=boxX y b;let Y:=boxY y b;let live:=hotel A.F X Y V O μ (pillow y) (room y)
    let copy:=chambers A.F Y V O μ
    ∀ (T:Nesting G A.f) (s:ℕ) (δ W:ℝ), δ ≤ 1/2 → BankPaid b y s p m δ T →
    let φ:=fun U=>clockReading p g T (chartLog g (copy U))
    ∀ pal:Palisade,(∀ U∈live,|A.modelP y b Z pal V φ U-W| ≤ g^((p:ℝ)+1-η/2)) →
    |expect A.S A.pre O (live.indicator φ)-W| ≤ g^((p:ℝ)+1-η) := by
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [cut_source_posterior V cle simple H H' P K br hD (show 0 < ((p+3:ℕ):ℝ) by positivity),
    purchased_hat_window V cle simple H H' P K br hD,rise.eventually (bank_hat_price (G:=G) p m (show 0 < (1/2:ℝ) by norm_num)),
    rise.eventually (posterior_clock p hη hp),rise.eventually_ge_atTop (8:ℝ)] with x period hats bank cost high
  intro A patch kernel season y g Z b width O μ X Y live copy T s δ W small paid φ pal point
  have pc:=season.case_
  rw [patch] at pc
  have y1:1≤y:=by dsimp only [y];linarith only [high]
  have y0:0<y:=zero_lt_one.trans_le y1
  have β:1≤A.pre.beta:=by linarith only [pc.beta,high]
  have g0:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have g1:g ≤ 1:=inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt β)
  have me:Measurable (fun U=>clockReading p g T (chartLog g U)):=(clockReading_continuous ..).measurable.comp (chartLog_meas g)
  have cover:=hats A patch kernel season (g•Z) b width
  have gain:=period A patch kernel season (g•Z) b width _ me (y^(δ+1/2)) W (g^((p:ℝ)+1-η/2))
    (Real.rpow_pos_of_pos y0 _) (Real.rpow_nonneg g0 _)
    (fun U hit=>bank b s δ g T paid (by rwa [abs_of_nonneg g0]) _ (cover U hit)) point
  have balance:(10:ℝ)*y^(δ+1/2)*y^(-((p+3:ℕ):ℝ)) ≤ 10*y^(-((p+2:ℕ):ℝ)):=by
    rw [mul_assoc,←Real.rpow_add y0]
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le y1 _) (by norm_num)
    push_cast;linarith only [small]
  exact gain.trans ((add_le_add le_rfl balance).trans (cost g (ever y0 pc.beta pc.upper)))

end YM.Integration.FVA1Physical.Round2.Curvature
