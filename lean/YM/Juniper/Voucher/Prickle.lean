import YM.Juniper.Voucher.Tokens
import YM.UVExtension.Camp.Pin
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open UVExtension
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
open Oriel Charted Dales Tour
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    {N m n : ℕ}{Q ε θ b C W u:ℝ}
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
variable (T:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T'"=> (A.B.a.params m)
local notation "P₀"=> Dales.mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
local notation "σ"=> Time.forecastE A.B.a m
local notation "s"=> (A.B.a.budget m)
local notation "φ"=> A.B.kin.alpha N m
local notation "B'"=> A.B.a.clock.hatBeta m
local notation "Ω"=> D.L (J)
variable {z' δ:ℝ} (hθ:Paperwork R.shape ε u A.delay)
local notation "i₀"=> A.B.a.clock.J m
local notation "χ"=> z'
local notation "ρ"=> (T').width
local notation "λ₁"=> (T').paths
local notation "Υ"=> regularNeed G s (T').clip ρ λ₁ φ δ
local notation "U'"=> regularNeed G s (T').clip ρ λ₁ 0 (Q+χ)+χ
local notation "F₀"=> (B).clock.allowance m
include H hθ
lemma tighten (hu:u ≤ Camp.soft)(hz:δ≤ (2*rim)*σ)(hb:0<b)(hf:Q ≤ rim*b*σ)(he:χ ≤ rim*b*σ): Υ ≤ (rim/4)*F₀ ∧ U' ≤ (rim/8)*(b* F₀):= by
    let K':= Time.base G (T')
    have hQ:=Time.base_nonneg G T'; obtain ⟨hp,hc⟩:= (Time.authorized G T'); have hσ:(s).threshold < 2:= lt_of_le_of_lt (s).threshold_le (by norm_num : (1:ℝ)<2)
    -- post H clamp. invoke Shaft calibration from gripped operator setup; α table reservation. Don't double count Born budget.
    have hy: Time.top G T' * (|φ| * (s).threshold^3) ≤ u*F₀ := by
       have h: (s).threshold ≤ 2*Pressure.fiery G B' Ω:= by rw [← H.atTopH.laws.data.funds.length_eq]; exact H.atTopH.laws.data.room.temperatures
       have hp:=Rain.jersey (A:=A) (m:=m); let p':= X.p.profile i₀; let hz:= params_eq A.B.valid m
       obtain ⟨ha,hx,hf⟩:= (hθ.chord _ _ (step_paid B m) _ (A.B.valid.pays m)|>.2.2).lifts s ⟨hp.2.1,hp.1,hp.2.2.1⟩ rfl rfl h
       have he:= (hf _ (show _ from Boulevard.coupling A N m H.hm)).2; unfold Yard.priceE at he; rw [Time.table G _ (show Time.Same p' s from ⟨hp.2.1,hp.1,hp.2.2.1⟩),Time.table G _ (show Time.Same p' s from ⟨hp.2.1,hp.1,hp.2.2.1⟩)] at he; simp only [mul_zero,zero_add,abs_zero,zero_mul,add_zero,mul_one] at he; rw [params_eq A.B.valid]; exact le_trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) (Time.base_nonneg G (X.p.profile i₀)|>.1)) ha)) he
    rw [Time.table G _ (show Time.Same T' s from ⟨rfl,rfl,rfl⟩),Time.table G _ (show Time.Same T' s from ⟨rfl,rfl,rfl⟩)]; simp only [abs_zero,zero_mul,mul_zero,add_zero]; constructor
    · simp only [Camp.soft, rim] at hu hz ⊢; unfold forecastE at hz; linarith only [hy,mul_le_mul_of_nonneg_left hz hQ.1,mul_le_mul_of_nonneg_right hu (Dales.fundedP m B|>.1.le), mul_le_mul_of_nonneg_right hc (Dales.fundedP m B|>.1.le), (Dales.fundedP m B).1]
    simp only [rim] at he hf ⊢; unfold forecastE at he hf; linarith only [he, mul_le_mul_of_nonneg_left (add_le_add hf he) hQ.1, mul_le_mul_of_nonneg_right hc (mul_pos hb (Dales.fundedP m B|>.1)).le,mul_le_mul_of_nonneg_right hp (mul_pos hb (Dales.fundedP m B|>.1)).le, mul_pos hb (Dales.fundedP m B|>.1)]
omit H hθ
lemma snap {X W' : Type} [NormedAddCommGroup X] [NormedAddCommGroup W'] (a v:X)(x y:W')(hx:‖x‖<rim)(hp:‖y‖<rim)(ht:u ≤ Camp.soft)(hz:b ≤ 1)(hw: ‖v‖ ≤ rim/4)(hh:‖a-v‖ ≤ (rim/8)*b + u/4 * ‖x-y‖): ‖a‖ ≤ rim/2:=by
    have he:=norm_add_le (a-v) v; rw [sub_add_cancel] at he
    have hk:=norm_sub_le x y; simp only [Camp.soft, rim] at *; have hV:‖x-y‖≤ 2*(1/131072:ℝ):=by linarith only [hk,hx,hp]
    linarith only [he,hV,hw,hz,hh,mul_le_mul ht hV (norm_nonneg _) (by norm_num : (0:ℝ)≤1/131072/8)]
end YM.Juniper.Voucher
