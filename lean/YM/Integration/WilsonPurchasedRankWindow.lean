import YM.Integration.WilsonPairedRankCutoff
import YM.Integration.WilsonCurvatureRankRate
import YM.Integration.WilsonMarkedSubpower
import YM.Integration.WilsonFlatPacketSource

/-! Cofinal prices for the original positive Wilson rank tails, retaining both physical flat coordinates. -/
set_option autoImplicit false

noncomputable section
namespace YM.Integration.WilsonPairedRankRate
open Filter Finset Lattice Wilson RG Marker OPE.Therm Next.Rank IterationFour
open Pert.Asymptotics PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open LocalComparison LocalComparison.MarkedPackets WilsonThermalPacketSum WilsonThermalReadout
open WilsonPolynomialResponse WilsonPairedRankCutoff
open scoped BigOperators Classical Topology
variable {G : Gauge}

def fieldCost (cap marks : ℕ) : ℝ :=
  (2:ℝ)^cap*(marks:ℝ)+((cap+1:ℕ):ℝ)*(marks:ℝ)*(2:ℝ)^cap

def factor (cap marks : ℕ) : ℝ :=
  ((marks+1:ℕ):ℝ)*(2*(fieldCost cap marks+1))^marks *
    (((cap+1:ℕ):ℝ)*(marks:ℝ)*(1+2^cap*(cap:ℝ)))

theorem polynomial (c cap marks : ℕ) {B X : ℝ} (hB : 0 ≤ B) (hX : 1 ≤ X) (hBX : B ≤ X) :
    amplifier c cap marks B ≤ ((marks+1:ℕ):ℝ)*(2*(fieldCost cap marks+1))^marks*X^marks := by
  let A := uniformReadCost cap marks B+cost c cap marks 2 0 B
  have h0 : 0 ≤ cost c cap marks 2 0 B := sum_nonneg fun _ _ => by positivity
  have a0 : 0 ≤ A := add_nonneg (show 0 ≤ uniformReadCost cap marks B by unfold uniformReadCost;positivity) h0
  have hc : 0 ≤ fieldCost cap marks := by unfold fieldCost;positivity
  have hA : A ≤ fieldCost cap marks*B := by
    apply (add_le_add (le_refl (uniformReadCost cap marks B)) (WilsonCurvatureRankRate.at_two c cap marks hB)).trans_eq
    unfold fieldCost uniformReadCost
    ring
  have hL : 2*(A+1) ≤ 2*(fieldCost cap marks+1)*X := by
    have H := hA.trans (mul_le_mul_of_nonneg_left hBX hc)
    linarith
  apply (slope_bound marks a0).trans
  calc
    _ ≤ ((marks+1:ℕ):ℝ)*(2*(fieldCost cap marks+1)*X)^marks :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hL _) (by positivity)
    _ = _ := by rw [mul_pow];ring

theorem at_level (A : Levels G) (hG : G.Simple) (c cap marks : ℕ) {s : ℝ} (hs : s<c) :
    ∀ᶠ m in atTop, ∀ B X : ℝ, 0 ≤ B → 1 ≤ X → B ≤ X →
    rate c cap marks (cool A m) (vanishP A m) B ≤
      factor cap marks*(A.clock.hatCoupling m)^s*X^(marks+1) := by
  filter_upwards [WilsonCurvatureRankRate.funded A hG c cap marks hs, WilsonCurvatureRankRate.thermal A hG c hs] with m h hthermal
  intro B X hB hX hBX
  have hc : 0 ≤ cool A m := hthermal.1
  have hv : 0 ≤ vanishP A m := (Real.exp_pos _).le
  have hC : 0 ≤ cost c cap marks (cool A m) (vanishP A m) B := sum_nonneg fun _ _ => by positivity
  have hg : 0 ≤ A.clock.hatCoupling m := by unfold Calendar.hatCoupling;positivity
  have hr := Real.rpow_nonneg hg s
  have hK : cost c cap marks (cool A m) (vanishP A m) B ≤
      ((cap+1:ℕ):ℝ)*(marks:ℝ)*(((1+2^cap*(cap:ℝ))*(A.clock.hatCoupling m)^s)*X) :=
    (h B hB).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBX (by positivity)) (by positivity))
  have hX0 := zero_le_one.trans hX
  have hfield : 0 ≤ fieldCost cap marks := by unfold fieldCost;positivity
  unfold rate
  apply (mul_le_mul (polynomial c cap marks hB hX hBX) hK hC (by positivity)).trans_eq
  unfold factor
  rw [pow_succ]
  ring

theorem selected {V : Type} (R : Run G) (hG : G.Simple) (J : Request V)
    (A : NumericSchedule R.family J) (K : NumericPrices A) (c rF rC marks : ℕ) (grade : ℝ) (hgrade : 0 ≤ grade) (hc : grade < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      rate c rF marks (cool R.family.path.levels (m+1)) (vanishP R.family.path.levels (m+1)) (A.admittedCost m) +
      rate c rC marks (cool R.family.path.levels m) (vanishP R.family.path.levels m) (K.geometry m) ≤
        D*(regulatorRun R.family N p (m+1))^grade := by
  let s := ((c:ℝ)+grade)/2
  have hs : s<c := by dsimp [s];linarith
  have hs0 : 0 ≤ s := by unfold s;positivity
  let eps := (s-grade)/((marks:ℝ)+1)
  have heps : 0<eps := by unfold eps;apply div_pos _ (by positivity);dsimp [s];linarith
  have hunit : s-eps*((marks:ℝ)+1)=grade := by unfold eps;field_simp;ring
  let F := factor rF marks+factor rC marks
  have hFF : 0 ≤ factor rF marks := by unfold factor fieldCost;positivity
  have hFC : 0 ≤ factor rC marks := by unfold factor fieldCost;positivity
  have hF : 0 ≤ F := add_nonneg hFF hFC
  obtain ⟨mF,hpaidF⟩ := A.cost_subpower eps heps
  obtain ⟨mC,hpaidC⟩ := K.subpower eps heps
  obtain ⟨mR,hR⟩ := eventually_atTop.mp ((at_level R.family.path.levels hG c rF marks hs).and
    (at_level R.family.path.levels hG c rC marks hs))
  refine ⟨1+F*(4:ℝ)^s,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max mR (max mF mC)),ActualRunAdjacentCoupling.eventually_ratio R hG,
    Currency.g_small hG R.makes (1/2) (by norm_num)] with m hm ratio small
  intro N p hN
  let g := regulatorRun R.family N p (m+1)
  let b := regulatorRun R.family N p m
  have hg : 0<g := Currency.g_pos R.makes _ _ _ hN
  have hb : 0<b := Currency.g_pos R.makes _ _ _ hN.le
  have hbg := (le_div_iff₀ hb).mp (ratio N p hN).1
  have hgb := (div_le_iff₀ hb).mp (ratio N p hN).2
  have hbs : b ≤ 1/2 := (small N p hN.le).le
  have hg1 : g ≤ 1 := by change g ≤ 2*b at hgb;linarith
  let X := g^(-eps)
  have hX : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hg hg1 (neg_nonpos.mpr heps.le)
  have Hf := (hR (m+1) (by omega)).1 _ X (A.admitted_cost_nonnegative m) hX (hpaidF m (by omega) N p hN)
  have Hc := (hR m (by omega)).2 _ X (K.geometry_nonnegative m) hX (hpaidC m (by omega) N p hN)
  have hp (i : ℕ) (hi : R.family.path.levels.clock.hatCoupling i ≤ 4*g) :
      (R.family.path.levels.clock.hatCoupling i)^s*X^(marks+1) ≤ (4:ℝ)^s*g^grade := by
    have hh : 0 ≤ R.family.path.levels.clock.hatCoupling i := by unfold Calendar.hatCoupling;positivity
    apply (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hh hi hs0) (pow_nonneg (zero_le_one.trans hX) _)).trans_eq
    rw [Real.mul_rpow (by norm_num) hg.le, mul_assoc]
    unfold X
    rw [←Real.rpow_natCast,←Real.rpow_mul hg.le,←Real.rpow_add hg, Nat.cast_add_one]
    have e : s+(-eps)*((marks:ℝ)+1)=(grade:ℝ) := by linarith
    rw [e]
  have hfhat : R.family.path.levels.clock.hatCoupling (m+1) ≤ 2*g := (Currency.hat_g R.makes N p (m+1) hN).1
  have hchat : R.family.path.levels.clock.hatCoupling m ≤ 2*b := (Currency.hat_g R.makes N p m hN.le).1
  have hpF := hp (m+1) (by linarith only [hg,hfhat])
  have hpC := hp m (by change (1/2:ℝ)*b ≤ g at hbg;linarith only [hbg,hchat])
  apply (add_le_add Hf Hc).trans
  calc
    _ ≤ factor rF marks*((4:ℝ)^s*g^grade) + factor rC marks*((4:ℝ)^s*g^grade) := by
      simp only [mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hpF hFF) (mul_le_mul_of_nonneg_left hpC hFC)
    _ ≤ _ := by change _ ≤ (1+F*(4:ℝ)^s)*g^grade;unfold F;nlinarith [Real.rpow_nonneg hg.le grade]

theorem nonnegative (c cap marks : ℕ) {t δ B : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hB : 0 ≤ B) :
    0 ≤ rate c cap marks t δ B := by
  have hA : 0 ≤ uniformReadCost cap marks B := by unfold uniformReadCost;positivity
  have hC : 0 ≤ cost c cap marks 2 0 B := sum_nonneg fun j _ => by positivity
  have hT : 0 ≤ cost c cap marks t δ B := sum_nonneg fun j _ => by positivity
  exact mul_nonneg (WilsonThermalMultiplier.slope_nonneg _ (add_nonneg hA hC)) hT

/-- The true fine purchased input and the prescribed output are paid separately.
Consequently a chain may use its two actual endpoint tariffs without summing the
quoted costs of intermediate levels. -/
theorem funded {V : Type} (R : Run G) (hG : G.Simple) (J : Request V)
    (A : NumericSchedule R.family J) (K : NumericPrices A) (c capF capC marks : ℕ) (grade : ℝ)
    (hgrade : 0 ≤ grade) (hc : grade < c) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      (rate c capF marks (cool R.family.path.levels (m+1)) (vanishP R.family.path.levels (m+1)) (A.admittedCost m) ≤
        b*(regulatorRun R.family N p (m+1))^grade) ∧
      (rate c capC marks (cool R.family.path.levels m) (vanishP R.family.path.levels m) (K.geometry m) ≤
        b*(regulatorRun R.family N p (m+1))^grade) := by
  obtain ⟨b,hb,h⟩ := selected R hG J A K c capF capC marks grade hgrade hc
  obtain ⟨k,hk⟩ := eventually_atTop.mp (WilsonCurvatureRankRate.thermal R.family.path.levels hG 2 (s:=0) (by norm_num))
  refine ⟨b,hb,?_⟩
  filter_upwards [h,eventually_ge_atTop k] with m H hm
  intro N p hN
  have hf := nonnegative c capF marks (δ:=vanishP R.family.path.levels (m+1)) (hk (m+1) (hm.trans (Nat.le_succ _))).1 (Real.exp_pos _).le
    (A.admitted_cost_nonnegative m)
  have ho := nonnegative c capC marks (δ:=vanishP R.family.path.levels m) (hk m hm).1 (Real.exp_pos _).le (K.geometry_nonnegative m)
  exact ⟨(le_add_of_nonneg_right ho).trans (H N p hN),(le_add_of_nonneg_left hf).trans (H N p hN)⟩

end YM.Integration.WilsonPairedRankRate
end

noncomputable section
namespace YM.Integration.WilsonCenteredRankTwo
open Filter Set MeasureTheory Lattice Wilson RG Marker OPE.Therm Push.GridApprox
open LocalComparison LocalComparison.MarkedPackets WilsonThermalReadout WilsonPairedRankCutoff
open scoped BigOperators Classical

def phase (z : ℂ) : ℂ := (‖z‖:ℂ)/z

theorem phase_meas : Measurable phase := by unfold phase;fun_prop

theorem phase_le (z : ℂ) : ‖phase z‖ ≤ 1 := by
  by_cases hz : z=0
  · simp [phase,hz]
  · simp only [phase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr hz),le_refl]

theorem phase_mul (z : ℂ) : phase z*z=(‖z‖:ℂ) := by
  by_cases hz : z=0
  · simp [hz]
  · exact div_mul_cancel₀ _ hz

theorem positive {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℂ} (hf : Measurable f) {b : ℝ}
    (h : ∀ ζ : X → ℂ, Measurable ζ → (∀ v,‖ζ v‖ ≤ 1) → ‖∫ v,ζ v*f v ∂μ‖ ≤ b) :
    (∫ v, ‖f v‖ ∂μ) ≤ b := by
  have Z := h (fun v => phase (f v)) (phase_meas.comp hf) (fun v => phase_le _)
  have hn : 0 ≤ ∫ v, ‖f v‖ ∂μ := integral_nonneg (fun v : X => norm_nonneg (f v))
  simpa only [phase_mul,integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hn] using Z

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {D : V → ComparisonDensity.Address.Orbit}
def field {n : Side} (P : MarkedPackets D G n R) (g : ℝ) (x : IndependentTests D)
    (L : Poly R →L[ℂ] ℂ) (U : Config G n) : ℂ := L (Poly.pass (P.read (testInclusion D x) g U))

section Source
variable {n : Side} {P : MarkedPackets D G n R} {p : BudgetPoint} {w : V → ℝ} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n} {g width fee : ℝ} {off cov : ℕ}

theorem centered (H : P.Paid p address region w g width fee off cov) (hG : G.Simple) (x : IndependentTests D)
    (L : Poly R →L[ℂ] ℂ) (cap : ℕ) (hr : P.rankCap ≤ cap) (U : Config G n) :
    L (gap P g x 2 U)=field P g x L U-field P g x L 1 := by
  simp only [gap,WilsonFlatPacketSource.subseries H x hG cap hr,field,map_sub]
end Source

variable {C : Family G} {N m p : ℕ}
variable {Pf : MarkedPackets D G (C.side (m+1) p) R} {Pc : MarkedPackets D G (C.side m p) R}
variable {dF dC : BudgetPoint} {adrF : V → Support (C.side (m+1) p)} {adrC : V → Support (C.side m p)}
variable {regF : Comparison.Density.Testing.Region (fun v => (D v).Mood) (C.side (m+1) p)}
variable {regC : Comparison.Density.Testing.Region (fun v => (D v).Mood) (C.side m p)}
variable {wF wC : V → ℝ} {gF gC widthF widthC feeF feeC : ℝ} {offF covF offC covC : ℕ}
local notation "μf" => scene C.path N p (m+1)
local notation "μc" => scene C.path N p m

def defect (Pf : MarkedPackets D G (C.side (m+1) p) R) (Pc : MarkedPackets D G (C.side m p) R)
    (gF gC : ℝ) (xF xC : IndependentTests D) (L : Poly R →L[ℂ] ℂ) (W : Config G (C.side m p)) : ℂ :=
  actualAverage C (N:=N) (field Pf gF xF L) W-field Pc gC xC L W-
    (field Pf gF xF L 1-field Pc gC xC L 1)

theorem joint (hC : C.Makes) (hG : G.Simple) (hm : m<N)
    (F : Pf.Paid dF adrF regF wF gF widthF feeF offF covF)
    (K : Pc.Paid dC adrC regC wC gC widthC feeC offC covC)
    (xF xC : IndependentTests D) (capF capC : ℕ) (hf : Pf.rankCap ≤ capF) (hc : Pc.rankCap ≤ capC)
    (tf δf tc δc : ℝ) (htf : 0 ≤ tf) (hdf : 0 ≤ δf) (htc : 0 ≤ tc) (hdc : 0 ≤ δc)
    (fr : ∀ z, (μf).real (trigger z tf) ≤ δf) (cr : ∀ z, (μc).real (trigger z tc) ≤ δc)
    (L : Poly R →L[ℂ] ℂ) (Lf : ∀ a,‖L a‖ ≤ Poly.price wF a) (Lc : ∀ a,‖L a‖ ≤ Poly.price wC a) :
    Integrable (defect (N:=N) Pf Pc gF gC xF xC L) μc ∧
      (∫ W, ‖defect (N:=N) Pf Pc gF gC xF xC L W‖ ∂μc) ≤
        rate 2 capF (Fintype.card V) tf δf feeF + rate 2 capC (Fintype.card V) tc δc feeC := by
  letI : IsProbabilityMeasure μc := probability (H:=C.path) (p:=p) hC.wilson hm.le
  let f := field Pf gF xF L
  let u := field Pc gC xC L
  have Ef : Envelope (fun U => f U-f 1) := by
    simpa only [f,centered F hG xF L capF hf] using WilsonPairedRankCutoff.envelope F xF 2 capF hf L Lf
  have Eu : Envelope (fun W => u W-u 1) := by
    simpa only [u,centered K hG xC L capC hc] using WilsonPairedRankCutoff.envelope K xC 2 capC hc L Lc
  have Efull : Envelope f := by
    simpa only [sub_add_cancel] using Ef.addC (Envelope.constC (f 1))
  have H (W : Config G (C.side m p)) : defect (N:=N) Pf Pc gF gC xF xC L W =
      actualAverage C (N:=N) (fun U => f U-f 1) W-(u W-u 1) := by
    have Econst : Envelope (fun _ : Config G (C.side (m+1) p) => f 1) := Envelope.constC _
    have av : actualAverage C (N:=N) (fun U => f U-f 1) W =
        actualAverage C (N:=N) f W - actualAverage C (N:=N) (fun _ => f 1) W := by
      obtain ⟨a,ha⟩ := Efull.cost
      obtain ⟨b,hb⟩ := Econst.cost
      unfold actualAverage
      simp_rw [smul_sub]
      exact integral_sub (actualAverage_integrable C hC hm Efull.meas.aestronglyMeasurable ha W)
        (actualAverage_integrable C hC hm Econst.meas.aestronglyMeasurable hb W)
    rw [av,actualAverage_const C hC hm]
    unfold defect
    change _ = _ - _ - (_-_)
    dsimp only [f,u]
    abel
  have Henv := (WilsonForwardMeasurable.average hC hm Ef).subC Eu
  have Ed : Envelope (defect (N:=N) Pf Pc gF gC xF xC L) := by
    rw [show defect (N:=N) Pf Pc gF gC xF xC L = _ from funext H]
    exact Henv
  refine ⟨Ed.integrableC _,positive _ Ed.meas ?_⟩
  intro ζ hmζ hζ
  simp only [H]
  simpa only [f,u,centered F hG xF L capF hf,centered K hG xC L capC hc] using
    WilsonPairedRankCutoff.joint hC hm F K xF xC 2 capF capC hf hc tf δf tc δc htf hdf htc hdc fr cr ζ hmζ hζ L Lf Lc

end YM.Integration.WilsonCenteredRankTwo
end

noncomputable section
namespace YM.Integration.WilsonCenteredSelectedRate
open Filter MeasureTheory Lattice Wilson RG Source Labels Marker OPE.Therm
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global Comparison.RG02
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Pert.Asymptotics WilsonCenteredRankTwo WilsonThermalReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
variable (R : Run G) (hG : G.Simple) (θ : Poetry R.family.path.levels) (J : Request V)
    (A : NumericSchedule R.family J) (K : NumericPrices A) (caps : Handoff.OutputCapacities)

private theorem smaller {d : LocalFormal.Datum R.family Γ} (F : AnalyticInput J A d)
    (a : Poly Γ) :
    Poly.price (fun v => F.outputRadii v/F.kernelCosts v) a ≤
      Poly.price (fun v => F.inputRadii v/F.kernelCosts v) a := by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Finset.prod_le_prod
  · exact fun v _ => div_nonneg (F.output_radius_positive v).le (F.kernel_positive v).le
  · intro v _
    exact div_le_div_of_nonneg_right
      ((le_mul_of_one_le_right (F.output_radius_positive v).le (A.radius_loss_ge_one _)).trans (F.radius_admission v))
      (F.kernel_positive v).le

include hG θ in
/-- Above every natural cut strictly larger than the requested grade the entire
nonlinear difference is negligible in normalized Wilson L¹, with all original
field choices, selected models and independent tests still quantified. -/
theorem high (c : ℕ) {grade : ℝ} (hg : 0 ≤ grade) (hlt : grade < c) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ m : ℕ in atTop, ∀ d : LocalFormal.Datum R.family Γ, d.level=m →
    ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (M : AnalyticOutput caps Y K F),
    ∀ (x y : IndependentTests J.tests) (L : Poly Γ →L[ℂ] ℂ),
    (∀ a, ‖L a‖ ≤ Poly.price (fun v => F.outputRadii v/F.kernelCosts v) a) →
    let g := regulatorRun R.family d.cutoff d.period (d.level+1)
    let μ := scene R.family.path d.cutoff d.period d.level
    let f := fun W => actualAverage R.family (N:=d.cutoff) (fun U => L (gap F.packets g x c U)) W-
      L (gap M.model g y c W)
    Integrable f μ ∧ (∫ W, ‖f W‖ ∂μ) ≤ b*g^grade := by
  obtain ⟨b,hb,rate⟩ := WilsonPairedRankRate.selected R hG J A K c J.inputPacketRankCap caps.packetRank
    (Fintype.card V) grade hg hlt
  obtain ⟨k,hr⟩ := eventually_atTop.mp ((rare θ hG R.makes.wilson).and
    (WilsonCurvatureRankRate.thermal R.family.path.levels hG 2 (s:=0) (by norm_num)))
  refine ⟨b,hb,?_⟩
  filter_upwards [rate,eventually_ge_atTop k] with m hrate hm
  rintro d rfl Y F M x y L hL
  let g := regulatorRun R.family d.cutoff d.period (d.level+1)
  let μ := scene R.family.path d.cutoff d.period d.level
  let f := fun U => L (gap F.packets g x c U)
  let u := fun W => L (gap M.model g y c W)
  let h := fun W => actualAverage R.family (N:=d.cutoff) f W-u W
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=d.period) R.makes.wilson d.below.le
  have F₀ := hr (d.level+1) (hm.trans (Nat.le_succ _))
  have C₀ := hr d.level hm
  have Lf := fun a => (hL a).trans (smaller R J A F a)
  have Ef := WilsonPairedRankCutoff.envelope F.input_paid x c J.inputPacketRankCap F.rank_bounded L Lf
  have Eu := WilsonPairedRankCutoff.envelope M.paid y c caps.packetRank M.rank_bounded L hL
  have Eh : Envelope h := (WilsonForwardMeasurable.average R.makes d.below Ef).subC Eu
  refine ⟨Eh.integrableC _,positive μ Eh.meas ?_⟩
  intro ζ hmζ hζ
  exact (WilsonPairedRankCutoff.joint R.makes d.below F.input_paid M.paid x y c J.inputPacketRankCap caps.packetRank
    F.rank_bounded M.rank_bounded (cool R.family.path.levels (d.level+1)) (vanishP R.family.path.levels (d.level+1))
    (cool R.family.path.levels d.level) (vanishP R.family.path.levels d.level)
    F₀.2.1 (Real.exp_pos _).le C₀.2.1 (Real.exp_pos _).le
    (F₀.1 d.cutoff (Nat.succ_le_of_lt d.below) d.period) (C₀.1 d.cutoff d.below.le d.period)
    ζ hmζ hζ L Lf hL).trans (hrate d.cutoff d.period d.below)

include hG θ in
/-- Every true rank at least two is paid before the cutoff, period, coordinates,
independent physical readers, and selected analytic output. The field-independent
part on either side is kept as its actual flat evaluation. -/
theorem selected {grade : ℝ} (hg : 0 ≤ grade) (hlt : grade < 2) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ m : ℕ in atTop, ∀ d : LocalFormal.Datum R.family Γ, d.level=m →
    ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (M : AnalyticOutput caps Y K F),
    ∀ (x y : IndependentTests J.tests) (L : Poly Γ →L[ℂ] ℂ),
    (∀ a, ‖L a‖ ≤ Poly.price (fun v => F.outputRadii v/F.kernelCosts v) a) →
    let g := regulatorRun R.family d.cutoff d.period (d.level+1)
    let μ := scene R.family.path d.cutoff d.period d.level
    let f := defect (N:=d.cutoff) F.packets M.model g g x y L
    Integrable f μ ∧ (∫ U, ‖f U‖ ∂μ) ≤ b*g^grade := by
  obtain ⟨b,hb,rate⟩ := WilsonPairedRankRate.selected R hG J A K 2 J.inputPacketRankCap caps.packetRank
    (Fintype.card V) grade hg hlt
  obtain ⟨k,hr⟩ := eventually_atTop.mp ((rare θ hG R.makes.wilson).and
    (WilsonCurvatureRankRate.thermal R.family.path.levels hG 2 (s:=0) (by norm_num)))
  refine ⟨b,hb,?_⟩
  filter_upwards [rate,eventually_ge_atTop k] with m hrate hm
  rintro d rfl Y F M x y L hL
  have F₀ := hr (d.level+1) (hm.trans (Nat.le_succ _))
  have C₀ := hr d.level hm
  have E := WilsonCenteredRankTwo.joint R.makes hG d.below F.input_paid M.paid x y
    J.inputPacketRankCap caps.packetRank F.rank_bounded M.rank_bounded
    (cool R.family.path.levels (d.level+1)) (vanishP R.family.path.levels (d.level+1))
    (cool R.family.path.levels d.level) (vanishP R.family.path.levels d.level)
    F₀.2.1 (Real.exp_pos _).le C₀.2.1 (Real.exp_pos _).le
    (F₀.1 d.cutoff (Nat.succ_le_of_lt d.below) d.period) (C₀.1 d.cutoff d.below.le d.period)
    L (fun a => (hL a).trans (smaller R J A F a)) hL
  exact ⟨E.1,E.2.trans (hrate d.cutoff d.period d.below)⟩

end YM.Integration.WilsonCenteredSelectedRate
end
