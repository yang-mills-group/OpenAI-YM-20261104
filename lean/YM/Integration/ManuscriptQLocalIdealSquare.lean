import YM.Integration.ManuscriptQLocalMeasuredAffineRows
import YM.Next.FOUNDATIONS.LinkBounds
import YM.Integration.ManuscriptQLocalAffineScalar
import YM.Integration.PhysicalAffineScalarStationary
import YM.Integration.ConditionalAffineMeanPurchase
import YM.Integration.PhysicalAffineScalarIdealSquare

/-! The absolute original full affine scalar at a financed measured stage. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalIdealSquare
open Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarRootContraction PhysicalAffineScalarChangedFields PhysicalAffineScalarIdealSquare
open Marker WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection FullQLocal.RenderedStep
open ConditionalAffineLoadPrices ConditionalAffineMeanPurchase
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

structure Rates where
  spatial : ℝ
  source : ℝ
  spatial_pos : 0<spatial
  source_pos : 0<source

/-- Uniform rooted fee in the fine rescaled measured chart. Neither
the inverse fine coupling nor the torus size enters this stage quantity. -/
def tariff (G : Gauge) (L : Side) (n : ℕ) (r : Rates) :=
  physicalVolume G L r.spatial*((2:ℝ)^(max 1 n)*(r.source*r.source))

def densityWidth (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (r : Rates) :=
  min r.spatial (width G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width)

def densityFee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (r : Rates) :=
  |(Fintype.card (Bloch.Co P.L (PAC G 1)):ℝ)*(earnings G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width/2)|+
    2*tariff G P.L n r

/-- Covers the ordinary full independent tensor and the sum over a single
actual changed site, simultaneously for every grade through n. -/
def expense (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (r : Rates) :=
  let s := densityWidth G P Pt n r/2
  (max 1 (torusPay PUnit.{1} s)*(max 1 (torusPay (PAC G 1) s))^n)*densityFee G P Pt n r

def Offer {G : Gauge} (P : Patch) (Pt : Teller G) (n : ℕ) (x : ℝ) (r : Rates) :=
  (1≤Real.log (Real.log x) ∧ expense G P Pt n r≤1+Real.log (Real.log x)) ∧
  4≤Pressure.betaF G x P.L ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    100*(1+radiusB x)≤c.val → Voucher S T (max 1 n) r.spatial r.source

def Paid {G : Gauge} (n : ℕ→ℕ→ℕ) : Prediction G := Selected (G:=G) Offer n

theorem prices {G : Gauge} (n : ℕ→ℕ→ℕ) : FundedPredictionSupply.AllPrices (@Paid G n) := by
  intro s K
  refine ConditionalAffineMeanPurchase.select (⟨1,1,zero_lt_one,zero_lt_one⟩ : Rates) Offer n ?_ s (ThroughLaunch.raging s K)
  intro P Pt hp d
  obtain ⟨δ,C,R,hδ,hC,H⟩ := purchased G P Pt hp (max 1 d)
  let r : Rates := ⟨δ,C,hδ,hC⟩
  refine ⟨r,?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (expense G P Pt d r)),
    (Work.E09.betaF_growth G P.L).eventually_ge_atTop 4,Work.E01.radiusB_tendsto.eventually_ge_atTop R] with x hL hβ hR
  refine ⟨⟨(le_max_left ..).trans hL,((le_max_right ..).trans hL).trans (le_add_of_nonneg_left zero_le_one)⟩,hβ,?_⟩
  intro c f S T hS hT hsize
  exact H S T hS hT (le_trans (by gcongr) hsize)

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "x" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "rp" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level

theorem realized {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) :
    Voucher S T (max 1 (n j₁ j₀)) (paid.choose j₁ j₀).spatial (paid.choose j₁ j₀).source := by
  obtain ⟨H,hF,hsize⟩ := selected_receipt R paid d.cutoff d.level d.period d.below
  exact H.2.2 S T rfl hF hsize

theorem numeric {n : ℕ→ℕ→ℕ} (paid : Paid n R.kit) {V : Type} {Q : Request V} (sale : NumericSchedule R.family Q) :
    let Pt := query R.metals.p R.metals.K j₁ j₀
    expense G (S).patch Pt (n j₁ j₀) (paid.choose j₁ j₀) ≤ sale.admittedCost d.level := by
  intro Pt
  have H := (selected_receipt R paid d.cutoff d.level d.period d.below).1.1
  exact ConditionalAffineMeanPurchase.admitted R d.level H.1 H.2 sale

theorem physical_germ (k : (S).Choices) (F : Forest (S).ratio) :
    PhysicalAffineScalarUncut.sourceResidual T x k F=ᶠ[𝓝 0] residual T k F := by
  filter_upwards [ManuscriptQLocalRootWeights.positive R d k F] with B h
  have hp := PhysicalAffineScalarSpectralRoot.positive T x k F B h.2
  exact (PhysicalAffineScalarSpectralRoot.source T x k F B hp).trans (physical T k F B hp).symm

/-- In the unscaled field the exact physical prefactor is still present. -/
theorem prescribed (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (g : ℝ) :
    (fun B : E => PhysicalAffineScalarSpectralRoot.stationaryScalar T k F g o B-
      PhysicalAffineScalarSpectralRoot.halfLog T k F o B) =ᶠ[𝓝 0] fun B => -(2*g^2)⁻¹*mass T k F o B := by
  filter_upwards [ManuscriptQLocalRootWeights.positive R d k F] with B h
  have hp := PhysicalAffineScalarSpectralRoot.positive T x k F B h.2
  simp only [PhysicalAffineScalarSpectralRoot.stationaryScalar,add_sub_cancel_left,mass,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  rw [physical T k F B hp]
  split <;> ring

/-- Each native signed slot has its own zero derivative in every genuine
coarse direction, obtained from the original stationary equation. -/
theorem slope (k : (S).Choices) (F : Forest (S).ratio) (a : Rows.Receipt G S) (v : E) :
    Tendsto (fun t : ℝ => t⁻¹*residual T k F (t • v) a) (𝓝[≠] 0) (𝓝 0) := by
  let d' : LocalFormal.Datum R.family Γ := {d with forest:=F}
  have h := ManuscriptQLocalStationaryScalar.residual R d' k v
  have h₁ : Tendsto (fun t : ℝ => t⁻¹*PhysicalAffineScalarUncut.sourceResidual T x k F (t • v) a) (𝓝[≠] 0) (𝓝 0) :=
    (continuous_apply a).continuousAt.tendsto.comp h
  have ray : Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 0) := by
    have h' := ((continuous_id.smul continuous_const : Continuous (fun t : ℝ => t • v)).continuousAt («x» := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    change Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • v)) at h'
    simpa only [zero_smul] using h'
  apply h₁.congr'; filter_upwards [ray.eventually (physical_germ R d k F)] with t ht
  exact congrArg (fun w => t⁻¹*w a) ht

theorem smooth {n : ℕ} {δ C : ℝ} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (H : ConditionalAffineLoadPrices.Paid rp δ C n (residual T k F)) : ContDiffAt ℝ n (mass T k F o) 0 := by
  unfold mass
  apply ContDiffAt.sum; intro a _
  by_cases hh : rp a=o
  · simp only [hh,if_true]
    have h := (TestD.evaluate a ()).contDiff.contDiffAt.comp 0 H.smooth
    exact h.mul h
  · simp only [hh,if_false]; exact contDiffAt_const

/-- All independent signed coarse legs, including the empty, bilinear
mixed, and fully polarized cubic grades, cancel before the row sum. -/
theorem short {V : Type*} {n : ℕ} {δ C : ℝ} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (H : ConditionalAffineLoadPrices.Paid rp δ C (max 1 n) (residual T k F)) (v : V→E) (l : List V)
    (hn : l.length≤n) (hl : l.length≤3) : jet v (mass T k F o) l 0=0 := by
  let N := max 1 n
  have hN : l.length≤N := hn.trans (le_max_right ..)
  have hP := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  have hp : (S).patch.Branches (S).kernel G := hP.knobs.symm ▸ hP.kernel
  let row := fun (a : Rows.Receipt G S) (B : E) => residual T k F B a
  let held := fun a B => if rp a=o then row a B*row a B else 0
  have hR (a : Rows.Receipt G S) : ContDiffAt ℝ N (row a) 0 := (TestD.evaluate a ()).contDiff.contDiffAt.comp 0 H.smooth
  have hH (a : Rows.Receipt G S) : ContDiffAt ℝ l.length (held a) 0 := by
    by_cases he : rp a=o
    · simp only [held,he,if_true]; exact (smooth_of_le (hR a) hN).mul (smooth_of_le (hR a) hN)
    · simp only [held,he,if_false]; exact contDiffAt_const
  change jet v (fun B => ∑ a : Rows.Receipt G S, held a B) l 0=0
  rw [jet_sum v l Finset.univ held (fun a _ => hH a)]
  apply Finset.sum_eq_zero; intro a _
  by_cases ha : rp a=o
  · simp only [held,ha,if_true]
    have h₀ : row a 0=0 := congrFun (PhysicalAffineScalarIdealSquare.zero T k hp F) a
    have h₁ : ContDiffAt ℝ 1 (row a) 0 := (hR a).of_le (by exact_mod_cast (le_max_left 1 n))
    exact PhysicalAffineScalarIdealGrading.square_short v (hR a) h₁ h₀
      (PhysicalAffineScalarIdealGrading.derivative_zero (h₁.differentiableAt (by norm_num)) h₀ (slope R d k F a)) l hN hl
  · simp only [held,ha,if_false]
    cases l with
    | nil => exact zeroth v (fun _ : E => (0:ℝ)) 0
    | cons i l => exact jet_const v (i :: l) (List.cons_ne_nil _ _) (0:ℝ) (0:E)

local notation "β" => (R.family.path.rep d.cutoff d.period (d.level+1)).beta
local notation "g₀" => Next.SectorChange.coupling β

theorem fine {n : ℕ→ℕ→ℕ} (p : Paid n R.kit) : 0<g₀ ∧ g₀≤1 := by
  have h := (selected_receipt R p d.cutoff d.level d.period d.below).1.2.1
  let t := R.family.path.levels.clock.hatBeta (d.level+1)
  have hL : (S).patch.L=R.rolls.L j₁ := Push.PriceCompiler.block_eq R.alloy.B.valid d.level
  have he : t=Pressure.betaF G x (S).patch.L := by rw [hL]; exact Push.PriceCompiler.beta_eq R.alloy.B.valid d.level
  have ht : 4≤t := he.symm ▸ h
  have hs : 2≤Real.sqrt t := by
    nlinarith [Real.sqrt_nonneg t,Real.sq_sqrt (by linarith : 0≤t)]
  have hband := (MatchingLedger.Compass.Income.Weather.into_band R.family R.makes (m:=d.level+1) (N:=d.cutoff) d.below d.period).2
  change g₀≤2*(Real.sqrt t)⁻¹ at hband
  refine ⟨Next.SectorChange.coupling_pos (ManuscriptQLocalScalarClockPurchase.band R d.cutoff d.level d.period d.below).1,?_⟩
  exact hband.trans (by rw [←div_eq_mul_inv,div_le_iff₀ (by linarith : 0<Real.sqrt t),one_mul]; exact hs)

/-- Original full rooted affine scalar with its own independently supplied
paired half-log removed, in the actual fine Gaussian field chart. -/
def graded (k : (S).Choices) (F : Forest (S).ratio) (g : ℝ) (o : Site c₀) (B : E) :=
  PhysicalAffineScalarSpectralRoot.stationaryScalar T k F g o (g • B)-
    PhysicalAffineScalarSpectralRoot.halfLog T k F o (g • B)

theorem graded_germ (k : (S).Choices) (F : Forest (S).ratio) (g : ℝ) (o : Site c₀) :
    graded R d k F g o=ᶠ[𝓝 0] PhysicalAffineScalarIdealGrading.scaled g (mass T k F o) := by
  have ht : Tendsto (fun B : E => g • B) (𝓝 0) (𝓝 0) := by
    let A : E →L[ℝ] E := g • ContinuousLinearMap.id ℝ E
    change Tendsto A (𝓝 0) (𝓝 0)
    simpa only [map_zero] using A.continuous.tendsto (0 : E)
  exact ht.eventually (prescribed R d k F o g)

theorem graded_smooth {n : ℕ} {δ C : ℝ} (k : (S).Choices) (F : Forest (S).ratio) (g : ℝ) (o : Site c₀)
    (H : ConditionalAffineLoadPrices.Paid rp δ C n (residual T k F)) : ContDiffAt ℝ n (graded R d k F g o) 0 := by
  have h : ContDiffAt ℝ n (mass T k F o) (g • (0:E)) := by rw [smul_zero]; exact smooth R d k F o H
  have hA : ContDiffAt ℝ n (fun B : E => g • B) 0 :=
    (g • ContinuousLinearMap.id ℝ E).contDiff.contDiffAt
  exact (contDiffAt_const.mul (h.comp 0 hA)).congr_of_eventuallyEq (graded_germ R d k F g o)

theorem grades {V : Type*} {n : ℕ} {δ C : ℝ} (k : (S).Choices) (F : Forest (S).ratio) (g : ℝ) (o : Site c₀)
    (H : ConditionalAffineLoadPrices.Paid rp δ C n (residual T k F)) (v : V→E) (l : List V) (hn : l.length≤n) :
    jet v (graded R d k F g o) l 0=(-(2*g^2)⁻¹*g^l.length)*jet v (mass T k F o) l 0 := by
  have e : jet v (graded R d k F g o) l 0=jet v (PhysicalAffineScalarIdealGrading.scaled g (mass T k F o)) l 0 := by
    change iteratedFDeriv ℝ l.length _ 0 _=iteratedFDeriv ℝ l.length _ 0 _
    rw [((graded_germ R d k F g o).iteratedFDeriv (𝕜:=ℝ) l.length).self_of_nhds]
  exact e.trans (PhysicalAffineScalarIdealGrading.scaled_jet g v _ l (smooth_of_le (smooth R d k F o H) hn))

theorem changed_grades {V : Type*} {n : ℕ} {δ C : ℝ} (k : (S).Choices) (F U : Forest (S).ratio)
    (z : Site c₀) (g : ℝ) (o : Site c₀) (H : Pair rp z δ C n (residual T k F) (residual T k U))
    (v : V→E) (l : List V) (hn : l.length≤n) :
    jet v (fun b => graded R d k U g o b-graded R d k F g o b) l 0 =
      (-(2*g^2)⁻¹*g^l.length)*jet v (fun b => mass T k U o b-mass T k F o b) l 0 := by
  rw [jet_sub v l (smooth_of_le (graded_smooth R d k U g o H.right) hn) (smooth_of_le (graded_smooth R d k F g o H.left) hn),
    jet_sub v l (smooth_of_le (smooth R d k U o H.right) hn) (smooth_of_le (smooth R d k F o H.left) hn),
    grades R d k U g o H.right v l hn,grades R d k F g o H.left v l hn,mul_sub]


theorem low {V : Type*} {n : ℕ→ℕ→ℕ} (p : Paid n R.kit) (k : (S).Choices) (F U : Forest (S).ratio)
    (z o : Site c₀) (hu : changed S F U z) (v : V→E) (l : List V) (hl : l.length≤n j₁ j₀) (h₃ : l.length≤3) :
    jet v (graded R d k F g₀ o) l 0=0 ∧
      jet v (fun B => graded R d k U g₀ o B-graded R d k F g₀ o B) l 0=0 := by
  have H := realized R d p k F U z hu
  have hn : l.length ≤ max 1 (n j₁ j₀) := hl.trans (le_max_right ..)
  have hF := short R d k F o H.left v l hl h₃
  have hU := short R d k U o H.right v l hl h₃
  refine ⟨(grades R d k F g₀ o H.left v l hn).trans (by rw [hF,mul_zero]),?_⟩
  rw [changed_grades R d k F U z g₀ o H v l hn,
    jet_sub v l (smooth_of_le (smooth R d k U o H.right) hn) (smooth_of_le (smooth R d k F o H.left) hn),hF,hU,sub_zero,mul_zero]

theorem rooted {n : ℕ→ℕ→ℕ} (p : Paid n R.kit) (k : (S).Choices) (F U : Forest (S).ratio)
    (z o : Site c₀) (hu : changed S F U z) (l : List (raw G c₀)) (hl : l.length≤n j₁ j₀) :
    let r := p.choose j₁ j₀
    let C := tariff G (S).patch.L (n j₁ j₀) r
    (marks G c₀ r.spatial).pay l o*|jet (ray G c₀) (graded R d k F g₀ o) l 0|≤C ∧
    (marks G c₀ r.spatial).pay l o*((native c₀).weight r.spatial o z*|jet (ray G c₀)
      (fun B => graded R d k U g₀ o B-graded R d k F g₀ o B) l 0|)≤2*C := by
  intro r C
  have H := realized R d p k F U z hu
  have hn : l.length ≤ max 1 (n j₁ j₀) := hl.trans (le_max_right ..)
  have hv : 0≤physicalVolume G (S).patch.L r.spatial := (Finset.sum_nonneg fun _ _ => (native c₀).weight_nn ..).trans
    ((row_volume (S) r.spatial r.spatial_pos).bound o)
  have hC : 0≤C := mul_nonneg hv (mul_nonneg (by positivity) (mul_self_nonneg _))
  by_cases small : l.length≤3
  · obtain ⟨hF,hΔ⟩ := low R d p k F U z o hu (ray G c₀) l hl small
    rw [hF,hΔ,abs_zero,mul_zero,mul_zero,mul_zero]
    exact ⟨hC,by positivity⟩
  obtain ⟨hg,hg₁⟩ := fine R d p
  let a := -(2*g₀^2)⁻¹*g₀^l.length
  have hcoef : |a|≤1 := by
    rw [show |a|=g₀^(l.length-2)/2 from PhysicalAffineScalarIdealGrading.coefficient hg (by omega)]
    have hp : g₀^(l.length-2)≤1 := pow_le_one₀ hg.le hg₁
    linarith
  have pos := PhysicalAffineScalarIdealSquare.positions T k r.spatial_pos r.source_pos.le F U z H o l hn
  have W : 0≤(marks G c₀ r.spatial).pay l o := ((marks G c₀ r.spatial).pay_pos ..).le
  have Z : 0≤(native c₀).weight r.spatial o z := (native c₀).weight_nn ..
  rw [grades R d k F g₀ o H.left (ray G c₀) l hn,changed_grades R d k F U z g₀ o H (ray G c₀) l hn]
  change _ * |a * _| ≤ C ∧ _ * (_ * |a * _|) ≤ 2*C
  constructor
  · calc _ = |a| * ((marks G c₀ r.spatial).pay l o*|jet (ray G c₀) (mass T k F o) l 0|) := by rw [abs_mul]; ring
         _ ≤ 1*C := mul_le_mul hcoef pos.1 (mul_nonneg W (abs_nonneg _)) zero_le_one
         _ = C := one_mul _
  · calc _ = |a| * ((marks G c₀ r.spatial).pay l o*((native c₀).weight r.spatial o z*
            |jet (ray G c₀) (fun B => mass T k U o B-mass T k F o B) l 0|)) := by rw [abs_mul]; ring
         _ ≤ 1*(_*(_+_)) := mul_le_mul hcoef pos.2 (mul_nonneg W (mul_nonneg Z (abs_nonneg _))) zero_le_one
         _ = 2*C := by dsimp only [C,tariff]; ring

/-- The independently specified absolute physical scalar square on one
root, in complete mixed-direction operator and one-tree summed norms. -/
theorem original {n : ℕ→ℕ→ℕ} (p : Paid n R.kit) (k : (S).Choices) (F : Forest (S).ratio)
    (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S F U z}) (o : Site c₀) (j : ℕ) (hj : j≤n j₁ j₀) :
    let r := p.choose j₁ j₀
    let s := r.spatial/2
    let C := tariff G (S).patch.L (n j₁ j₀) r
    let V := torusPay (PAC G 1) s
    PhysicalAffineScalarFieldContraction.Root j s o (fun _ : PUnit.{1} => o) (fun _ => graded R d k F g₀ o) (V^j*C) ∧
    PhysicalAffineScalarFieldContraction.Root j s o id
      (fun z B => graded R d k (U z).val g₀ o B-graded R d k F g₀ o B) ((torusPay PUnit.{1} s*V^j)*(2*C)) := by
  intro r s C V
  have hv : 0≤physicalVolume G (S).patch.L r.spatial := (Finset.sum_nonneg fun _ _ => (native c₀).weight_nn ..).trans
    ((row_volume (S) r.spatial r.spatial_pos).bound o)
  have hC : 0≤C := mul_nonneg hv (mul_nonneg (by positivity) (mul_self_nonneg _))
  constructor
  · apply PhysicalAffineScalarFieldContraction.regular G c₀ r.spatial C r.spatial_pos hC o
    intro a
    exact (rooted R d p k F (U o).val o o (U o).prop (List.ofFn a) (by simpa only [List.length_ofFn] using hj)).1
  · apply PhysicalAffineScalarFieldContraction.tagged G c₀ r.spatial (2*C) r.spatial_pos (by positivity) o
    intro z a
    exact (rooted R d p k F (U z).val z o (U z).prop (List.ofFn a) (by simpa only [List.length_ofFn] using hj)).2

end YM.Integration.ManuscriptQLocalIdealSquare
end
