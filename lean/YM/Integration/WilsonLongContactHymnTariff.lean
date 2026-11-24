import YM.Integration.WilsonLongContactHymnConcert
import YM.Integration.WilsonLongContactProtectedAddress
import YM.Integration.WilsonLongContactPlate

/-! The original pre-block quotient of the all-support price, on each genuine
protected physical sector. Every old root sees the same finite Gaussian model. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactHymnTariff
open Function Filter Set Lattice Wilson RG Pressure Tree Precision Marker Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Lotus
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling Supply Input Testing
open AnalyticBridge VerifiedReset ConnectedActivityE6
open WilsonLongContactSectorProtection WilsonLongContactProtectedRun
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase IterationFour Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] {J : Request V}
    {Δ : Daisy.Charity.RG12.Decal G} {extra : Stage → ℕ → ℝ} {γ : ℝ} {R : Run G}
    {ρ : Premium G J.outputFieldOrder} {paid : WilsonLongContactSectorProtection.Paid J Δ extra γ ρ R.kit}
    {A : NumericSchedule R.family J} {Γ : Census V} {z : LocalFormal.Datum R.family Γ}
local notation "S₀" => R.alloy.B.a.clock.op z.level z.period
local notation "T₀" => ships R.alloy.B z.cutoff z.level z.period
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "p₀" => A.outputNorm z.level
local notation "p₁" => A.inputNorm z.level
local notation "ℓ₁" => R.alloy.B.a.clock.J (z.level+1)
local notation "ℓ₀" => R.alloy.B.a.clock.J z.level
local notation "C₀" => libretto J R.metals.p R.metals.K (ℓ₁) (ℓ₀)
local notation "b₀" => paid.choose (ℓ₁) (ℓ₀)
local notation "u₁" => regulatorRun R.family z.cutoff z.period (z.level+1)

noncomputable def field (e : Field J Δ extra γ R ρ paid A z) (i : ℕ) (F : Forest (S₀).ratio)
    (k : (S₀).Choices) (q κ : Chi) (b : ℝ)
    (f : Config G (R.family.S.side (z.level+1) z.period) → ℝ) :=
  (Brim.mapcase e.cash.choose i F).hymn (T₀) (u₁) q b k f
    (Baffle.magic (b₀).record (p₁) (Y₁).beta κ) 1

theorem original (e : Field J Δ extra γ R ρ paid A z) (i : ℕ)
    (F : Forest (S₀).ratio) (k : (S₀).Choices) (q κ : Chi) (b : ℝ)
    (f : Config G (R.family.S.side (z.level+1) z.period) → ℝ)
    (regular : (p₁).Regular ((Y₁).activities.reg i).support f) {τ : ℝ}
    (o : Site (R.family.S.side (z.level+1) z.period)) (origin : o∈((Y₁).activities.reg i).support)
    (price : (p₁).supBounds o ((Y₁).activities.reg i).support f τ) :
    ∃ w : ℝ, (p₀).supBounds ((S₀).ratio.parent o) (Brim.plate e.cash.choose i).support
      (field e i F k q κ b f) w ∧
      Real.exp (QLocalRequestedHeirQuote.toll J * coverNumber (p₀).B (Brim.plate e.cash.choose i).support)*w ≤
        wage J R.metals.p R.metals.K (ℓ₁) (ℓ₀) * (p₁).mass ((Y₁).activities.reg i).support τ := by
  let X := ((Y₁).activities.reg i).support
  let Y := (Brim.plate e.cash.choose i).support
  let L := (S₀).patch.L
  let fee := Lute.returnFee (C₀) (b₀).record (p₀) (p₁) L X 505
    (R.alloy.B.a.clock.hatBeta z.level) (u₁)
  have room := Brim.billboard e.cash.choose (show 500+5≤505 by decide) i
  have hg := Currency.g_pos R.makes z.cutoff z.period (z.level+1) z.below
  have music : Silences G _ J.outputFieldOrder (u₁) ((b₀).record.ε*(p₁).threshold)
      (Baffle.magic (b₀).record (p₁) (Y₁).beta κ (I:=PhysicalNext.Repeat.Key X (R.alloy.B.a.clock.hatBeta z.level) F)) :=
    guard_silent κ hg (mul_pos (b₀).record.guards (p₁).threshold_pos)
  refine ⟨(((L.val:ℝ)^5)*τ)*fee,?_,?_⟩
  · exact WilsonLongContactHymn.held (Brim.mapcase e.cash.choose i F) e.plays origin regular price room hg.le music 1
  have chosen := reported J Δ extra γ R ρ paid z
  have receipts := QLocalRequestedSectorCalendar.record_at J Δ extra γ R A z _
    chosen.1.window chosen.2
  have quote := QLocalInheritedSourcePrice.quote J (C₀) 505
  have enough : Release.accepts 505 J.inputSupport (QLocalRequestedHeirQuote.toll J) L := by
    rw [← (A.input_norm z.level).reserve]
    exact receipts.2.1
  have ret := quote.prices (S₀) (b₀).record (p₀) (p₁) X Y (u₁) _
    (A.output_norm z.level).distance (A.input_norm z.level).reserve enough room
    (A.output_norm z.level).block (by rw [(A.output_norm z.level).block]; exact e.plays.rehearsed.weft.cover)
    (by rw [e.plays.rehearsed.temp_eq]; exact e.plays.rehearsed.tensions.coarse) hg.le receipts.2.2 τ price.1
  change Real.exp _*(τ*fee) ≤ wage J R.metals.p R.metals.K (ℓ₁) (ℓ₀)*((L.val:ℝ)⁻¹)^5*((p₁).mass X τ) at ret
  have hL : (L.val:ℝ)≠0 := (Nat.cast_pos.mpr L.property).ne'
  calc
    _ = (L.val:ℝ)^5 * (Real.exp (QLocalRequestedHeirQuote.toll J * coverNumber (p₀).B Y)*(τ*fee)) := by ring
    _ ≤ (L.val:ℝ)^5*(wage J R.metals.p R.metals.K (ℓ₁) (ℓ₀)*((L.val:ℝ)⁻¹)^5*((p₁).mass X τ)) :=
      mul_le_mul_of_nonneg_left ret (by positivity)
    _ = _ := by rw [inv_pow]; field_simp [hL]; ring

end YM.Integration.WilsonLongContactHymnTariff
