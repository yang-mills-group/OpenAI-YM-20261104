import YM.Integration.WilsonMeasuredOwnerFlatReading
import YM.Integration.WilsonMeasuredOwnerIntegrable
import YM.Integration.WilsonMeasuredSignedScalar
import YM.Integration.WilsonThermometerUnitFilingRaw

/-! A full signed scalar invoice includes its actual compulsory array on the original post. The order-zero hard gate at the fixed older date suffices for an already small native invoice. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWhole
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {N per m k b:ℕ} (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b≤N) {u:ℕ} (floor:m≤u) (ub:u≤b)
   (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
open Source RG16 WilsonThermometerUnitFilingCoarse
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "V" => Ψ b
local notation "W" => R.family.path.rep N per b
local notation "X" => Config G (R.family.side b per)

def RangeCost (f:X→ℂ) (C:ℝ) : Prop :=
  (∀ (j:ℕ) (_ : u ≤ j) (jb:j ≤ b),‖reading R (N:=N) f j jb‖≤C) ∧
  ∀ (i j:ℕ) (_ : u ≤ i) (_ : u ≤ j) (ib:i ≤ b) (jb:j ≤ b),
    ‖reading R (N:=N) f i ib-reading R (N:=N) f j jb‖≤2*C

include simple way D Q ticket π Γ Ψ course top floor ub gate in
theorem original (y:Site (R.family.side b per)) (h:Coefficient F₀ (R.family.side b per))
    (law:h.Format y R.family.params V) {M:ℝ} (income:h.remBound y V (LocalComparison.forcedDivisor R.family b) M)
    (nonneg:0≤M) : RangeCost R (N:=N) (u:=u) (h.density y S₀ V) (‖h.x 0‖+5*M):=by
  let source:=h.density y S₀ V
  let forced:=WilsonMeasuredCoefficientTransport.account h V
  have quiet:(V).eval=(W).eval:=(QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans ub) top).view
  obtain ⟨hF,hS⟩:=WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course (floor.trans ub) top S₀ R.family.params y h law income
  have received:∀U,h.density y S₀ V U=source U-((V).eval U:ℂ)*(0:ℂ):=by simp [source]
  obtain ⟨paid,_⟩:=WilsonMeasuredSignedScalar.original R simple π Γ Ψ course (floor.trans ub) top
    y h law income source (fun _=>0) received
  have regular:= (WilsonThermometerUnitFilingPosterior.original R top V quiet source
    (fun _=>0) forced (‖h.x 0‖+M) paid).1
  have base: ∀j,u ≤ j→∀jb:j ≤ b,‖reading R (N:=N) source j jb‖≤‖h.x 0‖+5*M := by
    intro j uj jb
    have softCost:‖reading R (N:=N) (source-forced) j jb‖≤‖h.x 0‖+M:=by
      simpa only [mul_zero,sub_zero,Pi.sub_def] using regular j jb
    have hardCost:‖reading R (N:=N) forced j jb‖≤4*M:=by
      rw [WilsonThermometerUnitFilingRaw.ratio R top V quiet forced jb]
      apply le_of_forall_pos_le_add
      intro δ hd
      have f:=WilsonMeasuredOwnerFlatReading.original R simple way D Q ticket π Γ Ψ course top floor ub 0
        (zero_lt_one:0<(1:ℝ)) le_rfl gate S₀ R.family.params y h law income
        (show 0<M+δ/4 by linarith) (show M≤M+δ/4 by linarith) uj jb
      simp only [div_one,mul_one,pow_zero] at f
      linarith only [f]
    have combine:=WilsonThermometerUnitFilingRaw.add R (N:=N) (source-forced) forced (hS.sub hF) hF jb
    rw [sub_add_cancel] at combine
    rw [combine]
    exact (norm_add_le ..).trans (by linarith only [softCost,hardCost])
  exact ⟨base,fun i j ui uj ib jb=>(norm_sub_le ..).trans (by linarith only [base i ui ib,base j uj jb])⟩

end YM.Integration.WilsonThermometerUnitFilingWhole
