import YM.Integration.WilsonOriginalCompanionTwinIntake
import YM.Integration.WilsonOriginalCompanionHardCurrency

/-! The submitted hard coefficient and its two unchanged peers on the actual canonical course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionCanonicalSeat
open Function Finset Filter MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn
open Push
open Lodestar Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Lotus
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonOriginalDepositedHard WilsonOriginalGalleryTwins WilsonOriginalCompanionTwinIntake
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple){V T I:Type}[Fintype V][DecidableEq V][Countable I]
  {d:ℕ}{F:Frame G d}(A:Hol G)(S:SectionData F)
local notation "C" => R.family
local notation "L" => R.family.path.levels
local notation "J" => Stock.census V

include simple in
theorem original : ∀ᶠ f:ℕ in atTop,∀ N per:ℕ, f≤N →
    let P:=(C).path.rep N per f
    let κ:=LocalComparison.forcedDivisor (C) f
    let cash:=(L).clock.forcedAllowance f
    ∃rent:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent cash,∀
    (o:V→Site ((C).side f per))(v:V)(h:Coefficient F ((C).side f per))
    (fit:h.Format (o v) A P)(t:T→ℂ)(E:Lamps T I G P.p o (J))(w:V→ℝ)(B:ℝ),
    (∀i,0<w i) → (∀x,‖t x‖≤1) → h.remBound (o v) P κ B → w v^2*(κ*B)≤1/2 →
    E.Paid (fun i=>w i^2) P.p.B P.p.supportExponent 1 → ∀a:ℝ,0≤a → a≤P.p.supportExponent →
    let old:= (Hard.rent rent : Hard T P.p P.activities.forced P.activities.K o (J))
    let L₀:= (⟨E,old⟩:Gallery T I o P (J))
    let L₁:= (⟨E,WilsonOriginalDepositedHard.joined old v h fit t⟩:Gallery T I o P (J))
    ∀ x:T, Admitted L₀ x w a ∧ Admitted L₁ x w a ∧ clear L₀ x=clear L₁ x ∧
      ∀(s:(J).Mode)(U:Config G ((C).side f per)),
      t x*h.density (o v) S P U*WilsonMeasuredCompanionFace.peers E v s x U=
        t x*(soft h).density (o v) S P U*WilsonMeasuredCompanionFace.peers E v s x U+
          (L₁.density x U).part s-(L₀.density x U).part s:=by
  filter_upwards [WilsonMeasuredOwnerReserve.room R simple,WilsonOriginalCompanionHardCurrency.reserve R simple]
    with f reserve price N per top
  let W:=((R.T.sticks N per).prices f (Nat.zero_le _) top).1
  let P:=(C).path.rep N per f
  let cash:=(L).clock.forcedAllowance f
  let κ:=LocalComparison.forcedDivisor (C) f
  have cap : κ≤1:=price.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _)))
  let rent : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent cash:=
    Hard.rentValid W.valid.labels.forced W.valid.labels.boundK
  refine ⟨rent,?_⟩
  intro o v h fit t E w B positive bound inc bought cover a expo within
  dsimp only
  intro x
  have small :cash≤1/2:=reserve.trans (div_le_div_of_nonneg_right cap (by norm_num))
  exact WilsonOriginalCompanionTwinIntake.received rent v h fit S t E w positive W.valid bound inc
    (small.trans (by norm_num)) (by linarith only [small,bought]) cover expo within x

end YM.Integration.WilsonOriginalCompanionCanonicalSeat
end
