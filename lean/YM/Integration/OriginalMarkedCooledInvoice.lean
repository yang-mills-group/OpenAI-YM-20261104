import YM.Integration.OriginalMarkedCooledBirth
import YM.Integration.QLocalFullRootedOffer

/-! A preselected radius on the stage clock pays the full signed ordinary
source of the original Q at the very aperture used by the physical outfit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedCooledInvoice
open Function Finset Lattice Wilson RG Marker MergeProof Menu FVA1
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem lower {n : Side} {Γ : Census V} {Y : Rep G n} {I : Type} [Fintype I]
    {o : V→Site n} {q : I→Menu.Hat Γ Y} {w : V→ℝ} (hw : ∀i,0<w i)
    {b : ℕ} {e d : ℝ} (offer : Menu.Offer o q w b e d) : Menu.Offer o q w b (e-4) d := by
  refine ⟨offer.sites,fun z=>Push.AbsoluteSums.budget_mono (offer.budget z) ?_ ?_⟩
  · intro i
    split_ifs
    · exact mul_nonneg (Menu.Crew w hw) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    split_ifs
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (sub_le_self e (by norm_num)) (by positivity))) (Menu.Crew w hw)
    · exact le_rfl

variable {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)
def radius (m : ℕ) : ℝ := QLocalFullRootedOffer.radius 1 (OriginalMarkedCooledBirth.fee R hG u J A m)

variable (z : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V→Site (R.family.side (z.level+1) z.period)) (μ : ℝ) (orders : V→ℕ)
local notation "Γ" => Stock.census V
local notation "D" => ActualOriginalQPointSetup.pointDatum R J z.period (z.level+1) o
local notation "roots" => ActualOriginalQPackets.positions (D) u
local notation "Y" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "M" => ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
local notation "E" => OriginalMarkedBirthRows.active R hG u J A z Q o μ orders
local notation "g" => regulatorRun R.family z.cutoff z.period (z.level+1)
local notation "δ" => radius R hG u J A z.level

theorem native (x : IndependentTests (ActualOriginalQPointSetup.request R u J).tests) :
    0<δ ∧ δ≤1 ∧ ∃(slot : (E)→ℕ) (m : (E)×Bool→Menu.Hat Γ (Y)),
      (∀i s,(m (i,s)).s=(M).mode i ∧ Menu.WKey (m (i,s))=.logKey (slot i)) ∧
      Menu.Offer (roots).origin m (fun _=>δ) (Y).p.B ((Y).p.supportExponent-4) 1 ∧
      (∀U,GapsLocal.Full.given m 0 U=((Y).eval U:ℂ) • Poly.pass
        (ManuscriptQLocalOriginalConditionalTail.source (M) (Y).p (g) x 1 U)) := by
  obtain ⟨slot,m,keys,fee,reads⟩ := OriginalMarkedCooledBirth.enrolled R hG u J A z Q o μ orders x
  have hw : ∀_ : V,0<(1:ℝ) := fun _=>zero_lt_one
  obtain ⟨pos,top,paid⟩ := QLocalFullRootedOffer.limited (roots).origin (fun _ : V=>1) hw m
    1 zero_lt_one ((Y).p.supportExponent-4) (Y).p.B (lower hw fee)
  exact ⟨pos,top,slot,m,keys,by simpa only [radius,mul_one] using paid,reads⟩

end YM.Integration.OriginalMarkedCooledInvoice
end
