import YM.Integration.WilsonOriginalPublicNodalQuadraticCutoffSelf
import YM.Integration.WilsonMovingForkCommonTranslation

/-! Common spatial translations act on the original Wilson law before any conditioned observation. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonOriginalPublicNodalQuadraticShift
open Function Filter Finset Set Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register
open Trace.Pilot PhysMS Frame XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonOriginalPublicNodalQuadraticSelf (self)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G)(h:ℕ)(ax:Axis)(x:RG17.Free R.family h)
    {Y:(Bel R.family.book).Hierarchy}{l:Filter (ℕ×ℕ)}
local notation "C" => R.family
local notation "D" => grades h h
local notation "submitted" r:max => homogeneous F J Z r h x

theorem move {n:ℕ}(d:Fin n → ℕ)(site N per:ℕ)(o:Fin n → Cover)(v:(C).book.Vector d)(shift:Cover):
    physical d site (fun i=>o i+shift) N per v = physical d site o N per v :=by
  by_cases top:site≤N
  · simp only [physical,Cells.location,dif_pos top]
    change (C).omega N per (WilsonOriginalTwoFlatGridCapture.word R d site N per top (fun i=>o i+shift) v)=
      (C).omega N per (WilsonOriginalTwoFlatGridCapture.word R d site N per top o v)
    exact WilsonMovingForkCommonTranslation.original R (p:=per) d top o v shift
  · simp only [physical,Cells.location,dif_neg top]

theorem original (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (below:l≤f.fuse){K:Set (Points 2)}(compact:IsCompact K)(sep:K⊆conf 2):
    ∃B:ℝ,0≤B ∧ ∀ᶠr in trail,∀(A:Arm (C) S l h (submitted r)){τ:Type}[Fintype τ]
      (site:ℕ)(o:τ → Fin 2 → Cover)(pos:τ → Points 2)(μ:τ → ℂ),(∀t,pos t∈K) →
      (∀t,Order.grid (C) site (o t)=r • pos t) → (∀t,Order.grid (C) site (o t)∈conf 2) →
      ∀ε:ℝ,0<ε → ∀ᶠw:ℕ×ℕ in l,∀shift:τ → Cover,‖∑t,μ t*physical D site (fun i=>o t i+shift t) w.1 w.2
        (columns R ax h h (A.source w) (A.source w))‖≤(∑t,‖μ t‖)*B+ε:=by
  obtain ⟨B,bp,original⟩:=WilsonOriginalPublicNodalQuadraticCutoffSelf.original R F J Z h ax x simple lead earned below compact sep
  refine ⟨B,bp,?_⟩
  filter_upwards [original] with r bound
  intro A τ finite site o pos μ hit placed safe ε ep
  filter_upwards [bound A site o pos μ hit placed safe ε ep] with w paid
  intro shift
  simpa only [move R] using paid

end YM.Integration.WilsonOriginalPublicNodalQuadraticShift
