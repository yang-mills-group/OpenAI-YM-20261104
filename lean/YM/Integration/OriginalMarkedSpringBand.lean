import YM.Integration.OriginalMarkedSpringWear
import YM.Gaps1020.Local.Pushed

/-! Complete, retained, and omitted marked densities on one actual physical
output.  The three bands have the native common supports, modes and hard gas. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedSpringBand
open Function Filter Lattice RG Pressure Tree Wilson Finset MeasureTheory Marker Overlay
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Pressure.Stores Pressure.Tube
open PhysicalNext PhysicalNext.Repeat Height Greenbelt ConnectedActivityE6.Blaze
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open Push.SectorMeasure YM.GapsLocal.Full
open Next.Fluctuations Oriented Work.E03 Shell SliceRows Control Window Coat Footprint Raw Matter
open Blaze.March Captain Silica Stained Shield
open Gas Ursell Trees RG.Supply Org Roost Opera Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open PhysicalNext.Repeat.Daisy.Charity.RG12 YM.RG01.Survive
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Merge Photo MergeProof Accent
open PhysicalNext.Repeat.Legato Extra.Trajectories
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}

/-- The full physical push, its genuine Taylor band and its signed discarded
part retain the same hard fields for every compound mode on the actual output. -/
def Output {c f : Side} (Z : Rep G c) (S : StepData c f) (β : ℝ)
    (source : Config G f→Poly Γ) (roots : V→Site c) (w : V→ℝ) (units : V→ℂ)
    (size allowance shade κ : ℝ) : Prop :=
  ∃ (full kept tail : Overlay.Bands Γ Z), S.push β source=full.density ∧
    GapsLocal.Full.Shares full kept tail units ∧ full.origins=roots ∧
    full.Active ∧ kept.Active ∧ tail.Active ∧ full.Radial w size shade allowance κ ∧
    kept.Radial w size shade allowance κ ∧ tail.Radial w 0 allowance allowance κ ∧
    ∀ j U,Poly.toll w j*‖(full.density U-kept.density U).part j‖ ≤
      (Real.exp (Fintype.card V*allowance)-1)*
        Poly.price w (OriginalMarkedSignedCutoff.lower j (full.density U))

section claim
variable {ι : Type} [Fintype ι] [Nonempty V] {c f L : Side} {W s μ C : ℝ}
    {S : StepData c f} {T : Tube G S} {Pt : Teller G} {Q : ConnectedActivityE6.Target G Pt}
    {o : Target.Order G W} {R : Rep G f} {H : Cash W s μ L Q o C T R}
    {A : Rep G c} {fields : ι→Lotus.Leaf R} {cost : ι→ℝ} {g : ι→Poly Γ}
    {hard : ℝ→Finset ι→Ovens.Code G c} {p : V→Site c} {i : V→ℂ} {M : ℕ}
    {u a b k : ℝ} {w : V→ℝ}

theorem report (h : Claim H A fields cost g hard p i M w u a b k) :
    Output A S R.beta (litGiven (S:=S) fields cost g i) p w i u a b k := by
  let rows (cut : ℕ→Prop) (constant : V→ℂ) :=
    Shared.scenery (H:=H) fields cost g cut constant p A hard Chi.canonical M
  refine ⟨rows (fun _=>True) i,rows (fun j=>¬ M+1 ≤ j) i,rows (fun j=>M+1 ≤ j) 0,
    h.push,⟨⟨rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,h.union,rfl,rfl,rfl,rfl⟩,
    rfl,h.complete.1,h.funded.1,h.remainder.1,h.complete.2,h.funded.2,h.remainder.2,?_⟩
  intro j U
  simpa only [h.push] using OriginalMarkedSignedCutoff.proper_price h j U
end claim

variable [Nonempty V] {ι : Type} [Fintype ι] (R : Run G) (hG : G.Simple)
    {N p m d : ℕ} (hm : m<N)
local notation "P" => ActualRunSpring.selected R N p m hm
local notation "fine" => R.family.path.rep N p (m+1)
local notation "coarse" => R.family.path.rep N p m
local notation "op" => R.family.path.levels.clock.op m p
local notation "coupling" => Pert.Asymptotics.regulatorRun R.family N p (m+1)

/-- This budget is fixed by the purchased history before cutoff or period.
The native zero grade in `shadowFactor` already contributes five powers. -/
def ordinary (R : Run G) (m seeds : ℕ) : ℝ :=
  (GapsLocal.Full.shadowFactor G (R.rolls.L (R.alloy.B.a.clock.J (m+1)))
    (R.alloy.B.a.clock.hatBeta m) 0)^seeds

include hG hm in
theorem received (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (sf : 100 ≤ (R.alloy.B.a.budget (m+1)).supportExponent)
    (sc : 100 ≤ (R.alloy.B.a.budget m).supportExponent)
    (level : GapsLocal.Full.target 0 (Fintype.card V) d ≤ R.alloy.B.a.clock.J (m+1))
    (o : V→Site (R.family.side (m+1) p)) (w : V→ℝ) (hw : ∀ j,0<w j)
    (occ : Extra.Multi.Occupancy ((op).ratio.parent ∘ o) (R.family.path.levels.clock.J (m+1)))
    (q : ι → MergeProof.Menu.Hat Γ (fine)) (offer : MergeProof.Menu.Offer o q w (fine).p.B ((fine).p.supportExponent-4) 1) :
    Output (coarse) (op) (fine).beta (GapsLocal.Full.given q 0) ((op).ratio.parent ∘ o) w 0 0
      ((Real.sqrt 2*coupling)^(d+1)) (ordinary R m (Fintype.card V))
      (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m)) := by
  obtain ⟨r,hr,h⟩ := OriginalMarkedSpringWear.registered R hG hm marks sf sc level o w hw occ q offer
  obtain ⟨issued,claim⟩ := h.adapted
  have β := congrArg (fun (sheet : Rep G (R.family.side (m+1) p))=>sheet.beta) (P).fine
  have changeG : coupling=GapsLocal.Vacuum.nativeG ((P).input (P).point.val).beta :=
    congrArg (fun t : ℝ=>(Real.sqrt t)⁻¹) β
  rw [(P).coarse,←hr,issued,β,changeG]
  exact report claim

end YM.Integration.OriginalMarkedSpringBand
end
