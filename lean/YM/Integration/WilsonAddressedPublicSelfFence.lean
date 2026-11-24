import YM.Integration.WilsonAddressedPublicSelfPurchase
import YM.Integration.WilsonAddressedPublicPairFence

/-! Keep the protected signed trial and the actual two card supports on the same reflected sample. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
namespace YM.Integration.WilsonAddressedPublicSelfFence
open Function Filter Finset Lattice RG Wilson Source Labels Cells OPE Extraction Spec
open Table PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical RegulatorIR.FVAAlt2 Pert.Asymptotics
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee width)
open WilsonAddressedPublicOpticalPair (length)
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalPublicNodalSeed (vector signed)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonAddressedPublicSelfPurchase (source at_grid)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,S.Field (d i).val)(b:Fin 2→Bool)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "fees" => (fun i=>fee F (B i) (d i) (v i) (b i))
local notation "widths" => (fun i=>width F (B i) (d i) (v i) (b i))
local notation "caps" => grades (d 0).val (d 1).val

theorem original (cash:Trace.Terrace.PostT (A)):
    let m:=min (widths 0) (widths 1)
    0 < m → ∀site:ℕ,∀ᶠ w:ℕ×ℕ in f.fuse,
    ∀(K u:ℕ)(fk:site ≤ K)(kn:K ≤ w.1)(ear:u ≤ K)(ax:Axis)
      (W:Initialize G)(file:Filed R caps K)(L:Type)[Fintype L](o:L→Fin 2→ Cover)(X:L→Sample 2)(μ:L→ℂ),
    (∀a i,wrap ((C).side K w.2) ((X a).layout i)=seats (R:=R) fk w.2 (o a) i) →
    (∀a,‖(C).S.gridPoint site (o a 0-o a 1)‖ ≤ 1) →
    (∀a,2*(C).S.a (m-1) < ‖(C).S.gridPoint site (o a 0)-(C).S.gridPoint site (o a 1)‖) →
    let Y:=source R F B d v b ax w
    let col:=vector R caps (N:=w.1) (per:=w.2) file Y
    let raw:=fun a=>word R caps site w.1 w.2 (fk.trans kn) (o a) Y
    let names:=doses R caps file.station (N:=w.1) (per:=w.2) (file.A w.1 w.2) Y
    let trial:=fun a=>product R caps (N:=w.1) (seats (R:=R) fk w.2 (o a)) names
    let obs:=∑a,μ a*(C).omega w.1 w.2 (raw a)
    let ν:=regulatorRun (C) w.1 w.2 K
    ‖obs‖ ≤ (∑a,‖μ a‖)*∏i,fees i ∧ ∀(q:ℕ)(due:L→ℝ),
    (∀a,‖WilsonThermometerUnitFilingCoarse.reading R (N:=w.1) (RG16.Literal.credit (C) w.1 w.2 0 (raw a) K kn) u ear-
      WilsonThermometerUnitFilingCoarse.reading R (N:=w.1) (numerator R w.1 w.2 K (trial a)) u ear‖ ≤ due a) →
    ‖sampled R W caps col X μ univ q ν-obs‖ ≤
      (∑a,‖μ a‖*(‖WilsonOriginalTwoFlatGridScaling.gap R w.1 w.2 u (ear.trans kn) (raw a)‖+due a))+
      ‖∑a,μ a*signed R W caps (N:=w.1) (per:=w.2) file Y ear (X a) q‖:=by
  classical
  intro m pos site
  filter_upwards [WilsonAddressedPublicPairFence.film R F B d v b cash pos] with w sides
  intro K u fk kn ear ax W file L _ o X μ placed compact far Y col raw names trial obs ν
  have apart(h:L):(C).S.a (m-1) < (C).S.a w.1*
      (separation (Cells.location (C).S site w.1 w.2 (o h 0)) (Cells.location (C).S site w.1 w.2 (o h 1)):ℝ):=by
    have dist:=WilsonAddressedPublicPairGeometry.gap (C) (p:=w.2) (fk.trans kn) (o h 0) (o h 1) (compact h)
    have strict:=(far h).trans_le dist
    linarith only [strict]
  constructor
  · change ‖∑a,μ a*(C).omega w.1 w.2 (word R caps site w.1 w.2 (fk.trans kn) (o a) (source R F B d v b ax w))‖ ≤ _
    simp_rw [at_grid R F B d v b ax (fk.trans kn)]
    apply sides
    intro i i' t diff
    fin_cases i <;> fin_cases i'
    · exact (diff rfl).elim
    · exact apart t
    · rw [separation_comm];exact apart t
    · exact (diff rfl).elim
  · intro q due spent
    exact WilsonAddressedTrialSelfSensor.weighted R W caps file Y fk kn ear o X μ placed q due spent

end YM.Integration.WilsonAddressedPublicSelfFence
end
