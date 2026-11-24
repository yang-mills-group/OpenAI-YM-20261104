import YM.Integration.WilsonThermometerFiniteConnectedCells
import YM.Integration.WilsonThermometerUnitFilingCylinder

/-! The true complex connected reading with its full signed measured head deducted. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingSignedCells
open Finset Marker Extra.Trajectories Comparison.RG02
open WilsonThermometerCenteredScalar WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
open WilsonThermometerFiniteConnectedRemainder
open private pair cubic from YM.Integration.WilsonThermometerFiniteConnectedRemainder
variable {ι:Type*} [Fintype ι]
local notation "J" => Stock.census (Fin 3)

private theorem proper (w : ι → ℂ) (F Q : ι → Poly J)
    (fu : ∀ i, (F i).part (J).quiet = 1) (qu : ∀ i, (Q i).part (J).quiet = 1)
    (A B C : ℝ) (ha : 0 ≤ A) (hb : 0 ≤ B)
    (two : ∀ s : Finset (Fin 3), s.card = 2 →
      ∑ i, ‖w i‖*‖read (total (F i) (Q i)) s‖^2 ≤ A^2)
    (one : ∀ v : Fin 3, ∑ i, ‖w i‖*‖read (total (F i) (Q i)) {v}‖^2 ≤ B^2)
    (three : ∀ v : Fin 3, ∑ i, ‖w i‖*‖read (total (F i) (Q i)) {v}‖^3 ≤ C^3) :
    ‖(∑ i, w i*(read (Extra.Trajectories.connected (F i)) univ -
      read (Extra.Trajectories.connected (Q i)) univ)) - ∑ i,w i*(total (F i) (Q i)).part full‖ ≤ 3*(A*B) + 2*C^3 := by
  let s (v : Finset (Fin 3)) (i : ι) := read (total (F i) (Q i)) v
  have pairs (v : Finset (Fin 3)) (i : Fin 3) (hv : v.card = 2) :
      ‖∑ j, w j*(s v j*s {i} j)‖ ≤ A*B := pair w _ _ ha hb (two v hv) (one i)
  have trip : ‖∑ j, w j*(s {0} j*s {1} j*s {2} j)‖ ≤ C^3 :=
    cubic w _ _ _ (three 0) (three 1) (three 2)
  have form : (∑ i, w i*(read (Extra.Trajectories.connected (F i)) univ -
      read (Extra.Trajectories.connected (Q i)) univ)) =
      (∑ i, w i*s univ i) - ((∑ i, w i*(s {0,1} i*s {2} i)) +
        (∑ i, w i*(s {0,2} i*s {1} i)) + (∑ i, w i*(s {1,2} i*s {0} i))) +
        (2 : ℂ)*(∑ i, w i*(s {0} i*s {1} i*s {2} i)) := by
    rw [Finset.mul_sum]
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [cell (F i) (Q i) (fu i) (qu i)]
    dsimp [s]
    ring
  change ‖(∑ i,w i*(read (Extra.Trajectories.connected (F i)) univ-
       read (Extra.Trajectories.connected (Q i)) univ))-(∑ i,w i*s univ i)‖≤_
  rw [form]
  set P:ℂ:=((∑ i, w i*(s {0,1} i*s {2} i)) + (∑ i, w i*(s {0,2} i*s {1} i)) + (∑ i, w i*(s {1,2} i*s {0} i))) with pr
  set T:ℂ:=∑ i,w i*(s {0} i*s {1} i*s {2} i)
  rw [show (∑ i,w i*s univ i)-P+2*T-(∑ i,w i*s univ i) = -(P)+2*T by ring]
  calc
    _ ≤ ‖-P‖+‖(2:ℂ)*T‖:=norm_add_le .. 
    _ ≤ _ :=by
      rw [norm_neg,norm_mul];norm_num
      rw [pr]
      have pt: ‖(∑ i,w i*(s {0,1} i*s {2} i))+(∑ i,w i*(s {0,2} i*s {1} i))+(∑ i,w i*(s {1,2} i*s {0} i))‖ ≤ 3*(A*B) :=by
        refine (norm_add_le ..).trans ((add_le_add (norm_add_le ..) le_rfl).trans ?_)
        linarith [pairs {0,1} 2 (by decide),pairs {0,2} 1 (by decide),pairs {1,2} 0 (by decide)]
      linarith

open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Extraction Table Spec
open Climb Trace.Pilot RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East FVA1 OriginalForcedAddresses
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) (A : Group R.family 6)
open WilsonThermometerFiniteConnectedCells
local notation "J!" => Stock.census (Fin 3)
local notation "sites" z:max => Fin 3 → Site (R.family.side z.1 z.2)

local notation "χ" r:max z:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
local notation "W" φ:max r:max z:max => WilsonSeparatedOriginalThermometerCells.weight φ (χ r z)

theorem original {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ r : ℝ, ∀ φ : Test 3, ∀ Q : sites z → Poly J!,
    (∀ y, (Q y).part (J!).quiet = 1) → ∀ A₂ A₁ A₃ : ℝ, 0 ≤ A₂ → 0 ≤ A₁ →

    let δ := fun (y : sites z) => read (total (measured R A z y) (Q y))
    (∀ s : Finset (Fin 3), s.card = 2 → ∑ y, ‖(W φ r z) y‖*‖δ y s‖^2 ≤ A₂^2) →
    (∀ t : Fin 3, ∑ y, ‖(W φ r z) y‖*‖δ y {t}‖^2 ≤ A₁^2) →
    (∀ t : Fin 3, ∑ y, ‖(W φ r z) y‖*‖δ y {t}‖^3 ≤ A₃^3) →
    ‖φ.applyTo (WilsonPositionThermometerGradedReading.full r A z) - reference R z r φ Q - WilsonThermometerUnitFilingCylinder.tested R A z r φ Q‖
      ≤ 3*(A₂*A₁) + 2*A₃^3 := by
  filter_upwards [WilsonThermometerCenteredCredit.unit_table R A checked unit] with z funded
  intro r φ Q qu A₂ A₁ A₃ ha hb
  dsimp only
  intro pair single cube
  let w := (W φ r z)
  let F := measured R A z
  have quiet (y : sites z) : (F y).part (J!).quiet = 1 := funded (placement R z y)
  have filed : head R A z r φ Q = ∑ y, w y*(total (F y) (Q y)).part full := by
    rw [head,WilsonSeparatedOriginalThermometerCells.tested φ (χ r z)
      (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
      (fun y => ∑ s : (J!).Mode, weight (Q y) s * WilsonPositionThermometerGradedReading.row A z y s.val)]
    apply sum_congr rfl
    intro y _
    rw [WilsonThermometerCenteredAlgebra.affine]
    rfl
  have all := proper w F Q quiet qu A₂ A₁ A₃ ha hb pair single cube
  let trueVal (y : sites z) := WilsonPositionThermometerConnected.value
    (WilsonPositionThermometerGradedReading.row A z y)
  let specVal (y : sites z) := WilsonPositionThermometerConnected.value (read (Q y))
  have actual (y : sites z) : read (Extra.Trajectories.connected (F y)) univ = trueVal y :=
    WilsonThermometerCenteredScalar.three _ (quiet y)
  have named (y : sites z) : read (Extra.Trajectories.connected (Q y)) univ = specVal y :=
    WilsonThermometerCenteredScalar.three _ (qu y)
  simp only [actual,named,mul_sub,Finset.sum_sub_distrib] at all
  have originalTest := WilsonSeparatedOriginalThermometerCells.tested φ (χ r z)
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
  change ‖φ.applyTo (fun x => trueVal ((χ r z) x)) -
    φ.applyTo (fun x => specVal ((χ r z) x)) - head R A z r φ Q‖ ≤ _
  rw [originalTest trueVal,originalTest specVal,filed]
  exact all


end YM.Integration.WilsonThermometerUnitFilingSignedCells
