import YM.Integration.WilsonIndependentConditionedFolioPupil
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonOriginalPublicNodalTestedChronology

/-! An individual native visit of the tested pupil on every occupied mark. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioVisit
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)

open WilsonIndependentNotebookConstantSeat (issue part)
open private seated_sum from YM.Integration.WilsonIndependentNotebookConstantSeat
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedOpeningColumn (column)


open WilsonIndependentMatchedCoverProfile (word)

open WilsonIndependentRawRosterWord (fold degree)
open RegulatorIR.Cluster (Composite)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPublicNodalTestedChronology (registered rank)
open WilsonIndependentConditionedFolioPupil (atSite)

private theorem swapped {G:Gauge}{a b:ℕ}{X Y:Era G ℝ}(hx:Auth a X)(hy:Auth b Y):agateV X Y=agateV Y X:=by
  apply WilsonIndependentMatchedOpeningFaithful.original (hx.manor hy) (Nat.add_comm b a ▸ hy.manor hx)
  intro n v
  change here n v (Blue.flash (woad (X.1 n) (Y.1 n)))=here n v (Blue.flash (woad (Y.1 n) (X.1 n)))
  rw [woadap _ _ (finite_shell (hx.span n)) (finite_shell (hy.span n)),
    woadap _ _ (finite_shell (hy.span n)) (finite_shell (hx.span n)),mul_comm]

private theorem scales {G:Gauge}{a b:ℕ}{X Y:Era G ℝ}(hx:Auth a X)(hy:Auth b Y)(r s:ℝ):
    agateV (r•X) (s•Y)=(r*s)•agateV X Y:=by
  rw [WilsonSeparatedPrefixMovingFixedCapture.scaled,swapped (hx.μ r) hy,
    WilsonSeparatedPrefixMovingFixedCapture.scaled,swapped hy hx,smul_smul,mul_comm s r]

variable {G:Gauge}(R:Run G)(W:Initialize G){d D:ℕ}(w:d<D)
local notation "F" => R.family.labels.level d

def visit (i:(R.family.labels.level d).Index)(φ:Rarity D)(x y:ℝ)(o:CellR)(n:Cover):Era G ℝ:=
  drumB d x • locale o (shoe (Shrine (plate (sectionAt R W false d) w) (issue F false (Pi.single i 1))) φ x y n)

theorem seatValue (i:(R.family.labels.level d).Index)(φ:Rarity D)(x y:ℝ)(o:CellR)(n:Cover):
    visit R W w i φ x y o n=(drumB d x*φ.ψ.val (Mer.position x y o n)) • column R W false w (seat F i) n:=by
  classical
  change drumB d x • planted R W false w (wheelC x y n φ.ψ o) (issue F false (Pi.single i 1)) n=_
  rw [WilsonIndependentConditionedFolioIssue.original,Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,atSite]
    simp [part,smul_smul]
  · intro j _ diff
    rw [Pi.single_eq_of_ne diff]
    simp [part]
  · simp

variable {I:Type}(d₀:I→ℕ){D₀:I→ℕ}(key:(i:I)→(R.family.labels.level (d₀ i)).Index)
    (cut:∀i,d₀ i<D₀ i)(φ:(i:I)→Rarity (D₀ i))(x y:ℝ)(o:CellR)(n:I→ Cover)

def cluster : Composite I → Era G ℝ
  | .atom i=>visit R W (cut i) (key i) (φ i) x y o (n i)
  | .pair a b=>agateV (cluster a) (cluster b)

theorem opened (J:Composite I):
    cluster R W d₀ key cut φ x y o n J=
      fold (fun i=>drumB (d₀ i) x*(φ i).ψ.val (Mer.position x y o (n i))) J •
        field R W (fun _=>false) d₀ key cut n J:=by
  induction J with
  | atom i=>exact seatValue R W (cut i) (key i) (φ i) x y o (n i)
  | pair A B a b=>
    change agateV _ _=_ •agateV _ _
    rw [a,b]
    exact scales (WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _=>false) d₀ key cut n A)
      (WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _=>false) d₀ key cut n B) _ _

end YM.Integration.WilsonIndependentConditionedFolioVisit
end
