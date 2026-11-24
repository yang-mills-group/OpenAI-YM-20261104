import YM.Integration.WilsonMeasuredPublicEntranceFlatShares
import YM.Integration.WilsonMeasuredPublicEntranceTrialPeerBoard
/-! The very same physical or compensated source occupies each earlier
position in the ordered expansion. The trial lamp keeps its real test
and labels when viewed at the equal original budget. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOrderedPeers
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal
open Push.Local Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat Legato Extra.Histories
open WilsonMeasuredPublicEntrancePeerShares WilsonMeasuredPublicEntranceShareRoster
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V]{p f N:ℕ}(d:V → ℕ)(o:V → Site (R.family.side f p))
variable (X E:∀v,Coefficient (R.family.labels.level (d v)) (R.family.side f p))
local notation "P" => R.family.path.rep N p f
def chosen (m:Share V)(v:V):Coefficient (R.family.labels.level (d v)) (R.family.side f p):=
  if pick m v then E v else X v
def allowance (B F:V → ℝ)(m:Share V)(v:V):ℝ:=if pick m v then F v else B v
def incidence (v:V)(U:Config G (R.family.side f p)):ℂ:=
  (X v).exponentialEntry (o v) (R.family.localSection (d v)) P U

theorem field {T I:Type}[Countable I](S:Census V)(W:Rep G (R.family.side f p))
    (Y:Lamps T I G W.p o S)(x:T)(m:Share V)(v:V)(U:Config G (R.family.side f p)):
    WilsonMeasuredPublicEntranceFlatShares.rest R
      (incidence (N:=N) R d o X) (fun i Z=>(Y.log x Z).part (S.fire i)) (incidence (N:=N) R d o E) m v U=
    WilsonMeasuredPublicEntranceTrialPeerBoard.field (N:=N) R S d o W (chosen R d X E m) Y x m.after.toFinset v U:=by
  unfold WilsonMeasuredPublicEntranceFlatShares.rest WilsonMeasuredPublicEntranceShareRoster.field
    WilsonMeasuredPublicEntranceTrialPeerBoard.field head incidence chosen
  simp only [List.mem_toFinset]
  split_ifs <;> rfl

def hosted {n:Side}{I T:Type}{S:Census V}{xs:V → Site n}{A B:BudgetPoint}
    (h:A=B)(Y:Lamps T I G A xs S):Lamps T I G B xs S:=h ▸ Y
theorem log {n:Side}{I T:Type}[Countable I]{S:Census V}{xs:V → Site n}{A B:BudgetPoint}
    (h:A=B)(Y:Lamps T I G A xs S)(x:T)(U:Config G n):
    ((hosted h Y).log x U)=Y.log x U:=by cases h;rfl
theorem paid {n:Side}{I T:Type}{S:Census V}{xs:V → Site n}{A B:BudgetPoint}
    (h:A=B)(Y:Lamps T I G A xs S)(w:V → ℝ)(b:ℕ)(α a:ℝ):
    (hosted h Y).Paid w b α a ↔ Y.Paid w b α a:=by cases h;rfl

end YM.Integration.WilsonMeasuredPublicEntranceOrderedPeers
end
