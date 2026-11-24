import YM.Integration.WilsonIndependentNotebookCubicMass
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! The changed third input is the actual placed raw stencil minus its
complete fitted column on the same original quiet at each upper date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookCubicCut
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Filter Function Matrix Lattice RG Laurent
open Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power Embroider Precision Exterior Fountain
open Soil Gauge Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedCoveredSeats WilsonIndependentMatchedFittedSeat
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open scoped Topology BigOperators Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {T:SectionData F}{p:h<D}{v:Rails h k u e}{E W K U:Credit}

def raw (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):Era G ℝ:=
  word (a • X.pt) φ (paceT X.ax.S X.m X.ceilC) y o h

/-- The seat has its actual lower-field subtractions on the full finite
and covered representations at the original top. -/
theorem input (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    let Y:=raw X a φ y o;let C:=receiving X a φ y o X.i
    Auth k Y ∧ Auth h C ∧ Auth k (seat X a φ y o X.i) ∧ Y-C=seat X a φ y o X.i:=by
  intro Y C
  have split:Y=seat X a φ y o X.i+C:=WilsonIndependentMatchedTotalTop.placed X a φ y o
  have proper:Auth h C:=(wired X.vesselsC (sectionSeal T p) (passport X) φ (dose X a) X.m X.N X.i
    X.ha (X.hc.trans X.hn) y o).1 X.i le_rfl
  have stable:Auth k (seat X a φ y o X.i):=(traced X a φ y o).1 X.i le_rfl
  exact ⟨split ▸ stable.add (proper.tall v.hk),proper,stable,by rw [split,add_sub_cancel_right]⟩

private theorem travel (A:Levels G)(Ñ:ChartRatio G)(N m n j:ℕ)(P:ℕ→Era G ℝ)
    (push:∀i<n,verseI A Ñ (m+i) N j (P (i+1))=P i)(i:ℕ)(le:i ≤ n):
    cruises A Ñ N j (m+n) (m+i) (P n)=P i:=by
  obtain ⟨t,ht⟩:=Nat.exists_eq_add_of_le le
  induction t generalizing i with
  | zero =>
    have eq:n=i:=by omega
    subst n
    exact cruises_top ..
  | succ t ih =>
    have before:m+i < m+n:=by omega
    rw [cruises_sub A Ñ N j _ before]
    have older:=ih (i+1) (by omega) (by omega)
    change cruises A Ñ N j (m+n) (m+i+1) (P n)=P (i+1) at older
    rw [older,push i (by omega)]

/-- Keep all lower feeds of the fitted stencil when the shared computation
uses the cap of its genuine stable difference. -/
theorem dated (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)(i:ℕ)(live:i ≤ X.i):
    let J:=cruises (V:=ℝ) X.ax X.tx X.N k X.ceilC (X.m+i)
    let Y:=raw X a φ y o;let C:=receiving X a φ y o X.i
    J Y-J C=seat X a φ y o i ∧ J C=receiving X a φ y o i:=by
  intro J Y C
  obtain ⟨r,f,_,change_top⟩:=input X a φ y o
  have old:=wired X.vesselsC (sectionSeal T p) (passport X) φ (dose X a) X.m X.N X.i
    X.ha (X.hc.trans X.hn) y o
  have linear:=cruisePlus X.ax (Nat.add_le_add_left live X.m) X.vesselsC.hG X.vesselsC.green
    (X.hc.trans X.hn) r (f.tall v.hk)
  have stable:=travel X.ax X.tx X.N X.m X.i k (seat X a φ y o) (traced X a φ y o).2 i live
  refine ⟨linear.symm.trans (change_top ▸ stable),?_⟩
  apply travel X.ax X.tx X.N X.m X.i k (receiving X a φ y o) _ i live
  intro j hj
  have hf:=old.1 (j+1) (by omega)
  have up:=verseExpand X.ax (m:=X.m+j) (N:=X.N) (by have hi:=X.hc.trans X.hn;omega)
    X.vesselsC.hG X.vesselsC.green hf v.hk
  exact up.symm.trans (old.2 j hj)

/-- On the specified genuine cut, comparing the complete original and
fitted products gives the four open connected deposits in the dated bill. -/
theorem original (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)
    {s t host:ℕ}(earlier:host ≤ X.ceilC){A B:Era G ℝ}(pa:Auth s A)(pb:Auth t B):
    let Y:=raw X a φ y o;let C:=receiving X a φ y o X.i
    let J:=cruises (V:=ℝ) X.ax X.tx X.N (s+t+k) X.ceilC host
    let sum:=WilsonIndependentNotebookCubicSeeds.bill X.ax X.tx host X.N s t k
      (X.ceilC-host) A B Y C
    J (agateV (agateV A B) Y)-J (agateV (agateV A B) C)=sum ∧
      J (agateV (agateV A B) (seat X a φ y o X.i))=sum:=by
  intro Y C J sum
  obtain ⟨r,f,_,difference⟩:=input X a φ y o
  have dates:host+(X.ceilC-host)=X.ceilC:=by omega
  have actual:=WilsonIndependentNotebookCubicSeeds.original X.ax X.vesselsC.hG X.vesselsC.green
    (m:=host) (N:=X.N) (n:=X.ceilC-host) (by rw [dates];exact X.hc.trans X.hn) pa pb r (f.tall v.hk)
  dsimp only at actual
  rw [dates] at actual
  refine ⟨actual,?_⟩
  dsimp only [J]
  rw [←difference,pairingP,cruisePlus X.ax earlier X.vesselsC.hG X.vesselsC.green (X.hc.trans X.hn)
    ((pa.manor pb).manor r) ((pa.manor pb).manor (f.tall v.hk))]
  exact actual

end YM.Integration.WilsonIndependentNotebookCubicCut
