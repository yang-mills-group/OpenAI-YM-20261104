import YM.Integration.WilsonIndependentNotebookCubicField
import YM.WilsonCoeffUV.Product.Report.Shapes

/-! Carry each cubic first join under the same normalized Wilson chronology
as the original ordinary face. The earlier AB covariance is a whole field. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookCubicLedger
open Lattice RG Precision WilsonCoeffUV WilsonCoeffUV.Mer
open WilsonIndependentNotebookCubicField (Faces issue)
open scoped BigOperators Classical
variable {G:Gauge}

def deposit (A:Levels G)(Ñ:ChartRatio G)(N h m b:ℕ)(Z:Faces G):Era G ℝ:=
  let J:=cruises (V:=ℝ) A Ñ N h m b
  J Z.ab+J Z.ac+J Z.bc+J Z.connected

private theorem linear (A:Levels G){Ñ:ChartRatio G}{N h m b:ℕ}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (live:b ≤ m)(top:m ≤ N){P Q:Era G ℝ}(hp:Auth h P)(hq:Auth h Q):
    cruises A Ñ N h m b (P+Q)=cruises A Ñ N h m b P+cruises A Ñ N h m b Q:=by
  have d:=cruisePlus A live simple ratio top (hp.add hq) hq
  rw [add_sub_cancel_right] at d
  exact sub_eq_iff_eq_add.mp d.symm

theorem filed (A:Levels G){Ñ:ChartRatio G}{N i j k m b:ℕ}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (live:b ≤ m)(edge:m<N){P Q D:Era G ℝ}(p:Auth i P)(q:Auth j Q)(d:Auth k D):
    let h:=i+j+k;let Z:=issue A Ñ m N i j k P Q D
    cruises A Ñ N h (m+1) b (agateV (agateV P Q) D)=cruises A Ñ N h m b Z.proper+
      deposit A Ñ N h m b Z:=by
  intro h Z
  obtain ⟨proper,ab,ac,bc,third⟩:=WilsonIndependentNotebookCubicField.admitted A simple ratio edge p q d
  change Auth h Z.proper at proper
  change Auth h Z.ab at ab
  change Auth h Z.ac at ac
  change Auth h Z.bc at bc
  change Auth h Z.connected at third
  rw [←cruiseStep A Ñ _ live,WilsonIndependentNotebookCubicField.parts A Ñ m N i j k P Q D]
  change cruises A Ñ N h m b (Z.proper+(Z.ab+Z.ac+Z.bc+Z.connected))=_
  rw [linear A simple ratio live edge.le proper (((ab.add ac).add bc).add third),
    linear A simple ratio live edge.le ((ab.add ac).add bc) third,
    linear A simple ratio live edge.le (ab.add ac) bc,linear A simple ratio live edge.le ab ac]
  rfl

/-- Actual difference of the two unaltered ordinary histories. Both the
initial AB product and its lower conditional covariance remain in the bill. -/
theorem changed (A:Levels G){Ñ:ChartRatio G}{N i j k m b:ℕ}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (live:b ≤ m)(edge:m<N){P Q U V:Era G ℝ}(p:Auth i P)(q:Auth j Q)(u:Auth k U)(v:Auth k V):
    let h:=i+j+k;let Z:=issue A Ñ m N i j k P Q (U-V)
    let J:=cruises (V:=ℝ) A Ñ N h (m+1) b
    J (agateV (agateV P Q) U)-J (agateV (agateV P Q) V)=
      cruises A Ñ N h m b Z.proper+deposit A Ñ N h m b Z:=by
  intro h Z J
  have formula:=filed A simple ratio live edge p q (u.sub v)
  change cruises A Ñ N (i+j+k) (m+1) b (agateV (agateV P Q) (U-V))=cruises A Ñ N h m b Z.proper+deposit A Ñ N h m b Z at formula
  rw [pairingP,cruisePlus (b:=b) (m:=m+1) (N:=N) A (by omega) simple ratio (by omega)
    ((p.manor q).manor u) ((p.manor q).manor v)] at formula
  exact formula

/-- An already deposited incoming joint is charged separately on its true
older receiver. Its scalar and all its previous proper faces are retained. -/
theorem inherited (A:Levels G){Ñ:ChartRatio G}{N i j k m b:ℕ}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (live:b ≤ m)(edge:m<N){P Q D H:Era G ℝ}(p:Auth i P)(q:Auth j Q)(d:Auth k D)(h:Auth (i+j+k) H):
    let t:=i+j+k;let Z:=issue A Ñ m N i j k P Q D;let J:=cruises (V:=ℝ) A Ñ N t (m+1) b
    J H=J (H-agateV (agateV P Q) D)+(cruises A Ñ N t m b Z.proper+deposit A Ñ N t m b Z):=by
  intro t Z J
  rw [←filed A simple ratio live edge p q d]
  change _=cruises A Ñ N t (m+1) b (H-agateV (agateV P Q) D)+_
  rw [cruisePlus A (by omega) simple ratio (by omega) h ((p.manor q).manor d)]
  exact (sub_add_cancel _ _).symm

end YM.Integration.WilsonIndependentNotebookCubicLedger
