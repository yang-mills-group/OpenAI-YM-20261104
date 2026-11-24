import YM.Integration.WilsonIndependentFittedMixedReturn
import YM.Integration.WilsonIndependentMatchedTotalTop
import YM.Integration.WilsonIndependentCollarWeightedCruise

/-! All printed pivots use their own actual report coefficients. The relative
kinetic clock, the two slot orders and the scalar survive the finite sum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedPivotRoster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (axis film)
open WilsonIndependentFittedReportedFilm (weight)
open WilsonIndependentFittedMixedReturn (planted word paid)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOlderFreshSoftSocketKinetic (reading)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

theorem basis (j l:Alma F):axis j 0 l=if l=j then 1 else 0:=by
  by_cases eqn:l=j <;> apply PowerSeries.ext <;> intro q <;> simp [axis,eqn,PowerSeries.coeff_one]

theorem split (d:Verse F):d=∑j,weight (d j) (axis j 0):=by
  funext l
  simp only [Finset.sum_apply,WilsonIndependentFittedReportedFilm.weight,basis,mul_ite,mul_one,mul_zero]
  simp

private theorem traced (A:Levels G)(O:ChartRatio G)(N m j:ℕ)(c d:Verse F):
    steep A O T p N m j (c+d)=steep A O T p N m j c+steep A O T p N m j d:=by
  funext i
  let M:=bindingS A O T p N m j false
  let τ:=reel (relativeC A O N m j)
  change τ (∑b,M i b*(c b+d b))=τ (∑b,M i b*c b)+τ (∑b,M i b*d b)
  simp only [mul_add,sum_add_distrib,map_add]

private theorem shrine (P:Island F D)(c d:Verse F):Shrine P (c+d)=Shrine P c+Shrine P d:=by
  unfold Shrine
  rw [←sum_add_distrib]
  refine sum_congr rfl fun j _=>?_
  have aff {V U:Type}[NormedAddCommGroup V][NormedSpace ℝ V](f g:Cost)(Z:Pal V U):
      affix (f+g) Z=affix f Z+affix g Z:=by
    funext n;simp only [affix,map_add,add_smul,sum_add_distrib,Pi.add_apply]
  exact Prod.ext (funext fun n=>aff (c j) (d j) _) (aff (c j) (d j) _)

private theorem port {V Z:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
    [NormedAddCommGroup Z][NormedSpace ℝ Z](f:V→L[ℝ]Z)(P Q:Era G V):
    tuftV f (P+Q)=tuftV f P+tuftV f Q:=
  Prod.ext (funext fun n=>(ply f.toLinearMap).map_add (P.1 n) (Q.1 n)) ((ply f.toLinearMap).map_add P.2 Q.2)

private theorem profile (d:ℕ)(P Q:TowerS G D)(φ:Rarity D)(x y:ℝ):
    pupil d (P+Q) φ x y=pupil d P φ x y+pupil d Q φ x y:=by
  unfold pupil
  rw [←sum_add_distrib]
  refine sum_congr rfl fun j _=>?_
  rw [←smul_add]
  congr 1

def docket (X:CutsP H T p v E W K U)(φ:Rarity D)(y:ℝ)(o:CellR):Verse F→+Era G ℝ:=
  AddMonoidHom.mk' (fun c=>planted X c φ y o) (by
    intro c d
    let P:=Peaks X.ax X.tx T p X.N (X.m+X.i)
    let t:=paceT X.ax.S X.m (X.m+X.i)
    let w:=steep X.ax X.tx T p X.N X.m (X.m+X.i-X.m)
    change tuftV (century o) (pupil h (Shrine P (w (c+d))) φ t y)=
      tuftV (century o) (pupil h (Shrine P (w c)) φ t y)+tuftV (century o) (pupil h (Shrine P (w d)) φ t y)
    dsimp only [w];rw [traced,shrine,profile,port])

def left (P:Era G ℝ):Era G ℝ→+Era G ℝ:=
  AddMonoidHom.mk' (agateV P) fun A B=>(WilsonIndependentMatchedTotalTop.binary A B P).2
def right (P:Era G ℝ):Era G ℝ→+Era G ℝ:=
  AddMonoidHom.mk' (fun Q=>agateV Q P) fun A B=>(WilsonIndependentMatchedTotalTop.binary A B P).1

theorem sources (X:CutsP H T p v E W K U)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR):
    planted X d φ y o=∑j,planted X (weight (d j) (axis j 0)) φ y o:=by
  change (docket X φ y o) d=∑j,(docket X φ y o) (weight (d j) (axis j 0))
  nth_rw 1 [split d]
  exact map_sum ..

theorem joined (X:CutsP H T p v E W K U)(P:Era G ℝ)(prior:Auth k P)(s:ℕ)(before:s≤X.m)
    (d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)(r:ℕ)(x:Fin r→YForest G):
    let Q:=planted X d φ y o
    let U:=fun j=>film X j 0 φ y o X.i
    let τ:=fun j=>clock X.ax X.tx X.N X.m s (d j)
    word X s P Q r x=∑j,τ j*word X s P (U j) r x ∧
      word X s Q P r x=∑j,τ j*word X s (U j) P r x:=by
  intro Q U τ
  let M:=fun j=>planted X (weight (d j) (axis j 0)) φ y o
  have list:Q=∑j,M j:=sources X d φ y o
  have covered (j:Alma F):Auth k (M j):=(paid X _ φ y o).tall v.hk
  have transpo (A:Alma F→Era G ℝ)(auth:∀j,Auth (k+k) (A j)):
      reading (cruises X.ax X.tx X.N (k+k) (X.m+X.i) s (∑j,A j)).2 x=
        ∑j,reading (cruises X.ax X.tx X.N (k+k) (X.m+X.i) s (A j)).2 x:=by
    have transfer:=WilsonIndependentCollarWeightedCruise.original X.ax X.tx X.vesselsC.hG X.vesselsC.green
      (before.trans (Nat.le_add_right X.m X.i)) (X.hc.trans X.hn) univ (fun _=>1) A (fun j _=>auth j)
    simp only [one_smul] at transfer
    rw [transfer]
    apply PowerSeries.ext
    intro j
    simp [WilsonOlderFreshSoftSocketKinetic.reading,Prod.snd_sum,Finset.sum_apply]
  have row (j:Alma F):=WilsonIndependentFittedMixedReturn.multiplied X s before P prior (d j) (axis j 0) φ y o r x
  constructor
  · change reading (cruises _ _ _ _ _ _ ((left P) Q)).2 x=_
    rw [list,map_sum]
    exact (transpo (fun j=>(left P) (M j)) (fun j=>prior.manor (covered j))).trans
      (sum_congr rfl fun j _=>(row j).1)
  · change reading (cruises _ _ _ _ _ _ ((right P) Q)).2 x=_
    rw [list,map_sum]
    exact (transpo (fun j=>(right P) (M j)) (fun j=>(covered j).manor prior)).trans
      (sum_congr rfl fun j _=>(row j).2)

end YM.Integration.WilsonIndependentFittedPivotRoster
