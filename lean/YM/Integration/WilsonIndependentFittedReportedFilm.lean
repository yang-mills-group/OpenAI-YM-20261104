import YM.Integration.WilsonIndependentFittedRelativeClock
import YM.Integration.WilsonIndependentMatchedPivotSeat
import YM.Integration.WilsonOlderFreshSoftSocketDeposit
import YM.WilsonCoeffUV.Root.UV.RingNaturality

/-! Scalar series on a reported pivot pass through the actual pupil and profile
on every auxiliary board, with the full inverse kinetic clock of that column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedReportedFilm
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (printed)
open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedPivotSeat (axis film)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}
variable {V Z:Type}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup Z][NormedSpace ℝ Z]

def funded (c:Cost)(P:Era G V):Era G V:=(fun n=>affix c (P.1 n),affix c P.2)
def weight (c:Cost)(d:Verse F):Verse F:=fun i=>c*d i

theorem written (A:Levels G)(O:ChartRatio G)(N m i:ℕ)(c:Cost)(d:Verse F):
    steep A O T p N m i (weight c d)=weight (reel (relativeC A O N m i) c) (steep A O T p N m i d):=by
  funext j
  let M:=bindingS A O T p N m i false
  let τ:=reel (relativeC A O N m i)
  change τ (∑b,M j b*(c*d b))=τ c*τ (∑b,M j b*d b)
  rw [map_sum,map_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro s _
  simp only [map_mul]
  ring

theorem whole (P:Island F D)(c:Cost)(d:Verse F):
    Shrine P (weight c d)=funded c (Shrine P d):=by
  refine Prod.ext (funext fun n=>?_) ?_
  · simp only [Shrine,Prod.fst_sum,Stem,funded,Finset.sum_apply,weight,affix_sum,affix_mul]
  · simp only [Shrine,Prod.snd_sum,Stem,funded,weight,affix_sum,affix_mul]

theorem probed (t:V→L[ℝ]Z)(c:Cost)(P:Era G V):tuftV t (funded c P)=funded c (tuftV t P):=
  Prod.ext (funext fun n=>WilsonOlderFreshSoftSocketDeposit.mapped t.toLinearMap c (P.1 n))
    (WilsonOlderFreshSoftSocketDeposit.mapped t.toLinearMap c P.2)

private lemma moved {B U:Type}[AddGroup B](o:B)(c:Cost)(P:Pal V (B×U)):
    skewV o (affix c P)=affix c (skewV o P):=by
  funext j r z
  simp only [skewV,revolve,affix,Finset.sum_apply,Pi.smul_apply]

theorem planted (P:TowerS G D)(φ:Rarity D)(x y:ℝ)(c:Cost)(b:Cover):
    shoe (funded c P) φ x y b=funded c (shoe P φ x y b):=by
  unfold shoe
  rw [probed]
  exact Prod.ext (funext fun n=>moved (wrap n b) c _) (moved b c _)

theorem enrol {ι:Type}(I:Finset ι)(a:ι→ℝ)(B:ι→Era G V)(c:Cost):
    (∑j∈I,a j • funded c (B j))=funded c (∑j∈I,a j • B j):=by
  refine Prod.ext (funext fun n=>?_) ?_
  · simp only [Prod.fst_sum,Prod.smul_fst,Pi.smul_apply,Finset.sum_apply,funded,affix_sum,affix_μ]
  · simp only [Prod.snd_sum,Prod.smul_snd,funded,affix_sum,affix_μ]

theorem pupil_paid (P:TowerS G D)(φ:Rarity D)(x y:ℝ)(c:Cost):
    pupil h (funded c P) φ x y=funded c (pupil h P φ x y):=by
  unfold pupil
  simp only [planted]
  exact enrol .. 

theorem drawn (X:CutsP H T p v E W K U)(φ:Rarity D)(y:ℝ)(o:CellR)
    (d:Verse F)(c:Cost)(i:ℕ):
    printed X.vesselsC (sectionSeal T p) φ (weight c d) X.m X.N y o i=
      funded (reel (relativeC X.ax X.tx X.N X.m i) c)
        (printed X.vesselsC (sectionSeal T p) φ d X.m X.N y o i):=by
  let P:=Peaks X.ax X.tx T p X.N (X.m+i)
  let t:=paceT X.ax.S X.m (X.m+i)
  let read:=fun w:Verse F=>tuftV (century o)
    (pupil h (Shrine P (steep X.ax X.tx T p X.N X.m (X.m+i-X.m) w)) φ t y)
  change read (weight c d)=funded _ (read d)
  dsimp only [read]
  rw [Nat.add_sub_cancel_left,written,whole,pupil_paid,probed]

theorem original (X:CutsP H T p v E W K U)(φ:Rarity D)(y:ℝ)(o:CellR)
    (j:Alma F)(q:ℕ)(c:Cost)(i:ℕ):
    printed X.vesselsC (sectionSeal T p) φ (weight c (axis j q)) X.m X.N y o i=
      funded (reel (relativeC X.ax X.tx X.N X.m i) c) (film X j q φ y o i):=
  drawn X φ y o (axis j q) c i

end YM.Integration.WilsonIndependentFittedReportedFilm
