import YM.Integration.WilsonIndependentMatchedLowerAtSix
import YM.WilsonCoeffUV.Product.Report.Census
import YM.WilsonCoeffUV.Product.Connected.Charges

/-! Submit the complete stable difference as a literal located cover pupil.
Its short-distance gain is charged once in the native two-field budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverProfile
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}
  {p:h<D}{v:Rails h k u e}{E W K U:Credit}

def word (P:TowerS G D)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ):Era G ℝ:=
  locale o (pupil l P φ x y)

def charge (φ:Rarity D)(u l:ℕ)(x y A B:ℝ):ℝ:=BasePrice l φ x y*(9^u*(B*A))

abbrev Income (P:Era G ℝ)(k e u:ℕ)(h:ProfileW)(A:ℝ):Prop :=
  Auth k P ∧ ∀ δ:ℝ, 0≤δ→PaidMer e u h P P A δ

/-- A trial with its own positive-radius test and all angular ranks, including
rank zero. The two pupils may have different centers and supports. -/
theorem submitted (P:TowerS G D)(hp:On k P)(A:ℝ)
    (bill:∀j≤e,∀r,Fruit 0 1 u (P.2 j r) A)
    (φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(S:Patch)(hx:0<x)(hx':x≤1)
    {B:ℝ}(hf:Amplitude φ B):
    Income (word P φ x y o l) k e u (OrbP S φ x y o) (charge φ u l x y A B) := by
  refine ⟨locale_val _ (placed l φ hp x y) o,?_⟩
  intro δ hd
  exact orbFunds P P φ x y o u hx hx' hf S
    (fun j hj r=>YieldP.same (bill j hj r) hd) hd l

def price (L:CutsP H T p v E W K U)(C:Credit)(i:ℕ)(a:ℝ):ℝ:=
 |a| *(C.buy L.Age * Real.exp (-(L.vesselsC.draws.S.scale L.ceilC -
   L.vesselsC.draws.S.scale (L.m+i))/4)*L.fuel)

/-- Native cover income for the complete propagated source minus its fitted
Shrine. The scalar comes from the same normalized transfer. -/
theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃ C:Credit,∀ (L:CutsP H T p v E W K U) (i:ℕ) (_:i≤L.i) (a:ℝ)
      (φ:Rarity D) (x y:ℝ)(o:CellR)(l:ℕ)(S:Patch) (_:0<x) (_:x≤1)
      (B:ℝ) (_:Amplitude φ B),
      Income (word (a • L.springP i) φ x y o l) k e u (OrbP S φ x y o)
        (charge φ u l x y (price L C i a) B) := by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  refine ⟨C,?_⟩
  intro L i hi a φ x y o l S hx hx' B hf
  exact submitted (a • L.springP i) ((L.onward hi).μ a) _
    (fun j hj r=>( (paid L).2.2 j hj i hi r).μ a) φ x y o l S hx hx' hf

/-- Both admitted cover sources enter the genuine graded ordinary product. -/
theorem occupied {P Q:Era G ℝ}{i j:ℕ}{a b:ProfileW}{A B:ℝ}
    (left:Income P i e u a A)(right:Income Q j e u b B):
    Income (agateV P Q) (i+j) e u (a⊓b) (coinMat (i+j) e*A*B) := by
  refine ⟨left.1.manor right.1,fun δ hd=>?_⟩
  exact procureT left.1 left.1 right.1 right.1
    ((left.2 δ hd).grade inf_le_left le_rfl) ((right.2 δ hd).grade inf_le_right le_rfl) hd le_rfl

end YM.Integration.WilsonIndependentMatchedCoverProfile
