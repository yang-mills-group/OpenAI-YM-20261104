import YM.Integration.WilsonPointChildFiniteWard
import YM.Integration.WilsonMarkedFiniteIndependentHistory

/-! Gauge transport of every finite marked face through the whole original Wick log. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedOriginalGaugeLaw
open Function Filter Lattice RG Wilson Precision FormalBulk08.Series FormalBulk08.Jets
open FormalBulk08.Reef FormalBulk08.Flat FormalBulk08.Shore FormalBulk08.Wine
open FormalBulk08 FormalBulk08.Orb FormalBulk08.Lava FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Next.Free Stationary Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι→ℕ}{n:Side}

/-- A genuine group gauge germ may be tested separately in each nonempty face
or in its full moment polynomial. The empty face retains its normalization. -/
theorem equation {M L:Sac ι (Pap (wire G n))}(h:Equation M L):
    (∀S,Rite (M S) (M S) 1 0) ↔ (∀S,Rite (L S) (L S) 1 0):=by
  constructor
  · intro ward S U inst a b g ha hb ca cb gauge constant localEq
    let A:=Wick.roam ℝ (motor a)
    let B:=Wick.roam ℝ (motor b)
    have same:A ∘ M=B ∘ M:=funext fun J=>ward J U a b g ha hb ca cb gauge constant localEq
    have old:=h.mapKin A
    rw [same] at old
    exact congrFun (Equation.unique _ _ _ old (h.mapKin B)) S
  · intro ward S U inst a b g ha hb ca cb gauge constant localEq
    let A:=Wick.roam ℝ (motor a)
    let B:=Wick.roam ℝ (motor b)
    have same:A ∘ L=B ∘ L:=funext fun J=>ward J U a b g ha hb ca cb gauge constant localEq
    have old:=h.mapKin A
    rw [same] at old
    exact congrFun (Equation.prod_u _ _ _ old (h.mapKin B)) S

def Valid (X:family G D):Prop:=∀(n:Side)(A:Case D)(S:Finset ι),Rite (readO A (X S) n) (readO A (X S) n) 1 0

/-- The signed connected response of the finite measured transfer commutes with
all analytic gauge changes. The retained upper quiet action is the genuine finite
story at that age. -/
theorem filed (R:Run G)(u:G.ColorIndex)(tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit){N j:ℕ}(live:j<N)
    {K:family G D}(auth:Eu k K)(empty:K ∅=0)(old:Valid K):
    Valid (logO R.family.path.levels R.metals.O j N K k):=by
  let V:=R.family.path.levels
  let M:=edV V R.metals.O j N K k
  have legal:=vol V R.metals.O j N K k live simple R.alloy.B.ratio auth
  have vacuum:=edV_e V R.metals.O j N K k live simple R.alloy.B.ratio
  intro n A
  apply (equation (levels_log M legal vacuum A n)).mp
  intro S
  let fine:=n*(destination V N j).patch.L
  let Y:=levelsO K S
  have entered:=placedO K auth S
  have move:=Mer.ply_verse V live simple R.alloy.B.ratio entered (touch A S)
  have prior:=(equation (levels_exp K auth empty A fine)).mpr (old fine A) S
  have heard:=WilsonMarkedFiniteIndependentStep.original R u tags simple v paid N j (mass k S) live
    (tuftV (touch A S) Y) (entered.tuft _) n
  have ward:=WilsonPointChildFiniteWard.step R u tags simple v paid live n
    ((tuftV (touch A S) Y).1 fine) prior 1
  simp only [one_smul] at ward
  change Rite (flash ((tuftV (touch A S) (verseI V R.metals.O j N (mass k S) Y)).1 n))
    (flash ((tuftV (touch A S) (verseI V R.metals.O j N (mass k S) Y)).1 n)) 1 0
  rw [move,heard]
  exact ward

end YM.Integration.WilsonMarkedOriginalGaugeLaw
