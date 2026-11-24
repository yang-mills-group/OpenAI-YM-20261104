import YM.MSbar.Pole.Feynman.Progress
import YM.Gauge.Colors
/-! # d-dimensional Yang-Mills propagator and vertex alphabet

Field weights are 4-dimensional mass weights, with measure convention absorbing change
of units for insertions. Gauge parameter Feynman, ghost-anterior pairing positive.
Retain formal auxiliary commuting imaginary multiplier with quadratic term `-b·b/2`;
no positive-measure assertion. Antifield legs uncontracted.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Book
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Feynman District
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

inductive Kind | vector | multiplier | ghost | antighost deriving DecidableEq
namespace Kind
def rank : Kind → ℕ | vector => 1 | _=>0
def degree : Kind → ℤ | multiplier=>2 | _=>1
def number : Kind→ℤ|ghost=>1|antighost=>-1|_=>0
end Kind
/-- Source weights/reality and field types. Composite source momenta enter
exactly like ordinary momenta on its ordered legs. -/
inductive Tag (G:Gauge)
| quantum (k:Kind)(c:G.ColorIndex)
| bv (k:Kind)(c:G.ColorIndex)
| source (d rank:ℕ) (ghostNumber:ℤ)

variable {G:Gauge}
namespace Tag
def rank : Tag G→ℕ| quantum k _=>k.rank| bv k _=>k.rank|source _ r _=>r
def degree:Tag G→ℤ | quantum k _=>k.degree|bv k _=>3-k.degree|source d _ _=>4-d
def number : Tag G→ℤ | quantum k _=> k.number | bv k _=> -1-k.number | source _ _ c=> c
def Odd (f:Tag G): Prop:= _root_.Odd f.number

variable {I:Type}
/-- Pairing coefficient, after removing common `1/p²` scalar, with kinetic weights
already rescaled. Along-going ordered momentum convention (`X` first). No choice even
on evanescent components. -/
def line (X Y : Tag G): (Fin X.rank→I)→(Fin Y.rank→I)→Option (Chain I × ℂ):=
  match X,Y with
  | .quantum .ghost a,.quantum .antighost b => fun _ _=>if a=b then some (.scalar,1) else none
  | .quantum .antighost a,.quantum .ghost b => fun _ _=> if a=b then some (.scalar,-1) else none
  | .quantum .vector a,.quantum .vector b => fun f g=> if a=b then some (.pair (f (0:Fin 1)) (g (0:Fin 1)),1) else none
  | .quantum .vector a,.quantum .multiplier b=>fun f _=>if a=b then some (.query (f (0:Fin 1)),-Complex.I) else none
  | .quantum .multiplier a,.quantum .vector b=>fun _ g=>if a=b then some (.query (g (0:Fin 1)),Complex.I) else none
  | _,_=> fun _ _=> none

lemma uses {X Y:Tag G} {f:Fin X.rank→I}{g:Fin Y.rank→I} {p:Chain I × ℂ} (hx: ∀ i j,f i≠g j)(h:line X Y f g=some p):
    p.1.usable ∧ p.1.reads=(Finset.univ.image f ∪ Finset.univ.image g) ∧ X.degree+Y.degree=2+(p.1.demand:ℤ):=by
  unfold line at h; split at h
  · split_ifs at h with hh; cases h; simp [rank,Kind.rank,Chain.usable,Chain.reads,degree,Kind.degree,Chain.demand]
  · split_ifs at h with hh; cases h; simp [rank,Kind.rank,Chain.usable,Chain.reads,degree,Kind.degree,Chain.demand]
  · split_ifs at h with hh; cases h; simp [rank,Kind.rank,Chain.usable,Chain.reads,degree,Kind.degree,Chain.demand]; apply hx
  · split_ifs at h with hh; cases h; simp [rank,Kind.rank,Chain.usable,Chain.reads,degree,Kind.degree,Chain.demand]
  · split_ifs at h with hh; cases h; simp [rank,Kind.rank,Chain.usable,Chain.reads,degree,Kind.degree,Chain.demand]
  · simp at h
end Tag
end YM.MSbar.Pole.Book
