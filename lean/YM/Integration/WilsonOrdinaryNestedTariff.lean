import YM.Integration.WilsonOrdinaryNestedCasting
import YM.Integration.WilsonCenteredNestedSigned
import YM.Integration.WilsonCenteredNestedViewer

/-! Factor the native finitely truncated public program's actual charges into
the telescoped engineering price, local logarithms, and the purchased coupling at each vertex. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedTariff
open Filter Extraction Spec Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree
open WilsonCenteredNestedProgram WilsonCenteredNestedRates WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (F:Final C f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def census (t:Tree) (D:t.Inner→ℕ) : ℝ:=premium F Q t D (fun _=>1) (fun _=>1)

theorem count (t:Tree) (D:t.Inner→ℕ) (s:t.Inner→ℝ) :
    premium F Q t D s (fun _=>1)=census F Q t D := by
  induction t with
  | bud=>rfl
  | fork n f ih=>
    unfold census
    simp only [premium,mul_one]
    congr 1
    apply Finset.prod_congr rfl
    exact fun i _=>ih i _ _

variable {n:ℕ} {p:Fin n→Tree}
local notation "T" => Tree.fork n p

def ratiosLoss (s:(fork n p).Inner→ℝ) (ε:ℝ) := ∏u:(fork n p).Inner,((fork n p).ratios 1 s u)^(-ε)
def logarithms (s:(fork n p).Inner→ℝ) := ∏u:(fork n p).Inner,shell (s u)
def clockSum (s:(fork n p).Inner→ℝ) (g:ℝ→ℝ) (P:ℕ) := ∑u:(fork n p).Inner,|g (s u)|^P
def footprint (v:(fork n p).Leaf→S.Tag) (s:(fork n p).Inner→ℝ) (w:ℕ) := Tree.toll (wages v) 0 w s

def price (v:(fork n p).Leaf→S.Tag) (D:(fork n p).Inner→ℕ) (w:ℕ) (ε:ℝ) (j:ℕ) (B:ℝ)
    (s:(fork n p).Inner→ℝ) (g:ℝ→ℝ) (P:ℕ) :=
  footprint v s w * (ratiosLoss s ε * Tree.nestPrice s D +
    census F Q T D * B^(Fintype.card (fork n p).Inner) * (logarithms s)^j * clockSum s g P)

theorem vertex (s:(fork n p).Inner→ℝ) (v:(fork n p).Leaf→S.Tag) (D:(fork n p).Inner→ℕ) (w j P:ℕ)
    (B:ℝ) (g:ℝ→ℝ) {a:ℝ} (h:(fork n p).Tapered a 1 s) :
    WilsonCenteredNestedPhysical.vertexFee F Q s v D w (wage j B) (fun x=>|g x|^P) =
    footprint v s w*(census F Q T D*B^(Fintype.card (fork n p).Inner)*(logarithms s)^j*clockSum s g P) := by
  have eg:=WilsonOrdinaryNestedEngineering.root (degrees v) s w h
  change s (.inl ())^w*leaves T s (degrees v) (s (.inl ()))=footprint v s w at eg
  unfold WilsonCenteredNestedPhysical.vertexFee
  simp only [wage,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Finset.prod_pow]
  rw [count,←eg]
  dsimp only [clockSum,logarithms]
  ring

theorem bill (s:(fork n p).Inner→ℝ) (v:(fork n p).Leaf→S.Tag) (D:(fork n p).Inner→ℕ) (w j P:ℕ)
    (B ε:ℝ) (g:ℝ→ℝ) {a:ℝ} (h:(fork n p).Tapered a 1 s) :
    Tree.bothToll (wages v) ε w D s +
      WilsonCenteredNestedPhysical.vertexFee F Q s v D w (wage j B) (fun x=>|g x|^P) =
      price F Q v D w ε j B s g P := by
  rw [vertex F Q _ _ _ _ _ _ _ _ h,Tree.bothToll,WilsonOrdinaryNestedEngineering.loss _ _ _ _ h]
  unfold price footprint ratiosLoss
  ring

end YM.Integration.WilsonOrdinaryNestedTariff
