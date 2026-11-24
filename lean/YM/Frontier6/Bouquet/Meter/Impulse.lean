import YM.Frontier6.Bouquet.Patron.Gentry

/-!
# Finite regulator kernels and forest terms

No hypothesis on *size* of the local delta-jet coefficients. They will be set
 in the recurring scheme by exact finite moments (in particular no treating
 absolute estimates on them as sufficient when the regulator is removed).
 Allow arbitrary payments in these algebra and fixed-regulator lemmas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V:Type}{G:Gauge}{L:Register G}
structure Issue (S: Table L) (p:Pod) where
   Code: Type
   [FT : Fintype Code]
   payment : Code→ S.Tag -- vector and maximum input grade (all output use a pure suit)
   course : Code→ Multiset Room
   sits : ∀ i,∀ x∈course i,x∈ normal p
attribute [instance] Issue.FT
abbrev Teller (S:Table L):= (p:Pod)→ Issue S p
variable {C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R:Ensemble}
abbrev Trip (P:Ensemble) := ∀ p:P,(A p.val).Code
def togetherS (p: Trip A P) (x:Seats P) (i:P): Spelling S:= let u:= (A i.val).payment (p i); Tale.suit K (x i) u.fst u.snd
def costsD (p:Trip A P) : Multiset Room:= ∑ i:P,(A i.val).course (p i)
lemma courses_in (p:Trip A P)(u:Room)(he:u∈ costsD A p) : u∈ fiber P:=by
    unfold costsD at he
    obtain ⟨i,_,hi⟩:= Multiset.mem_sum.mp he; exact home_sub i.property ((A i.val).sits (p i) _ hi) -- test
-- one common neighborhood factor multiplies the test before any normal jets read.
variable (h:P≤Q)
variable {Y:Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
def ink (x: Seats Q)(H:Patron S Q Y)(p:Trip A P) (f:Full (fiber Q))(z:Margin Q P) := train (fiber Q) (costsD A p) (T.film Q P f) (insideCL loft_le z) • convey h H (togetherS K A p (transit h x z)) -- use qualified film

def essay (x: Seats Q)(H:Patron S Q Y)(p:Trip A P) (f:Full (fiber Q)) := ∫ z:Margin Q P, ink K A T h x H p f z
def branch (x:Seats Q)(H: Patron S Q Y) (f:Full (fiber Q)) := ∑ p:Trip A P,essay K A T h x H p f
-- full regulated expression. Coordinate independent sheaf (proved below)
def regulator (x:Seats P)(H:Patron S P Y)(f:Full (fiber P)):Y:=∑ y:Down P, branch K A T y.property x H f
-- individual $ink$ equality for restrictions nested through any proper clearance
-- $δ$ factors isolate branches; no assertion about growth of $δ$ coefficients here
end YM.Frontier6.Bouquet
