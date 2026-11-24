import YM.MSbar.Pole.Book.Mon

/-!
# Diagram scheme interacting term table

Vertices in `I`, the Euclidean action minus the free (Feynman) quadratic including free
Batalin-Vilkovisky data. Thus `-I` is used in the formal weight. Only commuting compact
color data come from Gauge. Dot tensors on open polarization slots; all itertools include
unprojected ghost and antifield counterterm calculations. This module defines the
convention; gauge/identity assertions must be theorems separately. No analytic or even
finite-dimensional Berezin integral asserted.
-/
noncomputable section
namespace YM.MSbar.Pole.Book.Action
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Feynman District Kind Tag
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "cIdx" => G.ColorIndex

/-- $f_{abc}$ using exactly the color basis orthonormal for trace normalization in G. -/
def spin (a b c:cIdx):ℂ:= ((inner ℝ (EuclideanSpace.basisFun cIdx ℝ a) (G.ad (EuclideanSpace.basisFun cIdx ℝ b) (EuclideanSpace.basisFun cIdx ℝ c)):ℝ):ℂ)

-- define ranks with literal finite numerals for open polarization references
abbrev three (a b c:cIdx): Fin (↑(3:ℕ+))→Tag G:= ![quantum vector a,quantum vector b,quantum vector c]
private abbrev open0 {n:ℕ}{φ:Fin n→Tag G} (p:Fin n) (h:0<(φ p).rank) : Alphabet φ:= Sum.inr ⟨p,⟨0,h⟩⟩
private theorem sigma_test {n:ℕ}{φ:Fin n→Tag G} {P:Dims φ→ Prop} (h:∀ i j,P ⟨i,j⟩):∀ x,P x:=by rintro ⟨i,j⟩; exact h i j
private lemma cards {n:ℕ} {f:Fin n→Tag G} {L: List (Alphabet f)} (hh:L.Nodup) (hl:∀ i:Dims f, Sum.inr i∈L):∀ i : Dims f,L.count (Sum.inr i)=1:= fun i=> List.count_eq_one_of_mem hh (hl i)

def cubic (a b c:cIdx): Atom G:=by
  refine ⟨3,three a b c,1, Complex.I*spin a b c,[ (Sum.inl 0,open0 1 ?_), (open0 0 ?_,open0 2 ?_) ],?_,?_⟩
  · exact (show 0<1 from Nat.one_pos)
  · exact (show 0<1 from Nat.one_pos)
  · exact (show 0<1 from Nat.one_pos)
  · change (∑ i:Fin 3,((three a b c i).degree)) + _ =_
    simp [Fin.sum_univ_succ,tour,Tag.degree,Kind.degree,Kind.rank,three]
  apply cards
  · simp [tour,open0]
  apply sigma_test; intro i; change Fin 3 at i; fin_cases i <;> intro j <;> (change Fin 1 at j) <;> fin_cases j <;> simp [tour,open0]
  · exact .tail _ (.tail _ (.head ..))
  · exact .tail _ (.head ..)
  · exact .tail _ (.tail _ (.tail _ (.head ..)))
private abbrev Quartic (a b c d:cIdx): Fin (↑(4:ℕ+))→Tag G:= ![quantum vector a,quantum vector b,quantum vector c,quantum vector d]
def quartic (a b c d:cIdx): Atom G:=by
  refine ⟨4,Quartic a b c d,2, (∑ i:cIdx, spin i a b * spin i c d)/4,[(open0 0 Nat.one_pos, open0 2 Nat.one_pos), (open0 1 Nat.one_pos, open0 3 Nat.one_pos)],?_,?_⟩
  · change (∑ i:Fin 4,((Quartic a b c d i).degree)) + _ =_
    norm_num [Fin.sum_univ_succ,tour,Tag.degree,Kind.degree,Quartic,open0]
  apply cards
  · simp [tour,open0]
  apply sigma_test; intro i; change Fin 4 at i; fin_cases i <;> intro j
  · change Fin 1 at j; fin_cases j; exact .head ..
  · change Fin 1 at j; fin_cases j; exact .tail _ (.tail _ (.head ..))
  · change Fin 1 at j; fin_cases j; exact .tail _ (.head ..)
  · change Fin 1 at j; fin_cases j; exact .tail _ (.tail _ (.tail _ (.head ..)))

private abbrev Fade (a b c:cIdx): Fin (↑(3:ℕ+))→Tag G:= ![quantum antighost a,quantum vector b,quantum ghost c]
def fade (a b c:cIdx): Atom G:=by
  refine ⟨3,Fade a b c,1, Complex.I*spin a b c,[(Sum.inl 0, open0 1 Nat.one_pos)],?_,?_⟩
  · change (∑ i:Fin 3,((Fade a b c i).degree)) + _ =_
    norm_num [Fin.sum_univ_succ,tour,Tag.degree,Kind.degree,Fade,open0]
  apply cards
  · simp [tour,open0]
  apply sigma_test; intro i; change Fin 3 at i; fin_cases i <;> intro j
  · change Fin 0 at j; exact Fin.elim0 j
  · change Fin 1 at j; fin_cases j; exact .tail _ (.head ..)
  · change Fin 0 at j; exact Fin.elim0 j

private abbrev Stara (a b c:cIdx): Fin (↑(3:ℕ+))→Tag G:= ![bv vector a,quantum vector b,quantum ghost c]
def starA (a b c:cIdx): Atom G:=by
  refine ⟨3,Stara a b c,1, spin a b c,[(open0 0 Nat.one_pos, open0 1 Nat.one_pos)],?_,?_⟩
  · change (∑ i:Fin 3,((Stara a b c i).degree)) + _ =_
    norm_num [Fin.sum_univ_succ,tour,Tag.degree,Kind.degree,Stara,open0]
  apply cards
  · simp [tour,open0]
  apply sigma_test; intro i; change Fin 3 at i; fin_cases i <;> intro j
  · change Fin 1 at j; fin_cases j; exact .head ..
  · change Fin 1 at j; fin_cases j; exact .tail _ (.head ..)
  · change Fin 0 at j; exact Fin.elim0 j

private abbrev Starg (a b c:cIdx): Fin (↑(3:ℕ+))→Tag G:= ![bv ghost a,quantum ghost b,quantum ghost c]
def starG (a b c:cIdx): Atom G:=by
  refine ⟨3,Starg a b c,1, spin a b c / 2,[],?_,?_⟩
  · change (∑ i:Fin 3,((Starg a b c i).degree)) + _ =_
    norm_num [Fin.sum_univ_succ,tour,Tag.degree,Kind.degree,Starg,open0]
  apply cards
  · simp [tour,open0]
  apply sigma_test; intro i; change Fin 3 at i; fin_cases i <;> intro j
  · change Fin 0 at j; exact Fin.elim0 j
  · change Fin 0 at j; exact Fin.elim0 j
  · change Fin 0 at j; exact Fin.elim0 j

/-- Enumerate including multiplicities. Together with multiplier quadratic, Feynman
term/principal source signs in manuscript. -/
def interaction (G:Gauge) : List (Atom G) := (Finset.univ : Finset (G.ColorIndex×G.ColorIndex×G.ColorIndex)).toList.flatMap
  fun ⟨a,b,c⟩=> [cubic a b c,fade a b c,starA a b c,starG a b c] ++ ((Finset.univ:Finset G.ColorIndex).toList.map (quartic a b c))
end YM.MSbar.Pole.Book.Action
