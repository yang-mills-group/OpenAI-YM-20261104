import YM.FormalOPE.RG10.GaugeGear.Shifted
/-!
 # A triangular matrix of row and degree at a fixed normalized step

 No post-step logarithmic costs on same rank and component. Applies in any episode with a
 representation whose Ward-compatible channel carries same transfers ordered by aperture.
 No moment mismatches. Not a comparison measure. Requires exact coupling convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open HStein Route Route.Bulk PowerSeries Finset Function
open MvPolynomial (homogeneousComponent homogeneousComponent_isHomogeneous totalDegree)
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J S:Type} [Fintype J] {X:Tape S} (F:Tier)
local notation "H"=> homogeneousComponent
abbrev Grade := ℕ × ℕ

def items (r d:ℕ):Finset Grade:= range (r+1) ×ˢ range (d+3*r+1)
lemma belongs {x : Grade} {r d:ℕ}: x∈items r d ↔ x.1≤r ∧ x.2 ≤ d+3*r:= by simp [items]
lemma all_piece {P:Packet I}{k:ℕ}(h:totalDegree P ≤ k) : ∑ i∈range (k+1),H i P=P:= Eq.trans (Eq.symm (sum_subset (range_mono (show P.totalDegree+1≤k+1 by omega)) (fun i _ hi=> MvPolynomial.homogeneousComponent_eq_zero _ _ (by simp only [mem_range] at hi; omega)))) (MvPolynomial.sum_homogeneousComponent _)
variable (P:Channel I)
local notation "Y"=> Packet I
/-- Before capture location mixing. -/
def cargo (x: Grade) : Y:= H x.2 (coeff x.1 P)
-- cannot go from a scalar into any other slot

def strictHop (a b:Grade): Prop := 0<a.2 ∧ (a.1<b.1 ∨ (a.1=b.1 ∧ b.2<a.2))
instance : DecidableRel strictHop := fun _ _=> Classical.propDecidable _
variable (e:Episode I B J)
variable {x y:Grade} {r d:ℕ}
/-- All non-strict entries in one triangular estimate are same-rank read or zero. -/
def bench (e:Episode I B J) (x y:Grade)(P:Y) := if x.1 ≤ y.1 then H y.2 (beam e (y.1-x.1) (H x.2 P)) else 0
include P in
lemma manifests (hy:y ∈ items r d)(hp : Guard P r d): cargo (e.floats P) y=
    ∑ i∈ items r d,bench e i y (coeff i.1 P):= by
 unfold cargo items; rw [amounts, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>beam e j (coeff i P)), Finset.sum_product,map_sum]
 let U:=range (d+3*r+1)
 refine Eq.trans (b:=(∑ i∈range (y.1+1), ∑ j∈ U, bench e (i,j) y (coeff i P))) (sum_congr rfl ?_) ?_
 · intro i hi; have hj : i≤y.1:= Nat.le_of_lt_succ (mem_range.mp hi); have hv := hj.trans (belongs.mp hy).1; have he: ∀ j:ℕ, bench e (i,j) y (coeff i P)= H y.2 (beam e (y.1-i) (H j (coeff i P))):=fun _=> if_pos hj
   simp_rw [he]; rw [← map_sum,← map_sum, show (∑ j∈U,H j (coeff i P))= coeff i P from all_piece ((hp i hv).trans (by omega))];
 refine sum_subset (range_mono (show y.1+1≤r+1 by have := (belongs.mp hy).1; omega)) ?_
 intro i hi ht; refine sum_eq_zero (fun j hj=> if_neg (show ¬ i ≤ y.1 from fun h=> ht (mem_range.mpr (by omega))))
lemma vanishes (he :∀ j,(first e j).IsHomogeneous 1)(h : ¬strictHop x y)(hn:x ≠ y) (P₁:Y): bench e x y P₁=0:= by
 by_cases ht:x.1≤y.1
 · rw [bench,if_pos ht];
   by_cases hh:x.2=0
   · rw [hh,MvPolynomial.homogeneousComponent_zero,beam_scalar]; split_ifs with hv <;>try exact map_zero _;
     rw [MvPolynomial.homogeneousComponent_of_mem (n:=0) ((MvPolynomial.mem_homogeneousSubmodule ..).2 (MvPolynomial.isHomogeneous_C ..)), if_neg];
     intro ha; exact hn (Prod.ext (by omega) (by omega))
   have hy : y.1=x.1:= by unfold strictHop at h; omega
   have hw : y.2≠x.2:= fun he=>hn (Prod.ext hy.symm he.symm)
   rw [hy, Nat.sub_self, repeated _ _ he (by unfold strictHop at h; omega) (homogeneousComponent_isHomogeneous _ _), if_neg hw.symm];
 rw [bench,if_neg ht]

/-- Use pairing with normalized step only WHEN $w'` gauge-oriented reps compiled from original
 $A_tr` supply guarantee Ward identity `pass` on the Fk packet. Alternative by changing
 w` on entire input p via identity scheduled BEFORE splitting rows and ranks, to release gauge
 cancellation (including zeroth order). This is NOT equality of transfers assumed at output.
 No randomness/regulator-limit assertion. -/
def orient (w:I→Channel (I⊕B)) : Episode I B J:= { e with spur:=w }
variable (w:I→Channel (I⊕B))
abbrev pass (P : Channel I) (k:ℕ) := Through k (replot e.spur P) (replot w P)
lemma passenger (h : pass e w P r) : Through r (e.floats P) ((orient e w).floats P):= HStein.through_transfer e.joint e.vertices r h
variable {P e F} {p:I→ S} {q:B→S} {M C:ℝ} [Fintype I] [DecidableEq I]
variable (O:Lens X)
local notation "A"=> O.m ∘ p
local notation "B₀"=> O.m ∘ q
variable (hM:Inventory (orient e w) F p q X M r d)
    (hc:Pre (orient e w) (O.m ∘ p) (O.m ∘ q) F C)
include hM hc
lemma spot (hx: x∈items r d)(hy:y∈items r d) (hp:Guard P r d) : F.valueOf B₀ (bench (orient e w) x y (coeff x.1 P)) ≤ if x=y then (2*C)^x.2 * F.valueOf A (cargo P x) else if strictHop x y then M^expansive d r * F.valueOf A (cargo P x) else 0:= by
 split_ifs with hh hs
 · subst x; rw [bench, if_pos (le_refl _), Nat.sub_self]; exact diagonal _ _ (fun i=> O.sign (p i)) (fun i=> O.sign (q i)) hc (homogeneousComponent_isHomogeneous ..) -- order variables inspect
 · have he:= (Integral (H x.2 (coeff x.1 P)) y.2 O hM (i:=x.1) (j:=y.1-x.1) (by have h := (belongs.mp hy).1; unfold strictHop at hs; omega) ((covered_h _ _).trans (hp _ (belongs.mp hx).1))); rw [bench, if_pos (by unfold strictHop at hs; omega)]; exact he
 rw [vanishes _ hc.row hs hh,Tier.zero]

lemma triangular (hy:y∈items r d)(hp:Guard P r d)(hz:pass e w P r): F.valueOf B₀ (cargo (e.floats P) y) ≤
    (2*C)^y.2 * F.valueOf A (cargo P y) + M^expansive d r * ∑ i∈ (items r d).filter (fun x=>strictHop x y), F.valueOf A (cargo P i) := by
 rw [show cargo (e.floats P) y=cargo ((orient e w).floats P) y from congr_arg (H y.2) (passenger P e w hz y.1 (belongs.mp hy).1), manifests _ _ hy hp]
 apply (Tier.many F _ (fun i=> O.sign (q i)) _ _).trans; apply (sum_le_sum (fun i hi=> spot w O hM hc hi hy hp)).trans
 apply le_of_eq; rw [←add_sum_erase _ _ hy]; simp only [ite_true];
 rw [mul_sum, sum_filter]; congr 1; have hh : ¬ strictHop y y:= by unfold strictHop; omega
 rw [← add_sum_erase _ _ hy, if_neg hh, zero_add]; apply sum_congr rfl; intro i hi; rw [if_neg (ne_of_mem_erase hi)]
end YM.FormalOPE.RG10.GaugeGear
