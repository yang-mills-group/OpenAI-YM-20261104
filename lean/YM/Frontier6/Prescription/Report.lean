import YM.Frontier6.Normal.Law
import YM.Frontier6.Exact.Partial

/-!
# Root contact recursion for any arity. Physical detector implementation.

This is the general root operation. It acts on a *punctured reporter*: junk
on invalid patches/probes/tests doesn't matter, but we prove hypotheses on it
on the actual use (implemented for pairs here; further arities separately).
`D` is total actual basis grade. Applied with fixed centroid at 0; translations,
state and unselected readings must be on the same hierarchy. `reach` uses an
*exclusive* horizon z: sums empty for z=0. Thus `span X D` is max(K_I+1,0).
Recall ψ includes any normal Jacobian conventions for X. Before the punctured
product is tested with `area`, no changes except preceding extensions; the
following operator uses dyadic shell summation. No all-orders convergence implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Prescription
open Function Filter Set Spec Wilson Lattice MeasureTheory
open YM.Frontier6.Normal
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) {X: Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable (D:ℕ)(s:ℝ)
/-- Number of exact basis grades eligible for geometric jet subtraction
(including zero when the threshold is nonnegative). -/
def tiers (X:Type*)[AddCommGroup X][Module ℝ X](D:ℕ):ℕ:= D+1-Module.finrank ℝ X
def kilo (X:Type*)[AddCommGroup X][Module ℝ X](D w:ℕ):= D-(Module.finrank ℝ X+w)
theorem active_iff (w:ℕ): w < tiers X D ↔ Module.finrank ℝ X+w ≤ D:=by unfold tiers; omega
/-- Input list readouts of already extended proper cluster (away from
full diagonal); uses full f, though it *must* be punctured for conclusions. -/
abbrev Reporter (X:Type*)[NormedAddCommGroup X][NormedSpace ℝ X] := Full X → Reader K
variable (A:Reporter K X)
def one (α:StateIndex K)(p:Probe S)(f:Full X):= A f α p.length p.exterior p.letter
def row (w:ℕ)(f:Full X): S.Field w:= weight K w (capture K w (A f))
def reach (z:ℕ)(f:Full X)(α:StateIndex K)(n:ℕ)(y:Points n)(v:Fin n→ S.Tag) := ∑ i:Fin z, reading K α 0 y v i (row K A i f)
def tear (z:ℕ)(f:Full X) : Reader K:= fun α n y v=> A f α n y v - reach K A z f α n y v
def discard (z:ℕ)(α:StateIndex K)(p:Probe S) (f:Full X):= tear K A z f α p.length p.exterior p.letter
lemma discard_z (α:StateIndex K)(p:Probe S) (f:Full X): discard K A 0 α p f= one K A α p f:=by simp [discard,tear,reach,one]
lemma discard_hop (z:ℕ)(α:StateIndex K)(p:Probe S)(f:Full X): discard K A (z+1) α p f= discard K A z α p f-p.form K α z (row K A z f):=by
   unfold discard tear reach; rw [Fin.sum_univ_castSucc]; exact sub_add_eq_sub_sub ..
lemma discard_result (z:ℕ)(α:StateIndex K)(p:Probe S) (f:Full X) (he:observable K z (A f)) : discard K A (z+1) α p f= one K A α p f-p.form K α z (capture K z (A f)):=by
   refine congr_arg (one K A α p f - ·) (?_: reach K A (z+1) f α p.length p.exterior p.letter= p.form K α z (capture K z (A f)))
   rw [← weights_span K (capture K z (A f)),map_sum]; unfold reach; refine Finset.sum_congr rfl fun i _=> ?_
   rw [form_rises,capture_lower K he]; rfl

/-- suppress test before passing out an active field, including recursions. -/
def mapped (w:ℕ): Full X→ₗ[ℂ] Full X:= if w<tiers X D then leftOut s (kilo X D w) else LinearMap.id
theorem mapped_true (w:ℕ)(h:w<tiers X D)(f:Full X): mapped D s w f= f - portion s (kilo X D w) f:=by unfold mapped; rw [if_pos h,left_as]
theorem mapped_yes (w:ℕ)(h:w<tiers X D): mapped (X:=X) D s w=leftOut s (kilo X D w):= if_pos h
theorem mapped_false (w:ℕ)(h:tiers X D ≤ w)(f:Full X): mapped D s w f=f:=by unfold mapped; rw [if_neg (not_lt.mpr h)]; rfl
lemma mapped_void (f:Full X)(hv:Void f)(w:ℕ) : mapped D s w f=f:=by unfold mapped; split; exact void_left f hv s _; rfl

/-- Weight coefficients after integration. Later proved to agree exactly with
detecting at a sufficiently high horizon on the extended hierarchy. -/
def yield (w:ℕ)(f:Full X): S.Field w:= Normal.over (row K A w) (mapped D s w f)
def space (z:ℕ)(f:Full X):Reader K:=fun α n y v=> ∑ i:Fin z, reading K α 0 y v i (yield K D s A i f)
def roll (z:ℕ)(f: Full X): Reader K:= fun α n y v=>Normal.over (fun f=> tear K A z f α n y v) f + space K D s A z f α n y v

/-- (omrule) with K_I+1 written as exclusive horizon, fixed measurement at
0. All alternatives tested through independent annular pairings. Uniformity,
convergence and gluing need separate verification. -/
def root : Reporter K X:= roll K D s A (tiers X D)
lemma root_on (α:StateIndex K)(p:Probe S)(f:Full X):
    one K (root K D s A) α p f= Normal.over (discard K A (tiers X D) α p) f + ∑ i:Fin (tiers X D), p.form K α i (Normal.over (row K A i) (f-portion s (kilo X D i) f)):=by
    change _ + _ = _; congr 1; refine Finset.sum_congr rfl fun i _=>?_
    unfold yield; rw [mapped_true D s _ i.isLt]; rfl
lemma growth (z:ℕ)(α:StateIndex K)(p:Probe S)(f:Full X):
    space K D s A (z+1) f α p.length p.exterior p.letter=space K D s A z f α p.length p.exterior p.letter+p.form K α z (yield K D s A z f):=by unfold space; rw [Fin.sum_univ_castSucc]; rfl
end YM.Frontier6.Prescription
