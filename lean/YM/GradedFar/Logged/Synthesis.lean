import YM.GradedFar.Logged.Subtable

/-!
# Pay heterogeneous log costs for transformations of these basis estimates
Using each *actual projection* exactly once on all these layouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Synthesis
open Function Filter Finset Set Spec Table Extraction Orbits MeasureTheory
open scoped Topology Classical BigOperators ContDiff
open Economy (Paint)
open Seats Stroke Fork Deck Trace
variable {I J L:Type} [Fintype I][Fintype J]
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {d:I→ℕ}{e:J→ℕ}
local notation "Q"=>F.sector.derivatives
open Subtable
abbrev Samples (K:Economy.Small L) (r:L→ℝ) (d:I→ℕ)(x:L→Labels S d) :=
    ∀ i (j:ℕ), j≤ d i → Paint K (fun s=> r s^j) (fun s=> R.cutTest j (d i) (x s i))
section
variable {K:Economy.Small L}{r:L→ℝ} {t:I→ℝ} (Y:L→ℝ) (hr:∀ᶠ i in K.p, 0 < r i)

-- one array
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E]
abbrev Mlm (S:Table C.book) (d:I→ℕ)(E: Type) [NormedAddCommGroup E] [NormedSpace ℂ E]:= MultilinearMap ℂ (fun i=> S.Field (d i)) E
variable {x:L→Labels S d}
include hr
theorem array (A:(d:I→ℕ)→ L→ Mlm S d E)
    (Z:L→Labels S d) (hZ:Samples F R K r d Z)
    (hF:∀ (e:I→ℕ) (h:e≤d), ∀ᶠ i in K.p, ∀ v:Labels S e, A d i (current F h v)=A e i v)
    (hw:∀ (e:I→ℕ), e≤d→ ∀ w:Labels S e, Paint K (fun i=>Y i/(r i)^(∑ j, e j)) (fun i=>A e i w)) :
    Paint K Y (fun i=> A d i (Z i)) := by
    let J:=(j:I)→ Fin (d j+1); let n (p:J) j:=(p j).val
    let X (p:J) i : Labels S (n p) :=fun j=> R.cutTest (n p j) (d j) (Z i j)
    let v j (k:Fin (d j+1)) i:=R.cutTest k.val (d j) (Z i j)
    have ht (p:J) : n p ≤ d:= fun j=> Nat.le_of_lt_succ (p j).isLt
    have h i : A d i (Z i)= ∑ p:J, A d i (current F (ht p) (X p i)) := by
      rw [show Z i = fun j=> ∑ k:Fin (d j+1), F.sector.derivatives.rise (d:=k.val) (Nat.le_of_lt_succ k.isLt) (v j k i) from funext (fun j=> Trace.rise_cut F R (d j) (Z i j))]
      exact MultilinearMap.map_sum ..
    simp_rw [h]; apply Paint.sum; intro p _
    have hp:=Paint.contract (P:=fun i=>Y i/(r i)^(∑ j, n p j)) (fun i=>A (n p) i) (hw _ (ht p)) (fun j i=> r i^(n p j)) (X p) (fun j=>hZ j _ (ht p j))
    exact (hp.eases (U:=Y) (hr.mono (fun i h=> by rw [prod_pow_eq_pow_sum, mul_div_cancel₀ (Y i) (pow_pos h _).ne']))).assists ((hF (n p) (ht p)).mono (fun i h=>(h _).symm))
-- two-stage expansions without mixing captures. Keep *the same x and y fields/labels*.
abbrev Span (S:Table C.book) (d:I→ℕ) (e:J→ℕ) (E:Type)[NormedAddCommGroup E][NormedSpace ℂ E]:= Mlm S (Sum.elim d e) E
omit hr
private lemma legsF (A : Span S d e E) (x:Labels S d) (y:Labels S e) :
    A.currySum x y = A (stages x y) := by rw [MultilinearMap.currySum_apply]; congr 1; funext i; cases i<;>rfl
variable (D:Pitch L)
theorem combine (A:(d:I→ℕ)→(e:J→ℕ)→ L→ Span S d e E)
    (Z:L→Labels S d)(X:L→Labels S e) (hZ:Samples F R D.toSmall D.r d Z) (hX: Samples F R D.toSmall D.s e X)
    (hA:∀ (d':I→ℕ)(hd:d'≤d), ∀ᶠ i in D.p, ∀ v:Labels S d', ∀ u:Labels S e,
        A d e i (stages (current F hd v) u)=A d' e i (stages v u))
    (hB:∀ (d':I→ℕ)(e':J→ℕ), d'≤d →∀(he:e'≤e),∀ᶠ i in D.p,∀ v:Labels S d', ∀ u:Labels S e',
        A d' e i (stages v (current F he u))=A d' e' i (stages v u))
    (paid:∀ d' e',d'≤d→ e'≤e→∀ v:Labels S d',∀ u:Labels S e',
        Paint D.toSmall (fun i=>Y i/(Deck.Rnow D d' e' i)) (fun i=>A d' e' i (stages v u))) :
    Paint D.toSmall Y (fun i=>A d e i (stages (Z i) (X i))) := by
    let M (d':I→ℕ) i : Mlm S d' E := sectionLabels (d:=Sum.elim d' e) (X i) (A d' e i)
    have he k v i:M k i v=A k e i (stages v (X i)) := sectionLabels_apply ..
    have earned d' (hd:d'≤d) v : Paint D.toSmall (fun i=> Y i/(D.r i)^(∑ j,d' j)) (fun i=>M d' i v) := by
       simp_rw [he]; let B (e':J→ℕ) i : Mlm S e' E := (A d' e' i).currySum v
       have h e' i u : B e' i u=A d' e' i (stages v u):= legsF (A d' e' i) v u
       simp_rw [← h]; refine array F R (fun i=> Y i/(D.r i)^(∑ j,d' j)) (r:=D.s) (K:=D.toSmall) D.outer.positive B X hX ?_ ?_
       · intro e' he'; simp_rw [h]; exact (hB _ _ hd he').mono fun i h u=> h v u
       intro e' hi w; simp_rw [h, div_div]; exact paid d' e' hd hi v w
    simp_rw [← he d]; exact array F R Y D.toSmall.positive M Z hZ (fun d' hd=> (hA _ hd).mono (fun i hq v=> by rw [he,he]; exact hq v _)) earned

end
end YM.OPE.Logged.Synthesis
