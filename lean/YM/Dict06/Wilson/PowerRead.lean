import YM.Dict06.Wilson.Reclose
import YM.Dict06.Wilson.HGroup
/-! π S = I for the lattice FieldSystem, as a projected,
normalized series, at each finite horizon and coupling order. Distinguish
engineering/slot projection of the *initial* operators from the Wick
projections used after vacuum evolution. No regulator limits in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Wil
open PowerSeries Function Set Filter Series Lattice Wilson Labels Source Source.Drops
open scoped BigOperators ContDiff Matrix.Norms.Frobenius Topology Classical
variable {G : Gauge}{d:ℕ}{F:Frame G d} (H:Hol G)(S:SectionData F)

def widen (A : Panel S.stencil G) : Links ℤ G.Color := fun e=>
  if he : e.1∈S.stencil ∧ e.1+step e.2 ∈S.stencil then A ⟨e,he⟩ else 0
lemma restrict_inverse (A : Panel S.stencil G): restrictLog S.stencil (widen S A)= A := funext fun i=> dif_pos i.property
-- projected coefficient of the link-rank-e kernel: logTest on all
-- positive edges IN the stencil only. Pose presentations need no new paths
-- on output. (To include a ν-address at the root replace d by the allowed
-- field portion of the announced horizon.)
def placedKernel (p:F.Coeff) (e:ℕ) (q:Snap G d) :=
  coeff e (book S p (widen S (logTest H d S.stencil q)))
lemma placed_terms (p:F.Coeff) (e:ℕ) : placedKernel H S p e = term (echo S p) e ∘ logTest H d S.stencil := by
  funext q; rw [placedKernel,reported,restrict_inverse]; rfl

def packet (p:F.Coeff) (rank m l:ℕ)(J:Jet G) : ℂ := probe (placedKernel H S p rank) m l J

set_option maxHeartbeats 460000 in
lemma all_packets (p:F.Coeff)(m l:ℕ)(J:Jet G):
    probe (snapped H S p) m l J=∑ rank∈Finset.range (l+1), packet H S p rank m l J:=by
  unfold packet probe snapped; simp_rw [placed_terms]
  let L:=logTest H d S.stencil
  let T(rank) := term (term (echo S p) rank ∘ L) l
  change ordinary m (term (echo S p ∘ L) l ∘ engineered J) = ∑ rank∈Finset.range (l+1), ordinary m (T rank ∘ engineered J)
  have he q : term (echo S p ∘ L) l q = ∑ rank∈Finset.range (l+1), T rank q:= Series.comp _ _ l ((chart_of_links H d S.stencil).1.of_le le_top) ((echo_smooth S p).contDiffAt.of_le le_top) (chart_of_links H d S.stencil).2 _
  have hz (rank:ℕ) : ContDiff ℝ m (T rank ∘ engineered J):= (Tensor.diag_smooth _ _).comp ((engineered_diff _).of_le le_top)
  rw [show (term (echo S p ∘ L) l ∘ engineered J)=(fun y=> ∑ rank ∈ Finset.range (l+1),(T rank ∘ engineered J) y) from funext fun y=>he (engineered J y)]; exact ordinary_sum _ (fun rank=>T rank ∘ engineered J) m (fun rank _=> (hz rank).contDiffAt)

lemma packet_late (p:F.Coeff) (rank m l:ℕ)(J:Jet G)(hl:l<rank): packet H S p rank m l J=0:=by
  unfold packet probe; rw [placed_terms, show term (echo S p) rank = Tensor.diagonal (Tensor.coeff (echo S p) rank 0) from rfl,early (Tensor.coeff (echo S p) rank 0) hl ((chart_of_links H d S.stencil).1.of_le le_top) (chart_of_links H d S.stencil).2]; exact Eq.trans (ordinary_const 0 _) (ite_self ..)
lemma packet_unraised (p:F.Coeff) (m l:ℕ)(J:Jet G) : packet H S p l m l J =
    ordinary m (fun t=> coeff l (book S p (access (engineered (d:=d) J t)))):=by
  unfold packet probe; rw [placed_terms, show term (echo S p) l = Tensor.diagonal (Tensor.coeff (echo S p) l 0) from rfl, funext (first_hit (Tensor.coeff (echo S p) l 0) ((chart_of_links H d S.stencil).1.of_le le_top) (chart_of_links H d S.stencil).2)]; simp_rw [Function.comp_def,reported]; congr 1; funext t
  apply congrArg (Tensor.diagonal _) (funext fun i=>log_first ..)

variable (hs:S.Sound H)(hp:Bid.pop S)
omit hs
include hp in
lemma packet_early (i:F.Index) (n m l:ℕ)(hn:n<(F.grades i).2)(J:Jet G) : packet H S (Pi.single i 1) n m l J=0:=by
  unfold packet probe; rw [show placedKernel H S (Pi.single i 1) n=fun _=>0 from funext fun q=>no_lower S hp i n hn _,term,Tensor.coeff_zero]
  exact (ordinary_const 0 _).trans (ite_self ..)

/-- Sum all rank packets through M before calling this the projected leg.
When l≤M, the use of the lower-rank moments at *positive* coupling orders
is essential. -/
def collect (c:F.Coeff)(M m l:ℕ)(J:Jet G) := ∑ rank ∈ Finset.range (M+1), packet H S c rank m l J
lemma collects (c:F.Coeff)(M m l:ℕ)(h:l≤M)(J:Jet G):
    collect H S c M m l J = probe (snapped H S c) m l J := by
  rw [all_packets]; symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1)); intro b _ he
  apply packet_late; simpa using he -- not membership => ≥ l+1

/-- Coefficient rule from coupling powers:
    (1) initial column i rank `rank` from the ordered exponential
    carries g^(rank-l_i), no negative powers (no_lower called in the
    powered kernel; the definition here uses its equivalence to book);
    (2) substituting g^-1 log Hol removes g^rank;
    (3) output radial projection to `(m,l)` restores g^l.
 Thus compare order b exactly when l=l_i+b. When l<l_i,
 no term survives since rank≤l by packet_late and rank<l_i
 vanishes. We include all book ranks through l_i+r at once (input order r).
-/
def kjet (i:F.Index)(r b m l:ℕ)(J:Jet G):ℂ:=
    if l=(F.grades i).2+b then collect H S (Pi.single i 1) ((F.grades i).2+r) m l J else 0
include hs
/-- Tested with arbitrary real radial data, coefficientwise identity
through any fixed finite order r. pop used separately in projection ledger
for no negative powers and in `power_bundle` to justify that these are exactly
the input ranks present in Powered letter.
-/
theorem kjet_exact (i:F.Index)(r b m l:ℕ)(hb:b≤r)(hm:m≤d)(hl:l≤d)(J:Jet G):
    kjet H S i r b m l J=(if b=0 ∧ (m,l)=F.grades i then read J (F.basis i).val else 0) := by
  by_cases h : l=(F.grades i).2+b
  · rw [kjet,if_pos h, collects H S _ _ _ _ (by omega), projecting H S hs i hm hl]
    cases e : F.grades i with
    | mk α β =>
      simp only [e] at *; split_ifs with hv hj he
      all_goals first | rfl | simp_all
  rw [kjet,if_neg h,if_neg]; contrapose! h; simp_all; exact congrArg Prod.snd h.2

include hp
omit hs in
lemma no_negative (i:F.Index)(M m l:ℕ)(he:l<(F.grades i).2)(J:Jet G) : collect H S (Pi.single i 1) M m l J=0:=by
  unfold collect; apply Finset.sum_eq_zero; intro n _; by_cases ha : n<(F.grades i).2
  · exact packet_early H S hp i _ _ _ ha J
  exact packet_late H S _ _ _ _ _ (by omega)

theorem power_bundle (i:F.Index)(r m l:ℕ)(J:Jet G)(hm:m≤d)(hl:l≤d) :
    (∀ A:Links ℤ G.Color, letter S i A * PowerSeries.X^(F.grades i).2 = book S (Pi.single i 1) A ∧
       ∀ e≤r, coeff e (letter S i A) = Tensor.diagonal (author S (Pi.single i 1) ((F.grades i).2+e)) (restrictLog S.stencil A)) ∧
    (∀ b ≤ r, kjet H S i r b m l J = if b=0 ∧ (m,l)=F.grades i then read J (F.basis i).val else 0) ∧
    (l<(F.grades i).2 → collect H S (Pi.single i 1) ((F.grades i).2+r) m l J=0):=
  ⟨fun A=> ⟨powered_letter S hp i A,fun e _=>by rw [leg_at,reported]⟩,
   fun b hb=>kjet_exact H S hs i r b m l hb hm hl J, fun he=>no_negative H S hp i _ m l he J⟩
end YM.Dict06.Wil
