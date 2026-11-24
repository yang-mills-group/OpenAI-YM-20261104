import YM.FormalOPE.RG10.Transit.Merits
import YM.FormalOPE.RG10.Transit.Stability

/-!
# Reach a soft-cell identity readout in the finite-horizon scheme

Here zero-field report, prior to extracting the external terminal full-Wilson regulator's version.
Use with flow to older stop including terminal-to-normalized cover ratio identification by RG09
hypotheses. It's just the internal formal pre-log correlation evaluated at zero fields, still from
one independently prescribed Wilson scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function Voyage
open scoped Topology BigOperators Classical
variable {U J : ℕ → Type} {X : Type} [∀ i, Fintype (J i)]
    (V : Voyage U J) (W : Scale X U) (A : Lens W.tape) {j k t N : ℕ}

def rate (r : ℕ) (u : Series) := ∑ i∈range (r+1), ‖coeff i u‖
@[simp] lemma rate_zero (r) : rate r 0=0:=by simp [rate]
lemma rate_nn (u : Series) (r): 0≤ rate r u:=sum_nonneg fun _ _=>norm_nonneg _
lemma in_rate (u : Series) {r i:ℕ} (h:i ≤ r) : ‖coeff i u‖ ≤ rate r u := single_le_sum (f:=fun i=>‖coeff i u‖) (fun _ _ => norm_nonneg _) (mem_range.mpr (by omega))
lemma rate_add (u v:Series) (r) : rate r (u+v) ≤ rate r u + rate r v := by
  unfold rate; rw [← sum_add_distrib]; refine sum_le_sum fun i _=> ?_; rw [map_add]; exact norm_add_le ..
lemma rate_sub (u v:Series)(r):rate r (u-v)≤rate r u+rate r v:= by unfold rate; rw [← sum_add_distrib]; refine sum_le_sum fun i _ => ?_; rw [map_sub]; exact norm_sub_le ..
lemma rate_mul (u v : Series) (r : ℕ): rate r (u*v) ≤ rate r u*rate r v := by
  unfold rate; rw [Finset.sum_mul_sum]
  let f (i:ℕ×ℕ):= ‖coeff i.1 u‖*‖coeff i.2 v‖
  apply le_trans _ (triangle_le r f (fun i=> mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  apply Finset.sum_le_sum; intro i _; rw [coeff_mul]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; exact norm_mul_le ..

def void (I:Type) : Channel I →+* Series := PowerSeries.map MvPolynomial.constantCoeff
lemma first {I:Type} (p:Channel I) (i:ℕ) : coeff i (void I p)= MvPolynomial.coeff 0 (coeff i p):=by rw [void,coeff_map]; rfl
lemma void_cost {I: Type} (p:Channel I) (w : I→ℝ) (hw: 0 ≤ w) (n r:ℕ) :
    rate r (void I p) ≤ mag w n r p := by
  apply Finset.sum_le_sum; intro i _; rw [first];
  let P:= coeff i p; change ‖MvPolynomial.coeff 0 P‖≤ _
  by_cases h:0 ∈ P.support
  · apply le_trans (b:=fare w n 0 *‖MvPolynomial.coeff 0 P‖) _ (single_le_sum (s:=P.support) (f:= fun l=>fare w n l * ‖MvPolynomial.coeff l P‖) (fun j _=>mul_nonneg (fare_pos _ hw n j).le (norm_nonneg _)) h)
    rw [fare_nothing,one_mul]
  rw [MvPolynomial.notMem_support_iff.mp h, norm_zero]; exact worth_nonneg _ hw _ _

/-- Stop theorem as operator cost on *single invariant series* with all available probes. Widens
Hours to include arbitrarily many eligible older steps when this cost bound on those stated
lengths. -/
def Fence (V : Voyage U J) (W : Scale X U) (A : Lens W.tape) (F : ∀ i,Subring (Channel (U i))) (r n d s t : ℕ) (Q:ℝ) :=
   ∀ x ∈ F t, Guard x r d → W.value s n r A (V.yield s t x) ≤ Q* W.value t n r A x

def echo (k N : ℕ) : Channel (U N) →+ Series := (void (U k)).toAddMonoidHom.comp (V.yield k N)
lemma reflects {F} (hk:k ≤ t) (h:t ≤ N) (P:Channel (U N)) {Q:ℝ} (r d n : ℕ) (g: Fence V W A F r n d k t Q)
    (he:Guard (V.yield t N P) r d) (hp: V.yield t N P ∈ F t) : rate r (echo V k N P) ≤ Q*W.value t n r A (V.yield t N P) := by
  change rate r (void (U k) (V.yield k N P)) ≤ _; rw (occs:=.pos [1]) [V.follows hk h]; exact (void_cost _ _ (W.alive _ _) n r).trans (g _ hp he)
end YM.FormalOPE.RG10.Transit
