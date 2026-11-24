import YM.AllOrder.Floe.Leases
import YM.AllOrder.Ink.Broil
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M J U₀ E₀:ℕ} {a C D b:ℝ}
namespace Money
open Method
variable {V:Type} {Λ:V→ℝ}{Ad:Side→Prop} {U : ℕ→ℕ→V→Bills α}
variable {T:V→ℝ}{A:V→Stalk α α}
def chant (a:ℝ)(N:ℕ) : ℕ→ℝ
 | 0=>a
 | i+1=>chant a N i/(N+3:ℕ)
def song (S:ℕ) : ℕ →ℕ
 | 0=> S
 | i+1=>2*song S i +12
lemma soprano (N:ℕ)(h:0<a)(k:ℕ):0<chant a N k:= by induction k with | zero=>exact h | succ i ih=> exact div_pos ih (by positivity)
lemma gestate (N:ℕ)(h:0<a): Antitone (chant a N):= antitone_nat_of_succ_le fun i=> div_le_self (soprano N h i).le (by exact_mod_cast (show 1≤N+3 by omega))
lemma gesture (S:ℕ): Monotone (song S):= monotone_nat_of_le_succ fun i=> by change _ ≤ 2*song S i+12; omega -- unfolding both?
variable (hn:Code Ad A U)(hp:CreditF Λ 0 T)(ha:0<a)(hh:∀ v,Belt (A v) a (T v)) (l:ℕ)(hr:∀ i≤N,License Ad Λ (U i 0) a (i+2) l)
local notation "H"=>License Ad Λ
include N hn hp ha hr hh
lemma aqua (i:ℕ)(he:k≤N):License Ad Λ (U k i) (chant a N i) (k+2) (song l i):= by
 induction i using Nat.strong_induction_on generalizing k with
 | h i ih=>
    rcases i with _|i; · exact hr k he
    have h0:= soprano N ha (i+1)
    rcases i with _|i; · apply License.adapt (License.null Λ h0); intro v n hv; rw [hn.one k v n hv]; rfl
    let b':= chant a N (i+1+1); let D i:= chant a N i; let c:= song l i; let C i:= song l i
    have hx(k r:ℕ)(h:k≤N)(hg:r≤ i): License Ad Λ (U k r) (D (i+1)) (k+2) c:= (ih r (by omega) h).squeeze (gestate N ha (by omega)) le_rfl (gesture _ hg)
    have hv v:= Belt.debt (hh v) (gestate N ha (show 0≤ i+1 by omega)) le_rfl
    let f(i₀ j₀:ℕ)(v:V)(n:Side):= spark (A v) (U (k-i₀) (i-j₀) v n) (U i₀ j₀ v n); let f' v n:=flicker (A v) n (U k i v n)
    have hu:∀ k':ℕ,k'≤ k →∀ j≤ i,License Ad Λ (f k' j) b' (k+2) (C (i+1+1)):= by
       intro k' he' j hj; refine (License.join hp (soprano N ha (i+1)) hv (hx _ (i-j) (by omega) (by omega)) (hx k' j (he'.trans he) hj) h0 ?_).squeeze le_rfl (by omega) (by unfold c C; simp only [song]; omega); -- unfold cb. bound width
       refine (mul_le_mul_of_nonneg_left (show (↑(k'+2+1):ℝ)≤(N+3:ℕ) from (by exact_mod_cast (show k'+2+1 ≤ N+3 by omega))) h0.le).trans_eq ?_; apply div_mul_cancel₀; positivity -- definitional
    have hU:License Ad Λ f' b' (k+2) (C (i+1+1)):= (License.furnish hp (soprano N ha (i+1)) hv (hx k i he le_rfl)).squeeze (gestate N ha (by omega)) (by omega) (by unfold c C; simp only [song]; omega)
    refine License.adapt ((License.add (License.pile (F:=fun k v n=>∑ j∈range (i+1), f k j v n) (range (k+1)) (fun k' hk=> License.pile (range (i+1)) (f k') (fun j hj=>hu k' (Nat.le_of_lt_succ (mem_range.mp hk)) j (Nat.le_of_lt_succ (mem_range.mp hj))) h0) h0) hU h0).scale ((↑(i+2:ℕ):ℝ)⁻¹)) (fun v n he=> (hn.pact k i v n he).symm)
lemma peakward (he:k ≤ N) : License Ad Λ (snapshot U k) (chant a N (3*k)) (k+2) (song l (3*k)):= License.pile _ (U k) (fun j hj=>(aqua hn hp ha hh l hr j he).squeeze (gestate N ha (Nat.le_of_lt_succ (mem_range.mp hj))) le_rfl (gesture l (Nat.le_of_lt_succ (mem_range.mp hj)))) (soprano _ ha _)
end Money
end YM.AllOrder.Ink
