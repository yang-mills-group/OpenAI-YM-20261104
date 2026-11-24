import YM.RegulatorIR.Cluster.Cross
import YM.RegulatorIR.Diagram.Equations

/-! Finite chart scores for the polynomials arising in first joins. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open MvPolynomial Function Finset Budget Budget.Packet Diagram Diagram.Interval Diagram.Formal
open scoped Topology BigOperators Classical Polynomial PowerSeries
variable {I:Type}{m n:ℕ}

abbrev Rhythm (I:Type):= ℕ → Orders I
def Root (T V:Rhythm I)(K:Layer I I) : Rhythm I:=fun k e r=> heating K (T k e) r + drift K T V k e r
def metron (T:Rhythm I) : Rhythm I:= fun k e=> (k+1:ℝ) • T (k+1) e

variable [Fintype I]
structure Reads (m:ℕ)(V:Rhythm I)(f:EPS I) : Prop where
 ranks k e : Within (e+m) (V k e)
 align k : gradedSymmetric (V k)
 score k e : (PowerSeries.coeff e f).coeff k= packed (V k e) (e+m)

namespace Reads
variable {T S:Rhythm I}{f g:EPS I}
lemma extracts {V:Rhythm I}(t n :ℕ)(h:∀ e k r,V k e r≠0 → 2*k+r ≤3*e+t)(hp:∀ k e,Within (e+n) (V k e))(hh:∀ k,gradedSymmetric (V k)) : Reads n V (desert (fun e=>3*e+t) (fun e=>e+n) V):= by
 refine ⟨hp,hh,fun k e=>?_⟩
 unfold desert; rw [PowerSeries.coeff_mk,Polynomial.finsetSum_coeff]; by_cases he:k ≤ 3*e+t
 · simp [Polynomial.coeff_monomial,he]
 have hm : ¬ k<3*e+t+1:=by omega
 have hx : ∀ r,V k e r=0:= fun r=> Classical.byContradiction (fun hg=> by have := h e k r hg;omega)
 simp [Polynomial.coeff_monomial,hm,hx,packed]
lemma many (h:Reads m T f)(hh:Reads m S g): Reads m (fun k e=> T k e+S k e) (f+g):=by
 refine ⟨?_,fun k e r=>symmetric_add (h.align k e r) (hh.align k e r), ?_⟩
 · intro k e r hr
   by_contra! hv; apply hr; rw [Pi.add_apply, show T k e r=0 from by by_contra! hm; exact not_lt.mpr (h.ranks _ _ _ hm) hv, show S k e r=0 from by by_contra! hm; exact not_lt.mpr (hh.ranks _ _ _ hm) hv, zero_add]
 intro k e; rw [map_add,Polynomial.coeff_add, h.score,hh.score,pack_add]
lemma more (h:Reads m T f)(he:m≤n): Reads n T f:=⟨fun k e r hr=> le_trans (h.ranks k e r hr) (by omega),h.align,fun k e=>Eq.trans (h.score k e) (pack_extends (h.ranks k e) (by omega))⟩
lemma specifies (h:Reads m T f)(hh:Reads m S f): T=S := by
 ext1 k; ext1 e; ext1 r; by_cases he:r≤e+m
 · apply Diagram.identified _ _ (h.align k e r) (hh.align k e r)
   have ht:= (h.score k e).symm.trans (hh.score k e)
   rw [← Diagram.isolate (T k e) (Finset.mem_range.mpr (show r<e+m+1 by omega)),← Diagram.isolate (S k e) (Finset.mem_range.mpr (show r<e+m+1 by omega))]; exact congr_arg _ ht
 rw [show T k e r=0 from by by_contra! hp;exact he (h.ranks _ _ _ hp), show S k e r=0 from by by_contra! hv;exact he (hh.ranks _ _ _ hv)]
lemma composition (h:Reads m T f)(hh:Reads n S g): Reads (m+n) (composeT T S) (f*g):=by
 refine ⟨fun k e=> compose_shape T S h.ranks hh.ranks k e, fun k=> compose_sym T S k, ?_⟩
 intro k e; rw [PowerSeries.coeff_mul,Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_mul]; rw [Finset.sum_comm (s:=Finset.antidiagonal e)]
 rw [compose_order,pack_sum]; apply Finset.sum_congr rfl;intro a _;rw [accord_order, pack_sum]; apply Finset.sum_congr rfl; intro b hb
 have hu:=Finset.mem_antidiagonal.mp hb; rw [h.score,hh.score,← crisp_packed _ _ (h.ranks _ _) (hh.ranks _ _)]; congr 1; omega
lemma velocity (h:Reads m T f): Reads m (metron T) (farther (clock (Jet I)) f):=by
 refine ⟨?_,fun k e r=> symmetric_scale (h.align (k+1) e r) _,?_⟩
 · intro k e r hr; exact h.ranks (k+1) e r (fun h'=> hr (by rw [metron,Pi.smul_apply,h',smul_zero]))
 intro k e; unfold metron; rw [farther_v,clock_v,h.score, pack_smul];simp [mul_comm]
lemma thermal (h:Reads m T f) (K:Layer I I): Reads m (fun k e=>heating K (T k e)) ((2:ℝ)⁻¹ • sweepF K f):=by
 refine ⟨fun k e r hr=> le_trans (Nat.le_add_right r 2) (h.ranks k e (r+2) (heating_comes hr)),fun k _ _=> heating_sym K (T k _),?_⟩
 intro k e; rw [PowerSeries.coeff_smul,Polynomial.coeff_smul,pack_multiplicity K (h.ranks k e) (h.align k e),sweepF_v, sweepN_v,h.score]; exact Algebra.smul_def ..
lemma twist (h:Reads m T f)(hh:Reads n S g)(K:Layer I I): Reads (m+n) (drift K T S) (meetF K f g):=by
 refine ⟨fun k e r hr=>?_,fun k e r=> drift_sym K T S k e r,?_⟩
 · obtain ⟨i,j,p,q,a,b,hI,hP,hA,hT,hS⟩:= joins_come hr; have := h.ranks _ _ _ hT;have:= hh.ranks _ _ _ hS;omega
 intro k e; rw [meetF_v]; rw [show drift K T S k e=∑ p∈antidiagonal k,carry K (T p.1) (S p.2) e by ext1; simp [drift,Finset.sum_apply], pack_sum]
 apply Finset.sum_congr rfl;intro x _;rw [show carry K (T x.1) (S x.2) e=∑ p∈antidiagonal e,force K (T x.1 p.1) (S x.2 p.2) by ext1; simp [carry,Finset.sum_apply],pack_sum]; apply Finset.sum_congr rfl; intro p hp
 have H:=h.ranks x.1 p.1; have H':= hh.ranks x.2 p.2
 rw [h.score,hh.score,
   pack_extends (m:=p.1+m+1) H (by omega),pack_extends (m:=p.2+n+1) H' (by omega), ← pack_force]
 · congr 1; have :=Finset.mem_antidiagonal.mp hp; omega
 · exact fun r hr=> le_trans (H r hr) (by omega)
 · exact fun r hr=> le_trans (H' r hr) (by omega)
 · exact h.align x.1 p.1
 exact hh.align x.2 p.2

def thermalR (K:Layer I I)(f g:EPS I): EPS I:=(2:ℝ)⁻¹ • sweepF K f + meetF K f g
lemma transport (h:Reads m T f)(hh:Reads n S g)(K:Layer I I): Reads (m+n) (Root T S K) (thermalR K f g):= many ((thermal h K).more (by omega)) (twist h hh K)
end Reads
end YM.RegulatorIR.Cluster
