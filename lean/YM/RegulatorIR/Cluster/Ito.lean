import YM.RegulatorIR.Cluster.Rhythm

/-! Leibniz with direct forcing. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Finset MvPolynomial Function Budget Budget.Packet Diagram Diagram.Interval Diagram.Formal Reads
open scoped Topology BigOperators Classical
variable {I:Type}{a b c:ℕ}

structure Brief (a:ℕ)(T:Rhythm I) : Prop where
 ranks k e : Within (e+a) (T k e)
 times : ∃ t,∀ k e r,T k e r≠0→ 2*k+r ≤3*e+t
 align : ∀ k e r, IsSym (T k e r)

lemma timeVac {K:Layer I I}(V:Orders I) (h:Vacuum V)(hp:gradedSymmetric V) (b:Bool) : Brief 2 (logHeat K V b):= ⟨fun k e r he=> (heated_cap K V h b e r k he).2.1,⟨0,fun k e r hh=> by have := (heated_cap K V h b e r k hh).2.2;omega⟩,fun k=> heatedSym K hp b k⟩
lemma timeMark (K:Layer I I)(V F:Orders I)(h:Vacuum V)(hs:∀ e,Within (e+a) (F e))(hf:gradedSymmetric F)(b:Bool): Brief a (markHeat K (logHeat K V b) F):= ⟨fun k e r he=>(marked_cap a K V h F hs b e r k he).1,⟨a,fun k e r he=>(marked_cap a K V h F hs b e r k he).2⟩, fun k=>markedSym K _ hf k⟩

variable [Fintype I]
namespace Reads
private lemma heaten (K:Layer I I)(h:∀ i j,K i j=K j i)(f g :EPS I):
    (2:ℝ)⁻¹ • sweepF K (f*g) = ((2:ℝ)⁻¹ • sweepF K f) * g + f*((2:ℝ)⁻¹ • sweepF K g) + meetF K f g:=by
 have hh (i j:I): vane i (vane j (f*g))= vane i (vane j f)*g + f*vane i (vane j g)+(vane i f *vane j g+ vane j f *vane i g):=by simp_rw [Derivation.leibniz,smul_eq_mul,map_add,Derivation.leibniz,smul_eq_mul]; ring
 have ht : (∑ i:I,∑ j:I,K i j • (vane j f *vane i g))=meetF K f g:=by rw [sum_comm];exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by rw [h j i]
 simp_rw [sweepF, hh,smul_add,sum_add_distrib,ht,smul_add]
 let H:= meetF K f g
 change _+((2:ℝ)⁻¹ • H+(2:ℝ)⁻¹ • H)=_
 rw [show ((2:ℝ)⁻¹ • H + (2:ℝ)⁻¹ • H)= H by rw [← add_smul,show ((2:ℝ)⁻¹)+(2:ℝ)⁻¹=1 by norm_num, one_smul]]
 apply congr_arg (·+meetF K f g)
 apply congr_arg₂
 · rw [smul_mul_assoc]; simp_rw [Finset.sum_mul,smul_mul_assoc]
 rw [mul_smul_comm]; simp_rw [Finset.mul_sum,mul_smul_comm]
private lemma meets (K:Layer I I)(f g v:EPS I): meetF K (f*g) v= meetF K f v*g+f*meetF K g v:=by
 have ht (i j:I): vane i (f*g)*vane j v = vane i f *vane j v*g+f*(vane i g *vane j v):=by rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]; ring
 simp_rw [meetF,ht,smul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,mul_smul_comm,smul_mul_assoc]
lemma roots_mul (K:Layer I I)(h:∀ i j,K i j=K j i)(f g v:EPS I): thermalR K (f*g) v = thermalR K f v * g + f*thermalR K g v+meetF K f g:=by rw [thermalR,thermalR,thermalR, heaten K h, meets]; ring
end Reads
namespace Brief
lemma readable {T:Rhythm I}(h:Brief a T):∃ f, Reads a T f:= by obtain ⟨t,hv⟩:=h.times; exact ⟨_,Reads.extracts t a (fun e k=>hv k e) h.ranks h.align⟩
lemma pace {T U:Rhythm I}(h:Brief a T)(hh:Brief b U) : metron (composeT T U)=composeT (metron T) U+composeT T (metron U):=by
 obtain ⟨f,H⟩:= h.readable; obtain ⟨g,M⟩:=hh.readable
 have ht := velocity (composition H M)
 rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,mul_comm g, add_comm (f * _)] at ht
 exact specifies ht (many (composition (velocity H) M) (composition H (velocity M)))
lemma ito {K:Layer I I} (hK:∀ i j,K i j=K j i) {T U V:Rhythm I}(h:Brief a T)(hh:Brief b U)(hx: Brief c V) : Root (composeT T U) V K=composeT (Root T V K) U+composeT T (Root U V K)+ drift K T U:=by
 obtain ⟨f,H⟩:= h.readable; obtain ⟨g,Q⟩:= hh.readable; obtain ⟨v,E⟩:= hx.readable
 have ht:= transport (composition H Q) E K
 rw [roots_mul _ hK] at ht
 exact specifies ht (many (many (more (composition (transport H E K) Q) (by omega)) (more (composition H (transport Q E K)) (by omega))) (more (twist H Q K) (by omega)))
end Brief
end YM.RegulatorIR.Cluster
