import YM.FormalBulk08.Plait.Plaque

/-! Collect Hessian at loop. Low enough synchronized orders that only one scalar defect remains in the finite period:
 never interpreting that defect as a limiting statement. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Wick Orb Series Jets PowerSeries
open Matrix (of)
open scoped BigOperators Topology Classical Matrix
variable {V I:Type*}[Fintype V][DecidableEq V]
section order2
variable (T : Hull V I)(p:Pap (V⊕I))(h:Solved T p)
def rhoq (A : Matrix V V ℝ): Matrix V V (TypeR I):= MvPolynomial.C.mapMatrix A
def curve (A B : Matrix V V (TypeR I)):= -halve ((rhoq T.saddle.q*B).trace)+ halve (halve ((rhoq T.saddle.q*A*rhoq T.saddle.q*A).trace))
lemma rhoq_read (i j:V): rhoq (I:=I) T.saddle.q i j=MvPolynomial.C (T.saddle.q i j):= by simp [rhoq]
lemma rhoq_ag : (rhoq (I:=I) T.saddle.q)ᵀ=rhoq T.saddle.q:= by ext1 i j; change rhoq T.saddle.q j i=_; simp only [rhoq_read,T.saddle.ok j i]
omit [DecidableEq V] [Fintype V] in lemma charge_half (p:TypeR I)(n:ℕ)(h:p.totalDegree≤n): (halve p).totalDegree≤n:= by
    have he: (halve p)=MvPolynomial.C (1/2:ℝ)*p:= by rw [halve,IsScalarTower.algebraMap_apply ℚ ℝ]; congr; norm_num
    rw [he];exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add]; exact h)
omit [DecidableEq V] [Fintype V] in lemma tally_half (p:TypeR I)(n:ℕ)(h:p.IsHomogeneous n): (halve p).IsHomogeneous n:= by
    have he:(halve p)= MvPolynomial.C (1/2:ℝ)*p:=by rw [halve,IsScalarTower.algebraMap_apply ℚ ℝ]; congr; norm_num
    rw [he];exact h.C_mul _
-- Coin estimates trace homogeneous 2.
lemma beacon (A:Matrix V V (TypeR I))(n:ℕ)(h:∀ i j,(A i j).IsHomogeneous n)(i j): ((rhoq (I:=I) T.saddle.q*A) i j).IsHomogeneous n:= by rw [Matrix.mul_apply]; apply MvPolynomial.IsHomogeneous.sum; intro v _; rw [rhoq_read]; exact (h v j).C_mul _
omit [DecidableEq V] in lemma trace_grade (A:Matrix V V (TypeR I))(n:ℕ)(h:∀ i j,(A i j).IsHomogeneous n): A.trace.IsHomogeneous n:= MvPolynomial.IsHomogeneous.sum _ _ _ fun i _=> h i i
lemma curve_active {A B: Matrix V V (TypeR I)}(h:∀ i j,(A i j).IsHomogeneous 1)(hp:∀ i j,(B i j).IsHomogeneous 2): (curve T A B).IsHomogeneous 2:= by
   refine MvPolynomial.IsHomogeneous.add (tally_half _ _ (trace_grade _ _ (beacon T B 2 hp))).neg (tally_half _ _ (tally_half _ _ ?_))
   rw [Matrix.mul_assoc _ (rhoq T.saddle.q) A]; let X:=rhoq T.saddle.q*A; apply trace_grade; intro i j; change ((X*X) i j).IsHomogeneous _; rw [Matrix.mul_apply]; exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun l _=> (beacon T A _ h i _).mul (beacon T A _ h l _))
variable (A B : Matrix V V (TypeR I))(a b:TypeR I)(W Y:Pairs V I)
include h
lemma mixed_rate (f1:coeff 1 (toInk T p)=MvPolynomial.C a+ (rect A+ W))(f2: coeff 2 (toInk T p)=MvPolynomial.C b+(rect B+Y))(ha:Aᵀ=A)(hw: Rental W 0)(hy: Rental Y 1)(hv:Rental (rect A) 1):
     let Q:=rhoq T.saddle.q
     ∃ (U V : TypeR I), U.totalDegree≤0 ∧ V.totalDegree≤1 ∧
       coeff 1 (out T p) = a -halve ((Q*A).trace)+ U ∧ coeff 2 (out T p)= b+curve T A B + V:= by
    intro Q; let E:= (variation T.saddle I).call
    have hg (X: Pairs V I): E X=moment Q X:=rfl
    let F:=rect A; let r:= E F; let w:=E W; let hQ:= rhoq_ag T
    let χ:= F*W+W*F+W*W; let P:=r*w+w*r+w*w
    let B':= halve ((Q*A*Q*A).trace)
    have he : halve (E ((F+W)*(F+W))) - halve (E (F+W)* E (F+W)) = (halve B') + (halve (E χ) - halve P) := by
       have he: E (F*F)=r*r+B':= square_rep Q A ha hQ
       have hh: E (F+W)*E (F+W)=r*r+P:= by rw [map_add]; unfold P r w;ring -- parse
       rw [show (F+W)*(F+W)=F*F+χ by unfold χ;ring,map_add, he,kilo_plus,kilo_plus,hh,kilo_plus]; abel
    have hw':w.totalDegree≤0:= Rental.moment T.saddle.q hw
    have hF:r.totalDegree≤1:= Rental.moment T.saddle.q hv
    have hx': Rental χ 1:= ((hv.mul hw).add (hw.mul hv)).add ((hw.mul hw).money (by omega))
    have hh:P.totalDegree≤1:= by
       unfold P; refine (MvPolynomial.totalDegree_add ..).trans (max_le ((MvPolynomial.totalDegree_add ..).trans (max_le ?_ ?_)) ?_)
       · exact (MvPolynomial.totalDegree_mul ..).trans (Nat.add_le_add hF hw')
       · exact (MvPolynomial.totalDegree_mul ..).trans (Nat.add_le_add hw' hF)
       exact ((MvPolynomial.totalDegree_mul ..).trans (Nat.add_le_add hw' hw')).trans (by norm_num)
    refine ⟨w,E Y+(halve (E χ)-halve P),hw',?_,?_,?_⟩
    · have h':(-P).totalDegree≤1:= by
         rw [show -P= MvPolynomial.C (-1)* P by simp]; exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact hh)
      rw [sub_eq_add_neg, ←kilo_neg]; exact (MvPolynomial.totalDegree_add ..).trans (max_le (Rental.moment T.saddle.q hy) ((MvPolynomial.totalDegree_add ..).trans (max_le (charge_half _ _ (Rental.moment T.saddle.q hx')) (charge_half _ _ h'))))
    · rw [op_one T p h,op_coeff _ _ 1 (by omega),f1,map_add,map_add]; simp only [Saddle.call,moment_C]; change a+(moment Q (rect A)+w)=_; rw [income_rect Q A hQ];abel
    rw [op_two T p h]; rw [op_coeff _ _ 2 (by omega),op_coeff _ _ 1 (by omega),f2,f1, add_sub_assoc,tilt_drop, he]; simp only [map_add,Saddle.call,moment_C]; change b+(moment Q (rect B)+ E Y)+ (halve B'+(halve (E χ)-halve P)) = b+(-halve _+ halve B') + _;rw [income_rect Q B hQ]; abel
end order2
end YM.FormalBulk08.Plait
