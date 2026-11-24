import YM.Integration.WilsonThermometerUnitFilingWeakPair

/-! A covariance joining a vacuum vertex to a marked source. Sum the translated endpoint on the genuine periodic covariance before charging its row, keeping the marked root. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakSpoke
open Function Finset Lattice Laurent Bloch Precision RG Next.Free Work.F08 FormalBulk08 Flat Stationary
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {I J:Type*}

theorem moved (A:Bloch.Row I J){s c B:ℝ}(paid:A.strip s c)(bp:0 ≤ B)
    (n:Side)(x:Site n)(i:I)(j:J)(F:Site n→ℝ)
    (test:∀z:Cover,‖F (x+wrap n z)‖ ≤ Real.exp (s*size z)*B):
    |∑y:Site n,A.acts n (x,i) (y,j)*F y| ≤ c*B:=by
  let lift (d:Cover):=Real.exp (s*size d)*‖A i j d‖*B
  have h:=paid i j
  have sums:Summable lift:=h.2.1.mul_right B
  let piece (y:Site n)(d:Cover):=(if y=x+wrap n d then A i j d else 0)*F y
  have hinge (y:Site n)(d:Cover):‖piece y d‖ ≤ lift d:=by
    by_cases eq:y=x+wrap n d
    · subst y
      simp only [piece,norm_mul,lift]
      calc _ ≤ ‖A i j d‖*(Real.exp (s*size d)*B):=
             mul_le_mul_of_nonneg_left (test d) (norm_nonneg _)
           _ = _:=by ring
    · simp only [piece,if_neg eq,zero_mul,norm_zero,lift]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) bp
  have sm (y:Site n):Summable (piece y):=(sums.of_nonneg_of_le (fun d=>norm_nonneg (piece y d)) (hinge y)).of_norm
  have expan:(∑y:Site n,A.acts n (x,i) (y,j)*F y)=∑' d:Cover,A i j d*F (x+wrap n d):=by
    calc _ = ∑y:Site n,∑'d:Cover,piece y d:=by
             apply sum_congr rfl;intro y _
             change (∑' d:Cover,if y=x+wrap n d then A i j d else 0)*F y=_
             rw [←tsum_mul_right]
         _ = _:=by
           rw [←Summable.tsum_finsetSum (fun y _=>sm y)]
           apply tsum_congr;intro d
           simp [piece,ite_mul]
  rw [expan,←Real.norm_eq_abs]
  have high (d:Cover):‖A i j d*F (x+wrap n d)‖ ≤ lift d:=by
    simpa [piece] using hinge (x+wrap n d) d
  have sm':=sums.of_nonneg_of_le (fun d=>norm_nonneg (A i j d*F (x+wrap n d))) high
  exact (norm_tsum_le_tsum_norm sm').trans ((sm'.tsum_le_tsum high sums).trans
    (by simpa only [lift,tsum_mul_right] using mul_le_mul_of_nonneg_right h.2.2 bp))

theorem absolute (A:Bloch.Row I J){s c B:ℝ}(paid:A.strip s c)(bp:0 ≤ B)
    (n:Side)(x:Site n)(i:I)(j:J)(F:Site n→ℝ)(fp:∀y,0 ≤ F y)
    (test:∀z:Cover,F (x+wrap n z) ≤ Real.exp (s*size z)*B):
    ∑y:Site n,|A.acts n (x,i) (y,j)| * F y ≤ c*B:=by
  let signed (y:Site n):=if 0 ≤ A.acts n (x,i) (y,j) then F y else -F y
  have sig (y:Site n):A.acts n (x,i) (y,j)*signed y=|A.acts n (x,i) (y,j)| * F y:=by
    unfold signed;split <;> rename_i h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h),mul_neg,neg_mul]
  have salary (z:Cover):‖signed (x+wrap n z)‖ ≤ Real.exp (s*size z)*B:=by
    unfold signed;split <;> simpa only [norm_neg,Real.norm_eq_abs,abs_of_nonneg (fp _)] using test z
  exact (by simpa only [sig] using (le_abs_self _).trans (moved A paid bp n x i j signed salary))

variable {G:Gauge}(R:Run G) (fund:WilsonOriginalCompoundLodge.Filed R.kit)(i:ℕ)(ht:4 ≤ R.alloy.B.a.clock.J i)

include fund ht in
theorem original :
    let L:=R.alloy.B.a
    let K:=R.metals.p.kernel
    let X:Patch:=(L.clock.op i 0).patch
    let s:=(WilsonThermometerUnitFilingWeakRoom.book G K X.J (L.clock.J i)).width
    ∀F:Lodge X,∃c:ℝ,0<c ∧ c ≤ Borough.ageZ (L.clock.hatBeta i) ∧
      ∀N M:ℕ,i<N → N ≤ M → ∀h:X.Branches K G,∀n:Side,
        let P:=destination L N i
        let A:=Flat.gamma G K P F h
        ∀x:Site n,∀ a b,∀ B:ℝ,0 ≤ B → ∀f:Site n→ℝ,(∀y,0 ≤ f y) →
          (∀d:Cover,f (x+wrap n d) ≤ Real.exp (s*size d)*B) →
            ∑y:Site n,|A.acts n (x,a) (y,b)| * f y ≤ c*B:=by
  intro L K X s F
  obtain ⟨c,cp,cc,all⟩:=WilsonOriginalCompoundLodge.figure R fund i ht F
  refine ⟨c,cp,cc,?_⟩
  intro N M iN NM h n P A x a b B bp f fp tab
  exact absolute A (all N M iN NM h).1 bp n x a b f fp tab

end YM.Integration.WilsonThermometerUnitFilingWeakSpoke
