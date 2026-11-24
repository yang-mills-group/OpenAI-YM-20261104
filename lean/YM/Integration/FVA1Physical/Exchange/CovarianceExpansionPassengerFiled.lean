import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPassengerSeats

/-! The registered rank-two contact cancellation is proved coefficient by
coefficient on this regulator. The input is only the zero-momentum tensor
withdrawal already included in the filed affine-null packet certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function Finset Lattice RG Wilson Precision Push.Local
open AnalyticBridge VerifiedReset PhysicalNext.Repeat
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}
local notation "Fld" => Config G n

def contactLeg (p:PlaqAxes):Slot:=⟨[],p⟩
def contactTrim (a:Atom G k):Atom G k:={a with leg:=fun i=>contactLeg (a.leg i).plaq}

theorem contact_shorter (a:Atom G k):(contactTrim a).length≤a.length:=
  sum_le_sum (fun i _=>Nat.le_add_left 4 (a.leg i).walk.length)

def zeroContact (A:ℕ→Atom G 2):Prop:=
  ∀R:PathData G,R.loop=A → ∀i j,HasSum (R.loop_coeff i j) 0

private theorem clear_source (A:ℕ→Atom G 2)(rec:zeroContact A)(W:Fld)(z:Site n):
    HasSum (fun i=>(contactTrim (A i)).unmasked W z) 0:=by
  let R : PathData G:= ⟨fun p i=> ((i:ℝ),contactLeg p), A, fun i=> ⟨fun _=> (A i).leg 0,0⟩, fun i=>⟨fun _=>(A i).leg 0,0⟩⟩
  let f (p:Fin 2→PlaqAxes)(j:Fin 2→G.ColorIndex)(i:ℕ):=R.loop_coeff p j i * ∏ u,(contactLeg (p u)).atSite W z (j u)
  have H p j:HasSum (f p j) 0:=by simpa only [zero_mul] using (rec R rfl p j).mul_right (∏u,(contactLeg (p u)).atSite W z (j u))
  have sum:=hasSum_sum (s:=Finset.univ) (f:=fun p i=>∑j,f p j i) (a:=fun _=>0) (fun p (_:p∈_)=>show HasSum _ _ from by
    simpa only [sum_const_zero] using hasSum_sum (a:=fun _=>0) (s:=Finset.univ) (f:=f p) (fun j _=>H p j))
  rw [sum_const_zero] at sum
  refine sum.congr_fun ?_
  intro i
  let P(j:Fin 2):=((A i).leg j).plaq
  unfold f;rw [Finset.sum_eq_single P]
  · simp only [PathData.loop_coeff,if_pos (show (fun j=>((R.loop i).leg j).plaq)=P from rfl)]
    rfl
  · intro p _ diff;simp only [PathData.loop_coeff,if_neg (show (fun j=>((R.loop i).leg j).plaq)≠p from Ne.symm diff),zero_mul,sum_const_zero]
  simp

theorem contact_cancels (A:ℕ→Atom G k){σ C:ℝ}(sp:0<σ)(pay:SumBudget (fun i=>(A i).budget σ) C)
    (rec:∀h:k=2,zeroContact (h ▸ A))(W:Fld)(z:Site n):
    HasSum (fun i=>contactBody (A i) (contactTrim (A i)) z W) (∑'i,(A i).unmasked W z):=by
  have src:Summable (fun i=>(A i).unmasked W z):=(pay.2.1.mul_right ((2:ℝ)^k)).of_norm_bounded
    (fun i=>((A i).unmasked_bound W z).trans (mul_le_mul_of_nonneg_right ((A i).lower_budget σ sp) (by positivity)))
  by_cases eq:k=2
  · subst k;simpa only [contactBody,if_pos rfl,ite_true,sub_zero] using src.hasSum.sub (clear_source A (rec rfl) W z)
  simpa only [contactBody,if_neg eq] using src.hasSum

/-- A masked physical passenger's actual seats divided by the number of
orientations. Each seat keeps the same union mask and rank-two subtraction. -/
def filedSeat (p:BudgetPoint)(coef:ℝ)(a:Atom G k)(t:Seat n)(U:Fld):ℝ:=
  masked p.threshold (t.spread (contactSupport a (contactTrim a) 0))
    (fun Q=>VerifiedReset.factor*coef*contactBody a (contactTrim a) 0 (t.view Q)) U

def physicalPassenger (A:ℕ→Atom G k)(p:BudgetPoint)(coef:ℝ)(U:Fld):ℝ:=
  ∑'r:Seat n×ℕ,filedSeat p coef (A r.2) r.1 U

def wilsonOrbit (A:ℕ→Atom G k)(U:Fld):ℝ:=
  Patch.average (fun s=>uncut A (pull s 0 U))

theorem actual_passenger_emission (A:ℕ→Atom G k){σ C:ℝ}(sp:0<σ)
    (pay:SumBudget (fun i=>(A i).budget σ) C)(rec:∀h:k=2,zeroContact (h ▸ A))
    (p:BudgetPoint)(coef:ℝ)(U:Fld):
    HasSum (fun r:Seat n×ℕ=>filedSeat p coef (A r.2) r.1 U)
      (coef*wilsonOrbit A U+coef*seatLedger A (fun i=>contactTrim (A i)) p U):=by
  let B:=fun i=>contactTrim (A i)
  let src:=fun r:Seat n×ℕ=>contactBody (A r.2) (B r.2) 0 (r.1.view U)
  let err:=fun r:Seat n×ℕ=>seated p r.1 (A r.2) (B r.2) U
  have hsrc:=ConnectedActivityE6.Raw.finite_start src (fun t:Seat n=>∑'i,(A i).unmasked (t.view U) 0)
    (fun t=>contact_cancels A sp pay rec (t.view U) 0)
  have herr:=ConnectedActivityE6.Raw.finite_start err (fun t:Seat n=>∑'i,seated p t (A i) (B i) U)
    (fun t=>(seated_sums A B sp pay (fun _=>le_rfl) p t U).hasSum)
  have ident(r:Seat n×ℕ):filedSeat p coef (A r.2) r.1 U=(VerifiedReset.factor*coef)*(src r+err r):=by
    let X:=r.1.spread (contactSupport (A r.2) (B r.2) (0:Site n))
    let F:Fld→ℝ:=fun Q=>contactBody (A r.2) (B r.2) 0 (r.1.view Q)
    change masked p.threshold X (fun Q=>VerifiedReset.factor*coef*F Q) U=(VerifiedReset.factor*coef)*(F U+(masked p.threshold X F U-F U))
    by_cases healthy:Healthy p.threshold X U
    · rw [masked_eq _ _ _ _ healthy,masked_eq _ _ _ _ healthy];ring
    rw [masked_ne _ _ _ _ healthy,masked_ne _ _ _ _ healthy];ring
  have same(t:Seat n)(i:ℕ):(A i).unmasked ((Song.splay n t).view U) 0=(A i).unmasked (pull t.1 0 U) t.2:=by
    have e:(Song.splay n t).view U=Lattice.translate t.2 (pull t.1 0 U):=by
      rw [←Lattice.pull_one,pull_pull,mul_one,affine,add_zero];rfl
    rw [e];simp only [Atom.unmasked,Slot.atSite,expand_translate,zero_add]
  have h:=((hsrc.add herr).mul_left (VerifiedReset.factor*coef)).congr_fun (fun r=>ident r)
  have reindex: (∑t:Seat n,∑'i,(A i).unmasked (t.view U) 0)=∑s:Signed,uncut A (pull s 0 U):=by
    rw [←Equiv.sum_comp (Song.splay n) (fun t:Seat n=>∑'i,(A i).unmasked (t.view U) 0),Fintype.sum_prod_type]
    simp only [same,uncut]
  rw [reindex] at h
  have calcprice:(VerifiedReset.factor*coef)*((∑s:Signed,uncut A (pull s 0 U))+(∑t:Seat n,∑'i,seated p t (A i) (B i) U))=coef*wilsonOrbit A U+coef*seatLedger A B p U:=by
    unfold wilsonOrbit Patch.average seatLedger VerifiedReset.factor;ring
  rw [calcprice] at h;exact h

theorem physical_passenger_price (A:ℕ→Atom G k){σ C:ℝ}(sp:0<σ)
    (pay:SumBudget (fun i=>(A i).budget σ) C)(rec:∀h:k=2,zeroContact (h ▸ A))
    (p:BudgetPoint)(coef:ℝ)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (out:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V):
    |(physicalPassenger A p coef U-coef*wilsonOrbit A U)-(physicalPassenger A p coef V-coef*wilsonOrbit A V)|
      ≤ |coef| *(2*atomCash k σ C D):=by
  have eq(W:Fld):physicalPassenger A p coef W-coef*wilsonOrbit A W=
      coef*seatLedger A (fun i=>contactTrim (A i)) p W:=by
    rw [physicalPassenger,(actual_passenger_emission A sp pay rec p coef W).tsum_eq];ring
  rw [eq,eq,←mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (seated_passenger_price A (fun i=>contactTrim (A i)) sp pay
    (fun i=>contact_shorter _) (fun _=>le_rfl) p e D U V out cold after) (abs_nonneg _)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
