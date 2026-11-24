import YM.Integration.WilsonIndependentConditionalCoordinateHeat

/-! The normalized marked heat and the intensive unmarked heat use the
same change of link names, including the rank-zero projection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoordinateVerse
open Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonIndependentConditionalCoordinateHeat
open scoped BigOperators Classical
variable {X Y:Type}(q:X≃Y)

private theorem sum (s:Finset ℕ){r:ℕ}(V:ℕ→Packet Y r):
    (∑ i∈s,row q (V i))=row q (∑ i∈s,V i):=by funext z;simp [row,Finset.sum_apply]

theorem heating (K:Layer Y Y)(T:Ranked Y)(r:ℕ):
    Diagram.heating (line q K) (ranks q T) r=row q (Diagram.heating K T r):=by
  unfold Diagram.heating ranks
  rw [WilsonIndependentConditionalCoordinateHeat.loop,WilsonIndependentConditionalCoordinateHeat.symmetric]
  rfl

theorem pair (K:Layer Y Y)(T S:Ranked Y)(r:ℕ)(p:ℕ×ℕ):
    matchTwo (line q K) (ranks q T) (ranks q S) r p=row q (matchTwo K T S r p):=by
  by_cases h:p.1+p.2=r
  · subst r
    simp only [matchTwo,↓reduceDIte,ranks,WilsonIndependentConditionalCoordinateHeat.knot,WilsonIndependentConditionalCoordinateHeat.symmetric]
    rfl
  · simp only [matchTwo,h,↓reduceDIte]
    rfl

theorem force (K:Layer Y Y)(T S:Ranked Y)(r:ℕ):
    Diagram.force (line q K) (ranks q T) (ranks q S) r=row q (Diagram.force K T S r):=by
  funext z
  simp only [Diagram.force,Finset.sum_apply,pair,row]

theorem carry (K:Layer Y Y)(T S:Orders Y):
    Diagram.carry (line q K) (orders q T) (orders q S)=orders q (Diagram.carry K T S):=by
  funext e r z
  simp only [orders,ranks,Diagram.carry,Finset.sum_apply,force,row]

theorem drift (K:Layer Y Y)(T S:ℕ→Orders Y)(k:ℕ):
    Diagram.drift (line q K) (fun j=>orders q (T j)) (fun j=>orders q (S j)) k=orders q (Diagram.drift K T S k):=by
  funext e r z
  simp only [Diagram.drift,Finset.sum_apply,carry,orders,ranks,row]

theorem vacuum (K:Layer Y Y)(V:Orders Y)(b:Bool)(k:ℕ):
    logHeat (line q K) (orders q V) b k=orders q (logHeat K V b k):=by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    cases k with
    | zero=>
      funext e r
      change logHeat _ _ _ _ _ _=row q (logHeat _ _ _ _ _ _)
      rw [logHeat_first,logHeat_first]
      split <;> rfl
    | succ k=>
      let W:=logHeat (line q K) (orders q V) b
      let W':=fun i=>orders q (logHeat K V b i)
      have d:=forcing_earlier (K:=line q K) k W W' W W' (fun j h=>ih j (by omega)) (fun j h=>ih j (by omega))
      funext e r
      change logHeat _ _ _ _ _ _=row q (logHeat _ _ _ _ _ _)
      rw [logHeat_next,logHeat_next]
      split
      · rfl
      · rw [congrFun (congrFun d e) r,ih k (by omega),drift]
        change _ • (Diagram.heating (line q K) (ranks q _) _+_)=_
        rw [heating]
        rfl

theorem source (K:Layer Y Y)(V:ℕ→Orders Y)(F:Orders Y)(k:ℕ):
    markHeat (line q K) (fun i=>orders q (V i)) (orders q F) k=orders q (markHeat K V F k):=by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    cases k with
    | zero=>rw [markHeat_first,markHeat_first]
    | succ k=>
      let W:=markHeat (line q K) (fun i=>orders q (V i)) (orders q F)
      let W':=fun i=>orders q (markHeat K V F i)
      have d:=forcing_earlier (K:=line q K) k W W' (fun i=>orders q (V i)) (fun i=>orders q (V i))
        (fun j h=>ih j (by omega)) (fun _ _=>rfl)
      funext e r
      change markHeat _ _ _ _ _ _=row q (markHeat _ _ _ _ _ _)
      rw [markHeat_next,markHeat_next,congrFun (congrFun d e) r,ih k (by omega),drift]
      change _ • (Diagram.heating (line q K) (ranks q _) _+_)=_
      rw [heating]
      rfl

theorem marked (K:Layer Y Y)(V F:Orders Y)(k:ℕ):
    endHeat k (line q K) (logHeat (line q K) (orders q V) false) (orders q F)=
      orders q (endHeat k K (logHeat K V false) F):=by
  rw [show logHeat (line q K) (orders q V) false=fun j=>orders q (logHeat K V false j) from funext (vacuum q K V false)]
  funext e r z
  simp only [endHeat,heated,source,orders,ranks,row,Finset.sum_apply]

theorem quiet (K:Layer Y Y)(V:Orders Y):
    ceaseHeat (line q K) (orders q V) false=orders q (ceaseHeat K V false):=by
  funext e r z
  simp only [ceaseHeat,heated,vacuum,orders,ranks,row,Finset.sum_apply]

end YM.Integration.WilsonIndependentConditionalCoordinateVerse
