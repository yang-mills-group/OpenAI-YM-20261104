import YM.Integration.QLocalMarkedJoinedWeight
import YM.Integration.QLocalCompulsoryJoinedTape

/-! Charge the separately stored scalar force entries on the real old and
joined addresses. The old entries are copied verbatim. The new scalar
majorant is chosen before all independent inputs and configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedForcedBudget
open Function Finset Set Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic Push.AbsoluteSums LocalComparison.Global ActualWilsonJoinedCofactor QLocalMarkedJoinedWeight
open WilsonLimitConstruction.FundedMarkedFieldSplit QLocalCompulsoryJoinedTape QLocalCompulsoryInventoryBank
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {W:Rep G n} {X V:Type} [DecidableEq V] [Fintype V]
    {Γ:Census V} {o:V→Site n} {p:BudgetPoint} {w:V→ℝ}

def indices (Γ:Census V) : ((ℕ×ℕ)⊕(ℕ×Γ.Mode))≃(ℕ×ℕ) where
  toFun:=Sum.elim (fun z=>(z.1,roster Γ (.inl z.2))) (fun z=>(z.1,roster Γ (.inr z.2)))
  invFun:=fun z=>Sum.elim (fun j=>.inl (z.1,j)) (fun s=>.inr (z.1,s)) ((roster Γ).symm z.2)
  left_inv:=by rintro (⟨i,j⟩|⟨i,s⟩) <;> simp
  right_inv:=by
    rintro ⟨i,j⟩
    obtain ⟨s,rfl⟩:=(roster Γ).surjective j
    cases s <;> simp

theorem serial (d:X→ℕ→ Config G n→Poly Γ) (T:Taste X o W Γ) {κ price c:ℝ}
    (hw:∀v,0<w v) (κpos:0<κ) (B:ForcedBudget p T w κ price)
    (new:Coupon p (fun i (z:X×Config G n)=>d z.1 i z.2) w W c) :
    Nonempty (ForcedBudget p (replace T (QLocalCompulsoryJoinedTape.tape T d)) w κ (price+(Fintype.card Γ.Mode:ℝ)*c/κ)) := by
  let e:=indices Γ
  let fresh (z:ℕ×Γ.Mode):=if z.2=Γ.quiet then 0 else new.major z.1/Poly.toll w z.2
  let b (i:ℕ×ℕ):=(Sum.elim B.black fresh) (e.symm i)
  have nn (z:ℕ×Γ.Mode):0≤fresh z:=by
    unfold fresh
    split
    · exact le_rfl
    · exact div_nonneg (new.nonnegative _) (Poly.worth hw _).le
  have orig i j:b (i,roster Γ (.inl j))=B.black (i,j):=by
    change Sum.elim B.black fresh (e.symm (e (.inl (i,j))))=_
    simp
  have add i s:b (i,roster Γ (.inr s))=fresh (i,s):=by
    change Sum.elim B.black fresh (e.symm (e (.inr (i,s))))=_
    simp
  refine ⟨{black:=b,black_nonnegative:=?_,forced:=?_,total:=?_}⟩
  · rintro ⟨i,j⟩
    obtain ⟨t,rfl⟩:=(roster Γ).surjective j
    cases t with
    | inl j=>rw [orig]; exact B.black_nonnegative _
    | inr s=>rw [add]; exact nn _
  · intro x i j U
    obtain ⟨t,rfl⟩:=(roster Γ).surjective j
    cases t with
    | inl j=>
      rw [orig]
      change ‖(QLocalCompulsoryJoinedTape.tape T d).value x i (roster Γ (.inl j)) U‖≤_
      rw [(QLocalCompulsoryJoinedTape.original T d x i j U).2]
      exact B.forced x i j U
    | inr s=>
      rw [add]
      by_cases quiet:s=Γ.quiet
      · simp [replace,QLocalCompulsoryJoinedTape.tape,QLocalCompulsoryJoinedTape.entry,fresh,quiet]
      · simp only [replace,QLocalCompulsoryJoinedTape.tape,QLocalCompulsoryJoinedTape.entry,Equiv.symm_apply_apply,Sum.elim_inr,fresh,if_neg quiet]
        apply (le_div_iff₀ (Poly.worth hw s)).mpr
        rw [mul_comm]
        exact (Poly.member hw s _).trans (new.field i (x,U))
  · intro v
    let bill (ij:ℕ×ℕ):=if v∈((replace T (QLocalCompulsoryJoinedTape.tape T d)).menu.marks ij.1 ij.2).val then
      Poly.toll w ((replace T (QLocalCompulsoryJoinedTape.tape T d)).menu.marks ij.1 ij.2)*p.mass (ActualWilsonPacketSplit.scopes W ij.1) (b ij) else 0
    have old:SumBudget (fun z:ℕ×ℕ=>bill (e (.inl z))) (κ*price):=by
      convert B.total v using 1
      funext z
      simp [bill,e,indices,replace,QLocalCompulsoryJoinedTape.tape,mode,orig,ActualWilsonPacketSplit.scopes]
    have one:SumBudget (fun _:Γ.Mode=>(1:ℝ)) (Fintype.card Γ.Mode):=
      budget_finite (fun _=>zero_le_one) (by simp)
    have row (i:ℕ) (s:Γ.Mode) : bill (e (.inr (i,s))) =
        if v∈s.val then Poly.toll w s*p.mass (ActualWilsonPacketSplit.scopes W i) (fresh (i,s)) else 0 := by
      change (if v∈(mode T.menu.marks i ((roster Γ) (.inr s))).val then
        Poly.toll w (mode T.menu.marks i ((roster Γ) (.inr s))) *
          p.mass (ActualWilsonPacketSplit.scopes W i) (b (i,(roster Γ) (.inr s))) else 0) = _
      rw [add]
      by_cases hz:s=Γ.quiet
      · simp [mode,hz,fresh,BudgetPoint.mass]
      · simp [mode,hz]
    have right:SumBudget (fun z:ℕ×Γ.Mode=>bill (e (.inr z))) (c*(Fintype.card Γ.Mode:ℝ)):=by
      apply budget_mono (budget_prod new.full one)
      · rintro ⟨i,s⟩
        rw [row]
        split
        next => exact mul_nonneg (Poly.worth hw _).le ((nn (i,s)).trans (p.loMass _ _ (nn (i,s))))
        next => exact le_rfl
      · rintro ⟨i,s⟩
        change bill (e (.inr (i,s))) ≤ p.mass (ActualWilsonPacketSplit.scopes W i) (new.major i)*1
        rw [row,mul_one]
        by_cases hv:v∈s.val
        · rw [if_pos hv]
          have hz:s≠Γ.quiet:=by
            intro eq
            rw [eq] at hv
            exact Finset.notMem_empty _ hv
          apply le_of_eq
          simp only [fresh,if_neg hz,BudgetPoint.mass]
          field_simp [(Poly.worth hw s).ne']
        · rw [if_neg hv]
          exact new.full.1 i
    have sums:=HasSum.sum (f:=bill ∘ e) old.2.1.hasSum right.2.1.hasSum
    have sum:=e.hasSum_iff.mp sums
    change SumBudget bill _
    refine ⟨?_,sum.summable,?_⟩
    · intro ij
      obtain ⟨z,rfl⟩:=e.surjective ij
      cases z with
      | inl i=>exact old.1 i
      | inr i=>exact right.1 i
    rw [sum.tsum_eq]
    exact (add_le_add old.2.2 right.2.2).trans_eq (by field_simp [κpos.ne'])

end YM.Integration.QLocalMarkedJoinedForcedBudget
