import YM.Integration.WilsonRegisteredAffineTaylor

/-! Integrate the authentic derivative charges of all short previously
issued rows about a fixed, possibly nonflat configuration. The Taylor
coefficients in the conclusion are those of the independently identifiable
original functions, on the same field and in the same allowed direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineLedger
open Filter Set Finset Lattice Wilson RG Source Push.Local WilsonInheritedRegisteredField
open WilsonRegisteredAffineTaylor
open scoped Classical
variable {G:Gauge} {C:Family G} (h:C.Makes) {k N per d:ℕ}

theorem original (hk:k ≤ N) (hr:C.ref d ≤ k) (w:C.label d) (o:Site (C.side k per))
    (b q:ℕ) (W:Config G (C.side k per)) (D:Directions G (C.side k per)) {r:ℝ} (rp:0<r) :
    let A:=C.path.rep N per k
    let Z:=packet h hk w o
    let L:=C.labels.level d
    let U:=fun t:ℝ=>increment W (t • D)
    let native:=fun i=>if coverNumber A.p.B (Z.support i)<b then Z.maskedTerm A i (U r) else 0
    let budgeted:=fun i=>if coverNumber A.p.B (Z.support i)<b then jet (Z.regular i) W D q r else 0
    A.p.dirBound o D → q+1 ≤ A.p.order →
    (∀ t∈Icc (0:ℝ) r,∀ i,coverNumber A.p.B (Z.support i)<b → Healthy A.p.threshold (Z.support i) (U t)) →
    Summable native ∧ Summable budgeted ∧
    ‖(∑' i,native i)-(∑' i,budgeted i)‖ ≤
      (C.path.levels.params k).columns*L.coeffSize (L.core Z.x)*(r^(q+1)/q.factorial) := by
  intro A Z L U native budgeted admitted order healthy
  have prior:=WilsonTranslatedFactory.based h hr hk o ((C.factory d N per).terminal.symm w)
  have form:Z.Format o C.params A:=prior.1
  obtain ⟨a,c,_,hc,allFee,_,⟨p,P,S⟩,_⟩:=prior.2
  let price:=r^(q+1)/q.factorial
  have pos:0 ≤ price:=by dsimp [price];positivity
  have simple (i:ℕ):p i ≤ A.p.mass (Z.support i) (p i):=A.p.loMass (Z.support i) (p i) (S i).1
  have point (i:ℕ):‖native i‖ ≤ A.p.mass (Z.support i) (p i) ∧
      ‖native i-budgeted i‖ ≤ price*A.p.mass (Z.support i) (p i):=by
    have paid:A.p.supBounds o (Z.support i) (Z.regular i) (p i):=S i
    by_cases short:coverNumber A.p.B (Z.support i)<b
    · have clear:=healthy r (right_mem_Icc.mpr rp.le) i short
      have read:native i=Z.regular i (U r):=by dsimp only [native];rw [if_pos short,Coefficient.maskedTerm,masked_eq _ _ _ _ clear]
      have filed:budgeted i=jet (Z.regular i) W D q r:=if_pos short
      rw [read,filed]
      have bill:=WilsonRegisteredAffineTaylor.original (form.smooth i) paid W D admitted rp
        (fun t ht=>healthy t ht i short) q order
      refine ⟨(paid.2 _ clear [] (Nat.zero_le _) (by simp)).trans (simple i),bill.trans ?_⟩
      calc
        _ = price*p i:=by dsimp only [price];ring
        _ ≤ _:=mul_le_mul_of_nonneg_left (simple i) pos
    have carry:=P.1 i
    simp only [native,budgeted,if_neg short,sub_zero,norm_zero]
    exact ⟨carry,mul_nonneg pos carry⟩
  have ordinary:=sumBudget_mono P (fun i=>norm_nonneg (native i)) (fun i=>(point i).1) le_rfl
  have paid:=sumBudget_mono (sumBudget_mul_left P pos) (fun i=>norm_nonneg (native i-budgeted i))
    (fun i=>(point i).2) le_rfl
  have sn:Summable native:=ordinary.2.1.of_norm
  have sd:Summable (fun i=>native i-budgeted i):=paid.2.1.of_norm
  have sj:Summable budgeted:=(sn.sub sd).congr fun i=>by change native i-(native i-budgeted i)=_; abel
  refine ⟨sn,sj,?_⟩
  rw [←sn.tsum_sub sj]
  exact ((norm_tsum_le_tsum_norm paid.2.1).trans paid.2.2).trans
    ((mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hc).trans allFee) pos).trans_eq (mul_comm ..))

end YM.Integration.WilsonRegisteredAffineLedger
end
