import YM.Integration.WilsonIndependentConditionalCoordinateVerse

/-! A finite appointed thermal order uses only the same order of the full
incoming source and the positive angular ranks of the incoming action. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalThermalCap
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open scoped BigOperators Classical
variable {X:Type}{d:ℕ}(K:Layer X X)

theorem drift {T T' U U':ℕ→Orders X}{j e:ℕ}(he:e≤d)
    (ht:∀i≤j,∀a≤d,T i a=T' i a)(hu:∀i≤j,∀a≤d,U i a=U' i a)(r:ℕ):
    Diagram.drift K T U j e r=Diagram.drift K T' U' j e r:=by
  unfold Diagram.drift
  apply Finset.sum_congr rfl
  intro p hp
  have hp':=Finset.mem_antidiagonal.mp hp
  unfold carry
  apply Finset.sum_congr rfl
  intro b hb
  have hb':=Finset.mem_antidiagonal.mp hb
  rw [ht _ (by omega) _ (by omega),hu _ (by omega) _ (by omega)]

theorem quiet {V W:Orders X}(read:∀e≤d,∀r,0<r→V e r=W e r)(j:ℕ):
    ∀ e≤d,logHeat K V false j e=logHeat K W false j e:=by
  induction j using Nat.strong_induction_on with
  | h j ih=>
    cases j with
    | zero=>
      intro e he
      funext r
      rw [logHeat_first,logHeat_first]
      by_cases h:r=0
      · simp [h]
      · simp only [h,false_and,if_false]
        exact read e he r (by omega)
    | succ j=>
      intro e he
      funext r
      rw [logHeat_next,logHeat_next]
      rw [ih j (by omega) e he,drift K he (fun v hv=>ih v (by omega)) (fun v hv=>ih v (by omega))]

theorem marked {S T:ℕ→Orders X}{F G:Orders X}(ink:∀ e≤d,F e=G e)
    (quiet:∀j,∀e≤d,S j e=T j e)(j:ℕ):∀ e≤d,markHeat K S F j e=markHeat K T G j e:=by
  induction j using Nat.strong_induction_on with
  | h j ih=>
    cases j with
    | zero=>simpa only [markHeat_first] using ink
    | succ j=>
      intro e he
      funext r
      rw [markHeat_next,markHeat_next,ih j (by omega) e he,
        drift K he (fun v hv=>ih v (by omega)) (fun v _=>quiet v)]

theorem original {V W F G:Orders X}(read:∀e≤d,∀r,0<r→V e r=W e r)(ink:∀e≤d,F e=G e)
    (k:ℕ){e:ℕ}(he:e≤d):
    endHeat k K (logHeat K V false) F e=endHeat k K (logHeat K W false) G e:=by
  funext r
  unfold endHeat heated
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (marked K ink (quiet K read) j e he) r

end YM.Integration.WilsonIndependentConditionalThermalCap
