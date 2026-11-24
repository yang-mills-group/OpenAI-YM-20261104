import YM.RegulatorIR.Diagram.Heat

/-! The marked transfer retains its whole scalar when only the unmarked log is
filed modulo its constant. This also holds on the original infinite index set. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalScalarConvention
open RegulatorIR RegulatorIR.Diagram RegulatorIR.Budget
variable {I:Type}(K:Layer I I)

def Positive (U V:Orders I):Prop:=∀ e r,0<r→U e r=V e r

private theorem drift_positive {T T' S S':ℕ→Orders I}{k:ℕ}
   (h:∀ i≤k,Positive (T i) (T' i))(g:∀ i≤k,Positive (S i) (S' i)):drift K T S k=drift K T' S' k:=by
  funext e r
  unfold drift;apply Finset.sum_congr rfl;intro v hv
  have eq:=Finset.mem_antidiagonal.mp hv
  unfold carry;apply Finset.sum_congr rfl;intro a _
  unfold force;apply Finset.sum_congr rfl;intro t _
  simp only [matchTwo,h v.1 (by omega) a.1 (t.1+1) (by omega),g v.2 (by omega) a.2 (t.2+1) (by omega)]

theorem positive {V U:Orders I}(h:Positive V U)(s t:Bool)(k:ℕ):
    Positive (logHeat K V s k) (logHeat K U t k):=by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro e r hr
    have ne:r≠0:=by omega
    cases k with
    | zero=>simpa only [logHeat_first,ne,false_and,if_false] using h e r hr
    | succ k=>
      rw [logHeat_next,logHeat_next]
      simp only [ne,false_and,if_false]
      have earlier : ∀ i≤k,Positive (logHeat K V s i) (logHeat K U t i):=fun i hi=>ih i (by omega)
      rw [drift_positive K earlier earlier]
      simp only [heating,earlier k le_rfl e (r+2) (by omega)]

theorem original {V U:Orders I}(h:Positive V U)(s t:Bool)(m:ℕ)(F:Orders I):
    endHeat m K (logHeat K V s) F=endHeat m K (logHeat K U t) F:=by
  let W:=logHeat K V s
  let W':=logHeat K U t
  have same (k:ℕ):markHeat K W F k=markHeat K W' F k:=by
    induction k using Nat.strong_induction_on with
    | h k ih=>
      cases k with
      | zero=>rw [markHeat_first,markHeat_first]
      | succ k=>
        funext e r
        rw [markHeat_next,markHeat_next,ih k (by omega)]
        have z:∀ i≤k,Positive (markHeat K W F i) (markHeat K W' F i):=by
          intro i hi j r _
          rw [ih i (by omega)]
        rw [drift_positive K z (fun j _=>positive K h s t j)]
  change heated _ (markHeat K W F)=heated _ (markHeat K W' F)
  rw [funext same]

end YM.Integration.WilsonIndependentConditionalScalarConvention
