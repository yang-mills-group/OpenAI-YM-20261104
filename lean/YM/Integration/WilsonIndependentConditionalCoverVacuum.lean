import YM.Integration.WilsonIndependentConditionalScalarConvention
import YM.Integration.WilsonIndependentConditionalVacuumAttachment
import YM.Integration.WilsonIndependentConditionalCoverHeat

/-! Physical positive vacuum ranks, including their complete connected loops,
on an original period family with the free constant vacuum removed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverVacuum
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Lattice Laurent Bloch Matrix
open WilsonIndependentConditionalScalarConvention
open scoped Classical BigOperators
variable {α:Type}[Fintype α]{s e r:ℕ}
variable {K:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}
variable {V:Layers ℝ (Cloth α)}{A:(n:Side)→ Layers ℝ (Co n α)}
variable {P:Pal ℝ (Cloth α)}{F:(n:Side)→ Pal ℝ (Co n α)}

theorem cut (fund:Pilots G K)(g:∀ i ≤ s, ∀ j ≤ e, ∀ r,Yields (fun n=>A n i j r) (V i j r))(hr:0<r):
    curlJ K V V s e r=(1/2:ℝ) • Diagram.drift K V V s e r:=by
  unfold curlJ Diagram.drift Diagram.carry
  simp only [Finset.sum_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl;intro a ha;apply Finset.sum_congr rfl;intro j hj
  have a':a.1+a.2=s:=Finset.HasAntidiagonal.mem_antidiagonal.mp ha
  have j':j.1+j.2=e:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj
  exact WilsonIndependentConditionalVacuumAttachment.original fund (g _ (by omega) _ (by omega)) (g _ (by omega) _ (by omega)) hr

theorem drift {I:Type}(K:Layer I I){A B:ℕ→Orders I}{k:ℕ}
    (h:∀ i≤k,Positive (A i) (B i)):Diagram.drift K A A k=Diagram.drift K B B k:=by
  funext e r
  unfold Diagram.drift;apply Finset.sum_congr rfl;intro v hv
  have eq:v.1+v.2=k:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  unfold Diagram.carry;apply Finset.sum_congr rfl;intro a _
  unfold Diagram.force;apply Finset.sum_congr rfl;intro t _
  simp only [matchTwo,h v.1 (by omega) a.1 (t.1+1) (by omega),h v.2 (by omega) a.2 (t.2+1) (by omega)]

theorem original (fund:Pilots G K)(sym:K.transpose=K)
    (mark:∀i r,Yields (fun n=>F n i r) (P i r))(shape:gradedSymmetric P)(k:ℕ):
    Positive (tide K P k) (logHeat K P false k):=by
  have charges:=tide_pages fund mark
  have same (x y):K x y=K y x:=congrFun (congrFun sym.symm x) y
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro e r hr
    cases k with
    | zero=>rw [tide_zero,logHeat_first,if_neg (by omega)]
    | succ k=>
      have shape':Smooth (tide K P k e (r+2)):=by
        rw [ih k (by omega) e (r+2) (by omega)]
        exact heatedSym K shape false k e (r+2)
      have heat:heating K (tide K P k e) r=heating K (logHeat K P false k e) r:=by
        unfold heating;rw [ih k (by omega) e (r+2) (by omega)]
      rw [tide_rise,logHeat_next,if_neg (by omega)]
      simp only [Pi.smul_apply,Pi.add_apply,Nat.cast_succ]
      have hc:crimp K (tide K P k e) r=rime K (tide K P k e) r:=
        WilsonIndependentConditionalVacuumAttachment.untouched _ hr
      rw [hc,WilsonIndependentConditionalCoverLine.original K same _ r shape',heat,
        cut fund (fun i _ j _ t=>charges i j t) hr,drift K (fun i hi=>ih i (by omega))]
      simp [one_div]

end YM.Integration.WilsonIndependentConditionalCoverVacuum
