import YM.OPE.Compatible.Cum.Cove
/-!
# Playback bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier
variable {I J E R:Type}{A:Row I I}{v w:J→ℕ}{p:∀ i:J,Script I (w i+v i)}{t:Side}{d e k m n:ℕ}
variable [DecidableEq J] {s:Finset J} {α:J→Bool}
variable {F u g y:ℝ}{r:J→ℝ}{P:Script I (e+d+1)}
lemma payrollX (hu:0<u)(hy:0≤ y): Payroll I u y m v w s d e:=by
      apply inductS (fun s d e=>Payroll I u y m v w s d e) _ _
      · intro i e; by_cases h:i=∅
        · refine ⟨1,zero_le_one,fun A hA α P r h' q b hq x=>?_⟩; rw [Hall_nil, if_pos h,h,prod_empty,mul_one,one_mul]; by_cases he:x=e; · subst x; exact (show Shell.throw q (e+0)= q from Pi.single_eq_same ..) |>.symm ▸ hq
          rw [hubbub (e:=x) he]; exact Sack.zero (Sack.coins hq) _
        exact ⟨0,le_rfl,fun A hA α P r h' q b hq x=>by rw [Hall_nil,if_neg h,zero_mul,zero_mul]; exact Sack.zero le_rfl _⟩
      intro s d e h hp he; obtain ⟨b,hb,Y⟩:=h
      choose! B hB H using fun i hi=> crownR s i hi (he i hi) d e hu hy
      have hh: ∃ D:ℝ,0 ≤ D∧ ∀ (A:Row I I),A.strip u y→ ∀ (α:J→Bool)(P:∀ i:J,Script I (w i+v i))(r:J→ℝ), coversB v w P m r s→ ∀ (g:Script I (e+d+1)) (f:ℝ),soot m g f→ ∀ x:ℕ, soot m (WalkK A e d g (Shell.Hall A v w P α s) x) (D*f*∏ i∈s,r i):=by
            cases d
            next => refine ⟨0,le_rfl,fun A hA α P r h' g f hG x=>?_⟩;rw [zero_mul, zero_mul, soak_nil]; exact Sack.zero le_rfl _
            next d=>
              obtain ⟨D,hD,L⟩:= hp d (by omega) e; refine ⟨(d+1:ℕ)*D*y,by positivity,fun A hA α P r h' g f hG x=> ?_⟩; rw [soak_plus, Finset.sum_apply]; refine (Sack.finGather (univ:Finset (Fin (d+1))) _ (fun _=>_) (fun i _=>L A hA α P r h' _ _ (styleR g hA hu.le hy hG i) x) (fun i=> zero_le_one.trans (payer m i))).tips ?_;rw [sum_const,card_univ,Fintype.card_fin, nsmul_eq_mul]; exact le_of_eq (by ring)
      obtain ⟨D,hD,hh⟩:=hh; refine ⟨b+D+∑ i∈s,B i,add_nonneg (add_nonneg hb hD) (sum_nonneg hB),fun A hA α P r h' g f hG x=> ?_⟩
      have ht:= Y A hA α P r h' (Shell.Temper e d g) f (StyleK m g hG) x; rw [script_run,Pi.add_apply,Pi.add_apply,Finset.sum_apply]; exact (Sack.splits (Sack.splits ht (hh A hA α P r h' g f hG x) (fun i=>zero_le_one.trans (payer m i))) (Sack.finGather s _ _ (fun i hi=>H i hi A hA α P r h' f g hG x) (fun i=>zero_le_one.trans (payer m i))) (fun i=>zero_le_one.trans (payer m i))).tips (le_of_eq (by rw [add_mul,add_mul,add_mul,add_mul,sum_mul,sum_mul]))
end YM.OPE.Libra.Shell
