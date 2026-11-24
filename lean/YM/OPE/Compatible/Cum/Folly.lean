import YM.OPE.Compatible.Cum.Opera
/-!
# induction on cuts. Handy refactor
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page
variable {I J E R:Type} {V:Row I I}{u v:J→ℕ}{P:∀ i:J,Script I (v i+u i)}{t:Side}{d e:ℕ}
variable [DecidableEq J] {q:Finset J} {l:J→ Bool}
lemma inductS (H: (Finset J)→ℕ→ℕ→Prop) (h₀:∀ v e,H v 0 e)(hp:∀ s d e,H s d (e+1)→ (∀ k<d,∀ y,H s k y)→ (∀ i∈s,∀ k y,H (s.erase i) k y)→ H s (d+1) e):∀ x i j,H x i j:=by
    intro x; induction x using Finset.strongInduction with | _ s ih=> intro i; induction i using Nat.strong_induction_on with
          | _ i hk=> cases i
                     next => exact h₀ s
                     next i=> intro e; exact hp s i e (hk i (by omega) (e+1)) (fun k hy=> hk k (by omega)) (fun t ht=> ih _ (erase_ssubset ht))
section
-- recursion operator types
variable (μ:J→ℕ)
abbrev Rollup (u v:J→ℕ)(s:Finset J)(d e:ℕ):ℕ:= (∑ i∈s,(u i+v i)) +e+d
omit [DecidableEq J] in lemma rolling_le {t:Finset J} (h:t⊆q):Rollup u v t d e≤Rollup u v q d e:=Nat.add_le_add_right (Nat.add_le_add_right (sum_le_sum_of_subset h) _) _
lemma rollingB {t:J}(hp:t∈q)(j:ℕ)(h:u t=j+1): Rollup u v (q.erase t) (d+j) (e+v t)+2= Rollup u v q (d+1) e :=by
         unfold Rollup; rw [(show ∑ i∈q,(u i+v i)=(u t+v t)+∑ i∈q.erase t,(u i+v i) from by exact (sum_erase_add q (fun i=> u i+v i) hp).symm.trans (Nat.add_comm ..) )] -- fix precedence
         omega
lemma hubbub {r:ℕ}{w:Script I r}(h:¬ e=r):(Shell.throw w) e=0:= Pi.single_eq_of_ne h w
-- uncharged stamp bounds
lemma rim_height (x:ℕ)(ht:Rollup u v q d e < x+2*q.card) (T:Script I (e+d)): Shell.Hall V u v P l q d e T x=0:=by
     let f:=Shell.Hall V u v P l
     refine inductS (J:=J) (fun q d e => Rollup u v q d e < x+2*q.card→ ∀ T,f q d e T x=0) (fun v p=>?_) (fun s d e h H P' hp T=>?_) q d e ht T
     · intro h T; unfold f; rw [Hall_nil]; split
       next hv=> apply hubbub; rw [Rollup,hv,sum_empty,card_empty] at h; omega
       next h=>rfl
     unfold f; rw [script_run]; rw [Pi.add_apply, Pi.add_apply, show Shell.Hall V _ _ _ _ _ _ _ _ x= _ from h (by unfold Rollup at hp ⊢; omega) _, Finset.sum_apply]
     have hh: WalkK V e d T (f s) x=0:=by
          cases d with
          | zero=> rw [soak_nil]; rfl
          | succ d=> rw [soak_plus,Finset.sum_apply]; exact sum_eq_zero fun i _=>H d (by omega) e (by unfold Rollup at *; omega) _
     rw [hh]; suffices hQ : (∑ i∈s,((if l i then Once V (f (s.erase i)) e d T (v i) (u i) (P i) else 0): Curtain I) x)=0 by rw [hQ];simp
     refine Finset.sum_eq_zero fun i hi=>?_; split
     next hL =>
        have hv (y:ℕ)(X:Script I (v i+y))(he:u i=y): Once V (f (s.erase i)) e d T (v i) y X x=0:=by
             cases y
             next =>rfl
             next y=>rw [once_plus,Finset.sum_apply]; have ht:= rollingB (d:=d) (e:=e) (u:=u) (v:=v) hi y he; have hy:= Finset.card_erase_add_one hi; exact sum_eq_zero fun k _=> P' i hi _ _ (by omega) _
        exact hv _ _ rfl
     next h=>rfl
end
end YM.OPE.Libra.Shell
