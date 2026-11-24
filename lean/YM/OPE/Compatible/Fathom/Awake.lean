import YM.OPE.Compatible.Fathom.Anthem
import YM.OPE.Compatible.Straws.Stoop
/-!
# Polynomial test degree and scalar IBP. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {I J:Type}{i j k r:ℕ}
local notation "V!"=> Module.Dual ℝ E
variable {p q z:E→ℝ}
variable [FiniteDimensional ℝ E]
lemma veils (u:E) (h:anthem j p): anthem (j-1) (pointD u p):=by
     induction h with
     | bank n t=> unfold pointD; simp; exact anthem.bank ..
     | add ha hb hu hv=> rw [pointS _ _ _ ha.cost hb.cost]; exact hu.add hv
     | @cons n a f h ih=> rw [pointM _ _ _ (Bond.glyph _) h.cost,Nat.add_sub_cancel]; rw [pointC]; apply anthem.add
                          · cases n with
                            | zero=> have hp:∀ q:E→ℝ,∀ n,anthem n q→ n=0 →∃ c:ℝ,q=fun _=>c:=by
                                           intro q n hp hx; induction hp with
                                           | bank n c=> exact ⟨_,rfl⟩
                                           | add h hp hi hh=> obtain ⟨c,hc⟩:= hi hx; obtain ⟨b,hb⟩:= hh hx;rw [hc,hb]; exact ⟨c+b,rfl⟩
                                           | cons _ _ _=>omega
                                     obtain ⟨c,hc⟩:=hp f _ h rfl;rw [hc]; unfold pointD; simp; exact show anthem 0 (⇑a*(0:E→ℝ)) from by rw [mul_zero]; exact anthem.bank ..
                            | succ n=> rw [Nat.add_sub_cancel] at ih; exact anthem.cons a ih
                          rw [show f*(fun _=>a u)=a u • f from funext fun i=> mul_comm ..]; exact h.scale (a u)
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
lemma accord (a:E)(h:Bond p): A.average μ (⇑(A.P a)*p)= A.average μ (pointD a p):=by
      apply bask μ A a p _ h (h.amount a); intro x y; let t(z:ℝ):= x+z • a; have hx:HasDerivAt t a y:=by simpa only [one_smul] using! HasDerivAt.const_add x ( (hasDerivAt_id' y).smul_const a)
      exact (h.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y hx
-- orthogonality vs test degrees <i
structure Husk (μ:Measure E)(A:Law E)(i:ℕ)(f:E→ℝ):Prop where
      coin : Bond f
      pays {j:ℕ}(h:j < i)(g:E→ℝ)(hg:anthem j g): A.average μ (f*g)=0
variable {μ A}
namespace Husk
lemma deriv (h:Husk μ A (j+1) p) (u:E):Husk μ A j (pointD u p):=by
     refine ⟨h.coin.amount u,fun {i} hi g hg=>?_⟩; have hp:A.average μ (p*pointD u g)=0:=h.pays (j:=i) (by omega) _ ((veils u hg).bloat (by omega)) -- fix implicit
     have hh:= h.pays (show i+1<j+1 by omega) _ (anthem.cons (A.P u) hg)
     rw [show p*_=(⇑(A.P u)*(p*g)) from by ring,accord _ _ _ (h.coin.mul hg.cost),pointM _ _ _ h.coin hg.cost,sun μ A (u:=p*pointD u g) (v:=g*pointD u p) (h.coin.mul (hg.cost.amount u)) (hg.cost.mul (h.coin.amount u)),hp,zero_add] at hh; rw [mul_comm]; exact hh
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in lemma zeroH (h:Husk μ A (j+1) p): A.average μ p=0:=by have hp:=h.pays (show 0<j+1 by omega) 1 (anthem.bank ..); rwa [mul_one] at hp
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in lemma subW (h:Husk μ A j p)(hp:i≤j): Husk μ A i p:=⟨h.coin,fun hx g=> h.pays (lt_of_lt_of_le hx hp) g⟩
lemma foster (h:Bond p)(hp:A.average μ p=0)(hz:∀ v:E,Husk μ A j (pointD v p)): Husk μ A (j+1) p:=by
     induction j using Nat.strong_induction_on with
     | h j ihV=>
        refine ⟨h,fun {i} hi g hg=>?_⟩; induction hg with
        | bank n t=> rw [show p*(fun _=>t)=t • p from funext fun i=> mul_comm ..,scooted,hp,mul_zero]
        | add ha hb ha' hb'=> rw [mul_add,sun μ A (h.mul ha.cost) (h.mul hb.cost),ha' hi,hb' hi,add_zero]
        | @cons n a f hh ih=> let u:= A.inverse a; rw [← (show A.P u=a from A.applies _), show p*_=⇑(A.P u)*(p*f) from by ring, accord μ A _ (h.mul hh.cost), pointM _ _ _ h hh.cost, sun μ A (u:=p*pointD u f) (v:=f*pointD u p) (h.mul (hh.cost.amount u)) (hh.cost.mul (h.amount u)), mul_comm f, (hz u).pays (by omega) f hh,add_zero]; -- need ih not enough; induction j to get lower test result!
                              obtain ⟨t,ht⟩: ∃ t:ℕ,t+1 ≤ j∧ n-1<t+1 := ⟨n,by omega,by omega⟩; exact (ihV t (by omega) fun v=> (hz v).subW (by omega)).pays ht.2 _ (veils u hh)
end Husk
end YM.OPE.Cloud
