import YM.RGComparison01.Post.Direct
import YM.RGComparison01.Tithe
/-!
# Render V and residual as DISTINCT signed labels. Reuse K
 data on EXACT same supports. Create indefinitely many blanked regular labels
 (at each orientation too), e.g. for emitting further log markers. No claim
 on Ribbon layout counts after combining (charge any such reading separately).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Post.Split
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Ovens.Pipes
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup Averaging AnalyticBridge.VerifiedReset.Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {n:Side}{C D Z:Activities G n}{p:BudgetPoint} {w h r d:ℝ}
abbrev Heads (n:Side):= {X:Support n // (0:Site n)∈X}
abbrev Lamps (n:Side):=ℕ × Seat n × Heads n
abbrev Parts (n:Side):= ℕ⊕(ℕ⊕Lamps n)
def tie (n:Side): ℕ ≃ Parts n:= numbering _
-- no REG links conflated -- Z retains K. Require reg's support align only for reconstruction.
def parts (C D:Activities G n): Parts n→ RegularAddress n:= Sum.elim C.reg (Sum.elim D.reg (fun i=> Seat.reg i.2.1 _ i.2.2.property))
def songs (C D:Activities G n): Parts n→ Pot G n:=Sum.elim C.E (Sum.elim D.E 0)
def hub (C D Z:Activities G n): Activities G n:= {Z with reg:= parts C D∘ tie n,E:= songs C D ∘ tie n}
-- boolean designation of D alone. permit C Null contribution too by Titheportion later.
def mystery (n:Side)(i:ℕ): Prop:= ∃ j:ℕ,tie n i= Sum.inr (Sum.inl j)
local notation "J"=> hub C D Z
lemma postCost (h': C.EBound p w)(hT:D.EBound p d): (hub C D Z).EBound p (w+d):=by
    obtain ⟨g,h,h'⟩:=h'; obtain ⟨f,hF,hY⟩:=hT; let x : Parts n→ℝ:=Sum.elim g (Sum.elim f 0); refine ⟨x ∘ tie n,fun i=>?_,fun i=>?_⟩
    · change p.supBounds _ _ (songs C D (tie n i)) (x (tie n i))
      unfold hub; dsimp only [comp_apply]; rcases tie n i with i|i|i -- already expands some
      · exact h _
      · exact hF _
      exact CouplingShape.sup_larger (CouplingShape.sup_const 0) abs_zero.le
    let F (j:Parts n):= if (parts C D j).site=i then p.mass (parts C D j).support (x j) else 0
    have he:SumBudget (fun j:Lamps n=>F (.inr (.inr j))) 0:= by simp [F,SumBudget,x,BudgetPoint.mass]
    have ht:SumBudget (F ∘ Sum.inr) (d+0):=Cost.sum (hY i) he; rw [add_zero] at ht; exact Cost.equiv (tie n) (show SumBudget F (w+d) from Cost.sum (h' i) ht)
lemma tidy (hT:D.EBound p d)(C Z:Activities G n): (Tithe.portion (hub C D Z) (mystery n)).EBound p d:=by
    obtain ⟨g,hF,hT⟩:=hT; let f : Parts n→ ℝ:= Sum.elim 0 (Sum.elim g 0); let H (i:ℕ):= f (tie n i); refine ⟨H,fun i=> ?_,fun i=>?_⟩
    · unfold Tithe.portion hub; dsimp only [comp_apply]; unfold mystery; generalize he: tie n i=u
      rcases u with i'|i'|i' <;> unfold H <;> rw [he]
      · simp only [reduceCtorEq, exists_false, ↓reduceIte]; exact CouplingShape.sup_larger (CouplingShape.sup_const 0) abs_zero.le
      · rw [if_pos ⟨_,rfl⟩]; exact hF _
      rw [if_neg]; exact CouplingShape.sup_larger (CouplingShape.sup_const 0) abs_zero.le; simp
    let F (j:Parts n):= if (parts C D j).site=i then p.mass (parts C D j).support (f j) else 0
    have he:SumBudget (fun j:Lamps n=>F (.inr (.inr j))) 0:= by simp [F,SumBudget,f,BudgetPoint.mass]
    have ht:SumBudget (F ∘ Sum.inr) (d+0):=Cost.sum (hT i) he; have hx:SumBudget (F∘ Sum.inl) 0:= by simp [comp_def, F,SumBudget,f,BudgetPoint.mass]
    rw [add_zero] at ht; conv_rhs=> rw [← zero_add d]
    exact Cost.equiv (tie n) (show SumBudget F _ from Cost.sum hx ht)
lemma edited (he:C.RegularFamily p)(hh:D.RegularFamily p): (hub C D Z).RegularFamily p:=by
   let X (i):= parts C D i; let T i:=songs C D i
   suffices h : ∀ i, p.Regular (X i).support (T i)∧ T i 1=0∧ ∀ _h:Nonwrapping (X i).support (X i).site, ∀ x y:Directions G n, IsAffineDirection (X i).site x→ IsAffineDirection (X i).site y→logHessian (T i) x y=0 from ⟨fun _=>(h _).1,fun _=>(h _).2.1,fun _=>(h _).2.2⟩ -- Dir typo
   rintro (i|i|i); exact ⟨he.smooth _,he.at_flat i,he.vanish i⟩; exact ⟨hh.smooth _,hh.at_flat i,hh.vanish i⟩
   refine ⟨CouplingShape.reg_const _,rfl,fun _ x y _ _=> ?_⟩
   unfold logHessian; change iteratedFDeriv ℝ 2 (fun _: Directions G n=> (0:ℝ)) 0 _=0; simp

def leaps (n:Side)(s: Signed)(t:Site n): Equiv.Perm (Lamps n):= (Equiv.refl ℕ).prodCongr ((Seat.move s t).prodCongr (Equiv.refl _))
def propel {s:Signed}{t:Site n}(m:C.Moves s t)(u:D.Moves s t): Equiv.Perm (Parts n):= Equiv.sumCongr m.ep (Equiv.sumCongr u.ep (leaps n s t))
abbrev orbit {s:Signed}{t:Site n}(m:C.Moves s t)(u:D.Moves s t): Equiv.Perm ℕ:= ((tie n).trans (propel m u)).trans (tie n).symm
-- preserve plot.Lab.Key for calibration after
variable {s:Signed}{t:Site n}
def parlay (m:C.Moves s t)(u:D.Moves s t)(v:Z.Moves s t): (hub C D Z).Moves s t:= by
    let z:= propel m u; have ht i: tie n (orbit m u i)= z (tie n i):= (tie n).apply_symm_apply _
    have hx(i : Parts n): let p:=parts C D; (p (z i)).site=affine s t (p i).site∧(p (z i)).support=(p i).support.image (affine s t) ∧ ∀ U,songs C D (z i) U=songs C D i (pull s t U):=by
       dsimp only []; rcases i with i|i|i
       · exact ⟨m.reg_site i,m.reg_support i,m.valuesE i⟩
       · exact ⟨u.reg_site i,u.reg_support i,u.valuesE i⟩
       exact ⟨rfl,Seat.spread_move ..,fun _=>rfl⟩
    refine ⟨orbit m u,v.kp,fun i=> ?_,fun i=>?_, v.forced_support,v.forced_inventory,v.forced_tests,fun i x=>?_,v.valuesK⟩
    · change (parts C D (tie n _)).site=_; rw [ht]; exact (hx _).1
    · change (parts C D (tie n _)).support=_; rw [ht]; exact (hx _).2.1
    change songs C D (tie n _) x=_; rw [ht]; exact (hx _).2.2 _
lemma still (he:C.RegularFamily p)(hh:D.RegularFamily p)(m:∀ s t, Nonempty (C.Moves s t))(u:∀ s t, Nonempty (D.Moves s t))(h':C.EBound p w)(hT:D.EBound p d)(hZ:Z.Valid p h r): (hub C D Z).Valid p (w+d) r:= by
    have hx:= hZ.forced; exact ⟨edited he hh,⟨hx.sym,hx.symtest,hx.meas,hx.meas_test,hx.reads,hx.reads_test,hx.permit⟩,fun s t=>⟨parlay (Classical.choice (m s t)) (Classical.choice (u s t)) (Classical.choice (hZ.moves s t))⟩,postCost h' hT,hZ.boundK⟩
-- VALUE and additive. no changing flags.
lemma consumes (he:C.reg=Z.reg)(hh:D.reg=Z.reg)(hp:Z.E=C.E+D.E)(h:C.EBound p w)(hT:D.EBound p r) (U:Config G n): (hub C D Z).additive p U= Z.additive p U:=by
    let g i:= masked p.threshold (parts C D i).support (songs C D i) U
    have hz : Summable (fun i: Lamps n=>g (.inr (.inr i))):=by
       have h: (fun i: Lamps n=>g (.inr (.inr i)))=fun _=>0:= funext fun i=> by unfold g; simp only [masked, Set.indicator_apply]; split<;> rfl
       rw [h]; exact summable_zero
    have hx (U':Activities G n)(a:ℝ)(h:U'.EBound p a): Summable (fun i=> U'.regularOccurrence p i U):= by
       obtain ⟨k,hk,hK⟩:= Activities.E_total h; refine Summable.of_norm_bounded hk (fun i=>?_)
       change ‖masked _ _ _ _‖ ≤ _; simp only [masked, Set.indicator_apply]; split
       next hx=> exact (hK i).2 U hx [] (by simp) (by simp)
       next hx=> exact (norm_zero).le.trans (hK i).1
    have h1:=hx _ w h; have h2:=hx _ _ hT
    change ∑' i,g (tie n i)= _; rw [(tie n).tsum_eq g,Summable.tsum_sum (f:=g) h1 (Summable.sum _ h2 hz),Summable.tsum_sum (f:=fun i=>g (.inr i)) h2 hz]
    rw [show (fun i: Lamps n=>g (.inr (.inr i)))=fun _=> (0:ℝ) from funext fun i=> by simp only [g,masked,Set.indicator_apply]; split<;> rfl,tsum_zero,add_zero]
    rw [← Summable.tsum_add]; swap; exact h1
    swap; exact h2
    unfold Activities.additive; refine tsum_congr fun i=> ?_
    change C.regularOccurrence p i U+D.regularOccurrence p i U= Z.regularOccurrence p i U; simp only [Activities.regularOccurrence,he,hh,hp]; simp only [masked, Set.indicator_apply]; split <;> simp_all
end YM.RGComparison01.Post.Split
