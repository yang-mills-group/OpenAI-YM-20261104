import YM.Integration.WilsonVacuumPreResetLiftedAgreement

/-! Each finite signed packet uses its own true seat and exactly the same
covering index on two tori. The comparison includes the actual clover row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedSite
open Function Finset Set Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render PhysicalNext PhysicalNext.Repeat IterationFour.Vacuum
open Extra.Iteration Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes WilsonStartup WilsonVacuumPreResetLiftedPiece
open scoped Classical Topology BigOperators
variable {G:Gauge}{n m:Side}

private theorem turning (s:Signed)(a:ℕ)(U V: CoverConfig G)(h:Agrees (Lattice.box a) U V): Agrees (Lattice.box a) (pull s 0 U) (pull s 0 V):= by
 let X:= Lattice.box a; have hj x (h:x∈ X): Lattice.affine s (0: Cover) x∈ X:=by unfold X; rw [← box_covariant a s,affine,add_zero]; exact mem_image_of_mem s.act h
 rintro ⟨x,i⟩ hx hy
 have hb:=hj x hx; have he:=hj (x+step i) hy; rw [show Lattice.affine s 0 (x+step i)= Lattice.affine s 0 x+((posDir i).rotate s).vec from (by simp [Lattice.affine, s.act_add, Step.vec_rotate])] at he
 unfold pull; cases hq : ((posDir i).rotate s) with | mk k b =>
 rw [hq] at he; cases b; · exact h (affine s 0 x,k) hb he
 have hv : affine s 0 x-step k∈ X:=by simpa only [show (⟨k,true⟩ : Lattice.Step)=negDir k from rfl, Lattice.Step.vec_neg, sub_eq_add_neg] using he
 exact congr_arg Inv.inv (h (affine s 0 x-step k,k) hv (by change affine s 0 x-step k+step k∈X; rwa [sub_add_cancel]))

def index (x:Site n)(s:Signed)(i:ℕ):ℕ:=(numbering (Cycle n)).symm ((s,x),i)

theorem position (a:PrismA G)(B:BudgetPoint)(σ C:ℝ)(x:Site n)(s:Signed)(i:ℕ):
    ((FundedCorrectedPeriod.piece n B σ C a).packet.labels (index x s i)).site=x:=by
  rw [←whole]
  unfold issue index
  simp only [Function.comp_apply,Equiv.apply_symm_apply]
  rfl

theorem seated (a:PrismA G)(B Q:BudgetPoint)(σ τ C E:ℝ)(q i:ℕ)(fit:(a.cells i).length≤q)
    (room:4≤q)(s:Signed)(x:Site n)(y:Site m)(U:Config G n)(V:Config G m)
    (agree:Agrees (Lattice.box q) (expandAt x U) (expandAt y V)):
    (FundedCorrectedPeriod.piece n B σ C a).packet.action (index x s i) U=
      (FundedCorrectedPeriod.piece m Q τ E a).packet.action (index y s i) V:=by
  have match':Agrees (Lattice.box q) (expandAt 0 (pull s x U)) (expandAt 0 (pull s y V)):=by
    simp only [expandAt_pull,affine,Signed.act_zero,zero_add]
    exact turning s q _ _ agree
  rw [←whole,←whole]
  unfold issue index
  simp only [Function.comp_apply,Equiv.apply_symm_apply]
  rcases a with ⟨d,r,hr,P⟩
  cases r with
  | zero=>
    change (recipe 1 Frame.full i)*(baseLine 0 (P i) (pull s x U)-pollen 0 (P i) (pull s x U))=_
    rw [WilsonVacuumPreResetLiftedAgreement.corrected (P i) q fit room 0 0 _ _ match']
    rfl
  | succ r=>
    change (recipe 1 Frame.full i)*((P i).unmasked (pull s x U) 0)=_
    rw [WilsonVacuumPreResetLiftedAgreement.unmasked (P i) q fit 0 0 _ _ match']
    rfl

end YM.Integration.WilsonVacuumPreResetLiftedSite
