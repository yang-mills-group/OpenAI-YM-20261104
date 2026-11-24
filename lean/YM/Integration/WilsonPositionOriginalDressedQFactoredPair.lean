import YM.Integration.WilsonPhysicalHistoryKtoneModeTable

/-! Both signed emitted singleton multipliers cancel in the true four-corner
test. Each pair of occupied labels reads its original factored mixed entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQFactoredPair
open Finset Function Marker Overlay Extra.Trajectories WilsonPhysicalHistoryKtone
open scoped BigOperators Classical

private theorem fired (P Q:Poly pairBook)(b:Bool):
    (P*Q).part (pairBook.fire b)=P.part pairBook.quiet*Q.part (pairBook.fire b)+
      P.part (pairBook.fire b)*Q.part pairBook.quiet:=by
  cases b <;> rw [Poly.part_mul,mode_sum] <;> simp only [mode_sum] <;>
    simp (disch:=decide) only [if_pos,if_neg,add_zero,zero_add]

private theorem expand (P:Poly pairBook):Poly.pass P=(1+P)+(2:ℂ)⁻¹ • ((P*P):Poly pairBook):=by
  unfold Poly.pass
  norm_num [Finset.sum_range_succ,Nat.factorial,pow_succ]

private theorem factors (L Y:Poly pairBook)(mute:L.part pairBook.quiet=0):
    Y.part pairMode-Y.part (pairBook.fire false)*L.part (pairBook.fire true)-
      Y.part (pairBook.fire true)*L.part (pairBook.fire false)+
        Y.part pairBook.quiet*L.part (pairBook.fire false)*L.part (pairBook.fire true)=
      (Poly.pass (-L)*Y).part pairMode + Y.part pairBook.quiet*L.part pairMode:=by
  rw [joined_mul,expand]
  simp (disch:=decide) only [Poly.part_plus,Poly.part_neg,Poly.part_smul,Poly.one_part,
    joined_mul,fired,Poly.quiet_mul,if_pos,if_neg,mute]
  ring

theorem original {V:Type}[DecidableEq V][Fintype V]{Γ:Census V}(a b:V)(apart:a≠b)
    (s:Γ.Mode)(roots:s.val={a,b})(L Y:Poly Γ)(mute:L.part Γ.quiet=0):
    Y.part s-Y.part (Γ.fire a)*L.part (Γ.fire b)-Y.part (Γ.fire b)*L.part (Γ.fire a)+
      Y.part Γ.quiet*L.part (Γ.fire a)*L.part (Γ.fire b)=
      (Poly.pass (-L)*Y).part s+Y.part Γ.quiet*L.part s:=by
  let u:=twoNames a b apart s roots
  have quiet:(u.restriction L).part pairBook.quiet=0:=by change L.part (u.share pairBook.quiet)=0;simpa only [Names.quiet] using mute
  have read:=factors (u.restriction L) (u.restriction Y) quiet
  have empty:(-L).part Γ.quiet=0:=by simp [mute]
  rw [←map_neg,←u.pass_restrict empty,←map_mul] at read
  change Y.part (u.share pairMode)-Y.part (u.share (pairBook.fire false))*L.part (u.share (pairBook.fire true))-
    Y.part (u.share (pairBook.fire true))*L.part (u.share (pairBook.fire false))+
    Y.part (u.share pairBook.quiet)*L.part (u.share (pairBook.fire false))*L.part (u.share (pairBook.fire true))=
    (Poly.pass (-L)*Y).part (u.share pairMode)+Y.part (u.share pairBook.quiet)*L.part (u.share pairMode) at read
  simp only [show u.share pairMode=s from pair_share a b apart s roots,Names.quiet,Names.fire] at read
  exact read

end YM.Integration.WilsonPositionOriginalDressedQFactoredPair
