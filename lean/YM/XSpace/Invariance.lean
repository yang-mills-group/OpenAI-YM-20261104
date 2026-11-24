import YM.XSpace.Nested
import YM.XSpace.Talking

/-!
# Position scheme invariance under formal re-announcements

At finite regulator too. Allows precomposing with power-divergent
frame in positive orders (doesn't even require polynomial-L cap). No
pushing these multipliers into small residuals!
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick PowerSeries
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d:ℕ} {A:Screen G d}
namespace Fray
variable (D:Fray A) (H:A.Prepared)
private lemma same_shift (x y:Change G d) (h:stand x=stand y): x=y:= by
  apply Subtype.ext; ext1 p; exact add_left_cancel (DFunLike.congr_fun h p: p+ x.val p=p+ y.val p)

lemma no_reset {P Q:Reports G d} (h:Executed D H P) (hp:P 0=Q 0): Executed D H Q:=by
  let u:=D.Lays H P; let v := D.Lays H Q; have h0 : u 0=v 0:=by unfold u v; rw [leads,leads,hp]
  have he : Bijective (stand (u 0)):= (Module.End.isUnit_iff _).1 ((const_deck u) ▸ ((isUnit_iff_constantCoeff (φ:=deck u)).mp h.1.seed))
  have hv : SetEq A (v 0) (Q 0):= by
    have hz:= show A.D (realm (deck u) P 0)=_ from h.2.1 0; rw [if_pos rfl, rest,coeff_zero_eq_constantCoeff_apply,const_deck,hp,h0] at hz; exact hz
  have ht: Bijective (slope A (v 0) (Q 0)):=hp ▸ (h0 ▸ (show Bijective _ from h.2.2))
  refine ⟨formal_deck v (h0 ▸ he), ?_, ht⟩; unfold v at hv ht; rw [leads] at hv ht; exact Screen.solving A _ Q hv ht

theorem invariance (P:Reports G d) (S:Guard G d) (h: Formal S) (he:constantCoeff S=1) (H':Executed D H P):
    fit D H P=fit D H (realm S P):=by
  let Q:=realm S P; let v:= Lays D H Q; let a:= Lays D H P
  have hv: Q 0=P 0:= by unfold Q; rw [rest, coeff_zero_eq_constantCoeff_apply,he]; rfl
  have hg:= no_reset D H H' (Q:=Q) hv.symm
  obtain ⟨k,hk⟩:= (Formal.product (Y:=deck v) h hg.1).actions
  have hu : k 0=a 0:= by
    apply same_shift; rw [← const_deck, ← hk,map_mul,he,one_mul,const_deck]; unfold a v; rw [leads, leads,hv]
  have hh : realm (deck k) P=realm (deck v) Q:= by rw [← hk, ← parlance]
  have hkh : A.Solved k P:= fun l=> by rw [hh]; exact hg.2.1 l
  rw [← show realm (deck k) P=fit D H (realm S P) from hh, show k=a from Eq.symm (A.shift_unique P _ _ hu.symm H'.2.1 hkh H'.2.2.1)]; rfl
end Fray
end YM.XSpace.Normalize
