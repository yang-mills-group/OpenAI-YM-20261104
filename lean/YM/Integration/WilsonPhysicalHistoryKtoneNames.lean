import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Integration.WilsonMatrixTicketLanesNormalizedFleetHard

/-! Projection of the actual incumbent gas to the two elected original names. -/
noncomputable section
open scoped Classical BigOperators
namespace YM.Integration.WilsonPhysicalHistoryKtone
open Finset Function Marker Overlay Extra.Trajectories MergeProof MergeProof.Accent
variable {V:Type} [DecidableEq V] {J:Census V}

abbrev pairBook:=Stock.census Bool
def pairMode:pairBook.Mode:=⟨{false,true},Finset.mem_univ _⟩

def twoNames (a b:V)(different:a≠b)(mode:J.Mode)(seats:mode.val={a,b}):Names pairBook J where
  e:={
    toFun:=fun h=>cond h b a
    inj':=by intro u v he;cases u <;> cases v <;> simp_all}
  visible:=by
    intro s
    apply J.down mode.property _
    rw [seats]
    intro i hi
    obtain ⟨j,-,rfl⟩:=Finset.mem_image.mp hi
    cases j <;> simp

theorem pair_share (a b:V)(different:a≠b)(mode:J.Mode)(seats:mode.val={a,b}):
    (twoNames a b different mode seats).share pairMode=mode:=by
  apply Subtype.ext
  change ({false,true}:Finset Bool).image _=mode.val
  simp [seats,twoNames]

theorem marked_send {V' W:Type}[DecidableEq V'][DecidableEq W]{B:Census V'}{C:Census W}
    (u:Names B C)(s:B.Mode)(z:ℂ):
    u.restriction (Poly.send (u.share s) z)=Poly.send s z:=by
  apply Marker.Poly.ext (R:=B)
  intro j
  change (Poly.send _ z).part (u.share j)=(Poly.send s z).part j
  simp only [Poly.part_send,u.inj.eq_iff]

theorem foreign (a b:V)(different:a≠b)(mode:J.Mode)(seats:mode.val={a,b})(v:V)(left:v≠a)(right:v≠b)(z:ℂ):
    (twoNames a b different mode seats).restriction (Poly.send (J.fire v) z)=0:=by
  let u:=twoNames a b different mode seats
  apply Marker.Poly.ext (R:=pairBook)
  intro s
  change (Poly.send (J.fire v) z).part (u.share s)=0
  rw [Poly.part_send,if_neg]
  intro bad
  have hv:v∈(u.share s).val:=by rw [bad];simp [Census.fire]
  obtain ⟨h,-,he⟩:=Finset.mem_image.mp hv
  cases h
  · exact left he.symm
  · exact right he.symm

theorem marked_sum [Fintype V](a b:V)(different:a≠b)(mode:J.Mode)(seats:mode.val={a,b})(r:V→ℂ):
    (twoNames a b different mode seats).restriction (Mach J r)=
      Poly.send (pairBook.fire false) (r a)+Poly.send (pairBook.fire true) (r b):=by
  let u:=twoNames a b different mode seats
  have keep (v:V):u.restriction (Poly.send (J.fire v) (r v))=
      (if v=a then Poly.send (pairBook.fire false) (r a) else 0)+
      (if v=b then Poly.send (pairBook.fire true) (r b) else 0):=by
    by_cases left:v=a
    · subst v
      rw [if_pos rfl,if_neg different,add_zero]
      exact (u.fire false) ▸ marked_send u (pairBook.fire false) (r a)
    by_cases right:v=b
    · subst v
      rw [if_neg different.symm,if_pos rfl,zero_add]
      exact (u.fire true) ▸ marked_send u (pairBook.fire true) (r b)
    rw [if_neg left,if_neg right,zero_add]
    exact foreign a b different mode seats v left right (r v)
  change u.restriction (∑i,Poly.send (J.fire i) (r i))=_
  rw [map_sum]
  simp only [keep,Finset.sum_add_distrib]
  simp

end YM.Integration.WilsonPhysicalHistoryKtone
