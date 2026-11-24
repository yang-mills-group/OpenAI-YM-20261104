import YM.Integration.WilsonMeasuredSignedActionOwnedRows
import YM.Integration.WilsonPositionThermometerCapStation
import YM.Integration.WilsonMovingForkWeakWall

/-! Signed rotations and the unit of the submitted Vane at each sufficiently small physical home. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCapAxes
open Function Filter Set Extraction Table Spec Lattice RG Wilson
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot Next.UVStress Climb MergeProof.East
open WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (simple : G.Simple) {l : Ultrafilter (ℕ×ℕ)}

open Trace.Over
open WilsonMovingForkReporterFilament
open WilsonMeasuredPublicEntranceNativeFrame (Priced)
variable {H:(Bel C.book).Hierarchy}{z:Arch C}

open Spin PhysMS PhysMS.Frame WilsonPositionThermometerOrientedStation

def Honest (j:ℕ)(U:Spin.change S j):Prop:=
  ∀(Q:tower S),obedient F H Q j → Coherent H.spin H.spin j ((Q j).trans U.symm) ∧
    ((Q j).trans U.symm) ((Bel C.book).unit j)=(Bel C.book).unit j

structure Signed {k:ℕ}(W:Vane C k)(D:ℕ):Prop where
  fits:D≤k
  filed:∀d:Fin (D+1),
    let slot:Fin (k+1):=⟨d.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.isLt).trans fits)⟩
    ∃U:Spin.change S d, Priced l (fun p=>W.wheel.atCut p slot) U ∧ Honest F (H:=H) d U

include simple in
theorem along {cap:ℕ→ℕ}(V:∀i,Vane C (cap i))(c:Course V)(J:Scaling S)
    (script:Scribe f J (c.filed) z F.sector l F.room.kernel H)(D:ℕ):
    ∀ᶠ j:ℕ in atTop,Signed F (H:=H) (l:=l) (V (c.index j)) D:=by
  obtain ⟨Y,book⟩:=script.meters
  have rows:=eventually_all.mpr fun d:Fin (D+1)=>(book.terminal d).and (script.monorail.units d)
  filter_upwards [eventually_ge_atTop D,rows] with j roof price
  refine ⟨roof.trans (c.enough j),fun d=>?_⟩
  have ok:d.val≤j:=(Nat.le_of_lt_succ d.isLt).trans roof
  obtain ⟨⟨lands,moves⟩,motion,unit⟩:=price d
  have copy:heightV c.filed j d=fun p=>(V (c.index j)).wheel.atCut p
      ⟨d.val,Nat.lt_succ_of_le (ok.trans (c.enough j))⟩:=by
    funext p
    rw [heightV,dif_pos ok]
    rfl
  refine ⟨J.U j d,⟨Y d j,copy ▸ lands,moves⟩,fun Q aligned=>?_⟩
  have a:=obedient_realH F simple H aligned
  have inv:=flips motion
  constructor
  · constructor
    · intro x
      exact (congrArg (J.U j d).symm (a.2 x)).trans (inv.stars _)
    · intro i x
      exact (congrArg (J.U j d).symm (a.1 i x)).trans (inv.signed _ _)
  · change (J.U j d).symm (Q d ((Bel C.book).unit d))=_
    rw [aligned.unit,←unit,LinearEquiv.symm_apply_apply]

include simple in
theorem original {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))
    (made:C.Makes)(bliss:Bliss F l z H)(radius:∀s,(V s).wheel.r=s.val)
    (checked:∀s,(V s).checked f H (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun j=>(s j).val) atTop (𝓝 0) →
      Tendsto (fun j=>cap (s j)) atTop atTop ∧ Tendsto (fun j=>(V (s j)).k) atTop atTop)(D:ℕ):
    ∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r → Signed F (H:=H) (l:=l) (V s) D:=by
  by_contra no
  obtain ⟨rr,shrink,bad⟩:=contradictionTrail _ no
  have excluded(i:ℕ):∃s:Set.Ioc (0:ℝ) δ,s.val=rr i ∧ ¬Signed F (H:=H) (l:=l) (V s) D:=by
    by_contra exactNone
    apply (bad i).2
    intro s h
    by_contra missing
    exact exactNone ⟨s,h,missing⟩
  choose s place outside using excluded
  have small:Tendsto (fun j=>(s j).val) atTop (𝓝 0):=by
    simpa only [place] using shrink.mono_right nhdsWithin_le_nhds
  obtain ⟨levels,old⟩:=calendar s small
  have phys:Tendsto (fun j=>(V (s j)).wheel.r) atTop (𝓝 0):=by simpa only [radius] using small
  obtain ⟨c⟩:=WilsonMovingForkReporterFilament.selection (fun j=>V (s j)) levels phys
  obtain ⟨J,_time,script,_site,_row⟩:=WilsonMovingForkReporterFilament.mounted F (fun j=>V (s j)) c
    made simple bliss old (fun j=>checked (s j))
  obtain ⟨j,valid⟩:=(along F simple (fun j=>V (s j)) c J script D).exists
  apply outside (c.index j)
  exact valid


end YM.Integration.WilsonPhysicalStationMixedWickCapAxes
end
