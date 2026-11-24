import YM.Integration.WilsonMeasuredPublicEntranceNativeFrame
import YM.Integration.WilsonMovingForkReporterFilament
import YM.Integration.WilsonThermometerUnitFilingFourWeakWall
/-! The original reflected salary and field limit on a preappointed real
Wilson reporter, retaining its own cut maps. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionOwnedRows
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

structure Rows {k:ℕ}(W:Vane C k)(r:ℝ)(c:ℕ):Prop where
  fits:c≤k
  filed:∀d:Fin (c+1),
    let slot:Fin (k+1):=⟨d.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.isLt).trans fits)⟩
    ∃U:Spin.change S d, Priced l (fun p=>W.wheel.atCut p slot) U ∧
      ∀x:(Bel C.book).Field d,∃y:Arm C S (l:Filter _) d (U x),
        (∀p,y.source p=W.wheel.atCut p slot x) ∧
        ∀ᶠp:ℕ×ℕ in f.fuse,OPE.Cards.PaidAt C.S p.1 p.2 (purchaseWidth W)
          (C.beta p.1 p.2) (dock r*‖x‖) (C.O p.1 p.2 (y.source p) 0)

include F simple in
theorem along {cap:ℕ→ℕ}(V:∀i,Vane C (cap i))(c:Course V)(J:Scaling S)
    (script:Scribe f J (c.filed) z F.sector l F.room.kernel H)(D:ℕ):
    ∀ᶠ j:ℕ in atTop,Rows (f:=f) (S:=S) (l:=l) (V (c.index j)) ((V (c.index j)).wheel.r) D:=by
  obtain ⟨Y,book⟩:=script.meters
  choose B fee using fun d:Fin (D+1)=>WilsonThermometerUnitFilingFourWeakWall.quote F simple book d
  have growing:Tendsto (fun j=>dock (J.r j)) atTop atTop:=
    tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=J))
  have rank:=eventually_all.mpr fun d:Fin (D+1)=>
    ((fee d).and (book.terminal d)).and (growing.eventually_ge_atTop (B d))
  filter_upwards [eventually_ge_atTop D,rank] with j roof prices
  have atRadius:(V (c.index j)).wheel.r=J.r j:=(book.season j).2
  rw [atRadius]
  refine ⟨roof.trans (c.enough j),fun d=>?_⟩
  have ok:d.val≤j:=(Nat.le_of_lt_succ d.isLt).trans roof
  obtain ⟨⟨pay,lands,files⟩,funded⟩:=prices d
  have copy:heightV c.filed j d=fun p=>(V (c.index j)).wheel.atCut p
      ⟨d.val,Nat.lt_succ_of_le (ok.trans (c.enough j))⟩:=by
    funext p
    rw [heightV,dif_pos ok]
    rfl
  refine ⟨J.U j d,⟨Y d j,copy ▸ lands,files⟩,fun x=>?_⟩
  let source:=fun p=>heightV c.filed j d p x
  have ev:Continuous (fun A:(Bel C.book).Field d→L[ℂ] C.label d=>A x):=continuous_id.clm_apply continuous_const
  have conv:Tendsto source (l:Filter _) (𝓝 (Y d j x)):=
    ev.continuousAt.tendsto.comp lands
  refine ⟨⟨source,Y d j x,conv,(files x).symm⟩,fun p=>?_,?_⟩
  · exact congrArg (fun A:(Bel C.book).Field d→L[ℂ] C.label d=>A x) (congrFun copy p)
  · filter_upwards [pay x] with p real
    exact ⟨real.live,real.ticket,real.mark.trans (mul_le_mul_of_nonneg_right funded (norm_nonneg x))⟩

include F simple in
theorem original {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))
    (made:C.Makes)(bliss:Bliss F l z H)(radius:∀s,(V s).wheel.r=s.val)
    (checked:∀s,(V s).checked f H (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun j=>(s j).val) atTop (𝓝 0) →
      Tendsto (fun j=>cap (s j)) atTop atTop ∧ Tendsto (fun j=>(V (s j)).k) atTop atTop)(D:ℕ):
    ∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r → Rows (f:=f) (S:=S) (l:=l) (V s) r D:=by
  by_contra no
  obtain ⟨rr,shrink,bad⟩:=contradictionTrail _ no
  have excluded(i:ℕ):∃s:Set.Ioc (0:ℝ) δ,s.val=rr i ∧ ¬Rows (f:=f) (S:=S) (l:=l) (V s) (rr i) D:=by
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
  simpa only [radius,place] using valid

end YM.Integration.WilsonMeasuredSignedActionOwnedRows
end
