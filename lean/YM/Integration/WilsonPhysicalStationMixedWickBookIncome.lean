import YM.Integration.WilsonMeasuredSignedActionOwnedRows
import YM.Integration.WilsonMovingForkWeakWall

/-! The actual filed Vane at each own physical home funds its complete measured inverse. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickBookIncome
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

structure Inverse {k:ℕ}(W:Vane C k)(r:ℝ)(D:ℕ):Prop where
  fits:D≤k
  filed:∀d:Fin (D+1),
    let slot:Fin (k+1):=⟨d.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.isLt).trans fits)⟩
    ∃U:Spin.change S d, Priced l (fun p=>W.wheel.atCut p slot) U ∧
      ∀v:S.Field d,‖U.symm v‖≤dock r*cost F d r v

include simple in
theorem along {cap:ℕ→ℕ}(V:∀i,Vane C (cap i))(c:Course V)(J:Scaling S)
    (script:Scribe f J (c.filed) z F.sector l F.room.kernel H)(D:ℕ):
    ∀ᶠ j:ℕ in atTop,Inverse F (l:=l) (V (c.index j)) ((V (c.index j)).wheel.r) D:=by
  obtain ⟨Y,book⟩:=script.meters
  choose A _ rents using fun d:Fin (D+1)=>window_prices F simple script.monorail d.val 1 1 one_pos
  have growing:Tendsto (fun j=>dock (J.r j)) atTop atTop:=
    tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=J))
  have rank:=eventually_all.mpr fun d:Fin (D+1)=>
    ((book.terminal d).and (rents d)).and (growing.eventually_ge_atTop (A d))
  filter_upwards [eventually_ge_atTop D,rank] with j roof prices
  have atRadius:(V (c.index j)).wheel.r=J.r j:=(book.season j).2
  rw [atRadius]
  refine ⟨roof.trans (c.enough j),fun d=>?_⟩
  have ok:d.val≤j:=(Nat.le_of_lt_succ d.isLt).trans roof
  obtain ⟨⟨⟨lands,files⟩,rent⟩,money⟩:=prices d
  have copy:heightV c.filed j d=fun p=>(V (c.index j)).wheel.atCut p
      ⟨d.val,Nat.lt_succ_of_le (ok.trans (c.enough j))⟩:=by
    funext p
    rw [heightV,dif_pos ok]
    rfl
  refine ⟨J.U j d,⟨Y d j,copy ▸ lands,files⟩,fun v=>?_⟩
  have fare:‖(J.U j d).symm v‖≤A d*cost F d (J.r j) v:=by
    simpa only [LinearEquiv.apply_symm_apply] using (rent ((J.U j d).symm v)).1
  exact fare.trans (mul_le_mul_of_nonneg_right money (cost_pos F ..))

include simple in
theorem original {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))
    (made:C.Makes)(bliss:Bliss F l z H)(radius:∀s,(V s).wheel.r=s.val)
    (checked:∀s,(V s).checked f H (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun j=>(s j).val) atTop (𝓝 0) →
      Tendsto (fun j=>cap (s j)) atTop atTop ∧ Tendsto (fun j=>(V (s j)).k) atTop atTop)(D:ℕ):
    ∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r → Inverse F (l:=l) (V s) r D:=by
  by_contra no
  obtain ⟨rr,shrink,bad⟩:=contradictionTrail _ no
  have excluded(i:ℕ):∃s:Set.Ioc (0:ℝ) δ,s.val=rr i ∧ ¬Inverse F (l:=l) (V s) (rr i) D:=by
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

theorem appointed {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))(prior:ℝ→PhysMS.tower S)
    (D:ℕ)(stock:∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r→Inverse F (l:=l) (V s) r D):
    ∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r→∀d:Fin (D+1),∀a:S.Field d,
      ‖(WilsonMeasuredPublicEntranceNativeFrame.atRadius l cap V prior r d).symm a‖≤dock r*cost F d r a:=by
  filter_upwards [stock] with r paid s eq
  subst r
  have bill:=paid s rfl
  intro d a
  obtain ⟨U,file,every⟩:=bill.filed d
  have bound:d.val≤cap s:=(Nat.le_of_lt_succ d.isLt).trans bill.fits
  rw [WilsonMeasuredPublicEntranceNativeFrame.at_site l cap V prior s bound file]
  exact every a

end YM.Integration.WilsonPhysicalStationMixedWickBookIncome
end
