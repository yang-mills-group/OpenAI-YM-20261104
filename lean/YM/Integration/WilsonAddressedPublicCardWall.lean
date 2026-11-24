import YM.Integration.WilsonThermometerUnitFilingFourWeakWall
import YM.GapsContact.Slab.Along

/-! The observed weak cabinet and its full inverse are issued together
on each reporting radius of the original elected phase. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonAddressedPublicCardWall
open Function Filter Set Extraction Table Spec Lattice RG Wilson
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot Next.UVStress Climb MergeProof.East
open WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (simple : G.Simple) {l : Ultrafilter (ℕ×ℕ)}
variable {H : (Bel C.book).Hierarchy}
/-- The selected weak field, its physical card width and every earlier block ratio. -/
structure Purchased (F : Final C f S) (H : (Bel C.book).Hierarchy)
    (l : Ultrafilter (ℕ×ℕ)) (r : ℝ) (c : ℕ) : Prop where
  station : ∃ (k : ℕ) (cap : c ≤ k) (W : Vane C k), W.checked f H k ∧ W.wheel.r = r ∧ c ≤ W.k ∧
    (0 < purchaseWidth W ∧ 20*C.S.a (purchaseWidth W) < C.S.a (purchaseWidth W-1) ∧
      C.S.a (purchaseWidth W-1) < r*LogV r/32) ∧
    (C.S.a (purchaseWidth W) ≤ r*(C.path.levels.clock.monitor W.k)^5 ∧
      ∀i:ℕ,i ≤ W.k → ((C.S.block i).val:ℝ) ≤ C.path.levels.clock.monitor W.k) ∧
    ∀ d : Fin (c+1), ∃ T : Spin.change S d,
      (∀ v:S.Field d, ‖T.symm v‖ ≤ dock r*cost F d r v) ∧ ∀ a : (Bel C.book).Field d,
      ∃ y : Arm C S (l:Filter _) d (T a),
        (∀ z, y.source z = W.wheel.atCut z ⟨d,(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ d.isLt) (Nat.lt_succ_of_le cap))⟩ a) ∧
        ∀ᶠ z : ℕ×ℕ in f.fuse, OPE.Cards.PaidAt C.S z.1 z.2 (purchaseWidth W)
          (C.beta z.1 z.2) (dock r*‖a‖) (C.O z.1 z.2 (y.source z) 0)

include simple in
theorem original {arch : Arch C} (bliss : Bliss F l arch H) (c : ℕ) :
    ∀ᶠ r in trail, Purchased F H l r c := by
  by_contra no
  obtain ⟨s,hs,excluded⟩ := contradictionTrail _ no
  obtain ⟨m,hm,X,hX,V,script⟩ := bliss.picks s (hs.mono_right nhdsWithin_le_nhds)
    (fun n => (excluded n).1)
  obtain ⟨Y,book⟩ := script.meters
  choose B fee using fun d : Fin (c+1) => WilsonThermometerUnitFilingFourWeakWall.quote F simple book d
  choose A _ fit using fun d : Fin (c+1) => window_prices F simple script.monorail d.val 1 1 one_pos
  have growing : Tendsto (fun k => dock (X.r k)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=X))
  have ranks := eventually_all.mpr fun d : Fin (c+1) =>
    (((fee d).and (book.terminal d)).and (growing.eventually_ge_atTop (B d))).and
      ((fit d).and (growing.eventually_ge_atTop (A d)))
  have widths:=book.growth.eventually ((inch_upper C.path.levels simple bliss.budgets).and
    (block_upper C.path.levels simple bliss.budgets))
  obtain ⟨k,cap,coarse,room,⟨sharp,blocks⟩,prices⟩ := ((eventually_ge_atTop c).and
    ((book.growth.eventually_ge_atTop c).and ((overhang book simple bliss.budgets).and (widths.and ranks)))).exists
  apply (excluded (m k)).2
  rw [← show X.r k = s (m k) from congr_fun hX k]
  have positive:0<(V k).b:=lt_trans (by norm_num : (0:ℝ)<5) (book.season k).1.high.1
  have fee:= (div_le_iff₀ (C.S.a_pos (V k).k)).mp (sharp (V k).b positive)
  have purchase:C.S.a (purchaseWidth (V k)) ≤ X.r k*(C.path.levels.clock.monitor (V k).k)^5:=by
    rw [←(book.season k).2]
    change _ ≤ (C.S.a (V k).k*Next.Rank.Station.mag C.path.levels (V k).b (V k).k)*_
    calc
      _ ≤ _ := fee
      _ = _ := by ring
  refine ⟨k,cap,V k,(book.season k).1,(book.season k).2,coarse,room,⟨purchase,blocks⟩,fun d => ?_⟩
  have ok : d.val ≤ k := (Nat.le_of_lt_succ d.isLt).trans cap
  obtain ⟨⟨⟨pay,lands,files⟩,funded⟩,win,lower⟩ := prices d
  refine ⟨X.U k d,?_,fun a => ?_⟩
  · intro a
    have available:‖(X.U k d).symm a‖ ≤ A d*cost F d (X.r k) a:=by
      simpa only [LinearEquiv.apply_symm_apply] using (win ((X.U k d).symm a)).1
    exact available.trans (mul_le_mul_of_nonneg_right lower (cost_pos F ..))

  have ev : Continuous (fun A : (Bel C.book).Field d →L[ℂ] C.label d => A a) :=
    continuous_id.clm_apply continuous_const
  let cut := fun z : ℕ×ℕ => heightV V k d z a
  let y : Arm C S (l:Filter _) d (X.U k d a) :=
    ⟨cut,Y d k a,ev.continuousAt.tendsto.comp lands,(files a).symm⟩
  refine ⟨y,fun z => ?_,?_⟩
  · simp only [y,cut,heightV,dif_pos ok]
  · filter_upwards [pay a] with z q
    exact ⟨q.live,q.ticket,q.mark.trans (mul_le_mul_of_nonneg_right funded (norm_nonneg _))⟩

end YM.Integration.WilsonAddressedPublicCardWall
end
