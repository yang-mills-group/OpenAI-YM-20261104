import YM.MS.Graphical.Panels
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.ManyRoot
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Leading
import YM.MS.Dial.Slope

/-!
# Separated MS forest with actual mark charges and limits

The stock entries `u` can be *any* labels of the Booked B under consideration;
works for the actual filed clients too. Arbitrary pointwise separated pins. The
unmarked and 1-mark inputs in `Population` **are the integral and pole Pages**
from `Diagram.bulk`, `sectorMark`, transported into schedules by Parade. The
renormalized group at many pins is `C Z`. This uses the normalized connected
prescription (multi-mark graphs not multiplied by vacuum amplitudes; full uses
`bouquet`, the disjoint-subset exponential).

`gauge_cluster` and `screened` prove these are the filed results at finite IR
length (after UV limit, then specialization to 4d, i.e. finite part in a row
where pole has canceled). `collection_limits`, `identification` and
`full_regulation` also send the IR length bound to ∞, scalar closed readings,
again **on the same graphs**. Uses the library estimates for the final IR
limit on the complete filed sum, not requiring limits of arbitrarily split
summands. Formal across all orders. For further conclusions including coupling
and field conversion see e.g. the top-level calibrated gates applications.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock Rake Geo Latch Job High
open scoped Topology ContDiff Interval
open Land Local.Physical Outlook
variable {I : Type} [LinearOrder I] {G : Gauge} {n k : ℕ} {s : Finset I} {x : I→Tone.QP} {B : Deck G}


variable (X : Booked B) (u : I → Label B) (y : ℝ)



local notation "Z"=> allScale X u y x
local notation "C"=> Population.clusters
open Population

omit [LinearOrder I] in
lemma price_room (hx : Injective x) : (Z).Ready where
  bulkOK := fun k=> by
    obtain ⟨ht,h,hP⟩:= Diagram.ambient_bob G k
    exact mark_prices (all0 (clockMoon h)) (clockCap h) 4 ht.toll y
  cost := fun i k=> by
    obtain ⟨ht,h,hP⟩:= Diagram.mark_bob G (h:=(u i).h)
       (fun n=> Diagram.contracts_seed X _ (u i).item n) k
    convert mark_prices (clockMoon h) (clockCap h) _ ht.toll y using 1; swap; · rfl
    simp [allScale, budget, Diagram.rankRoom]; omega
  separated:=hx

theorem gauge_cluster (T : MS_Data G X) (hx : Injective x) : Vane.DOrd X (Tide.frameF Unit y) T u (fun i _=>x i)
    (physicalGroups (C (Z))) := by
  obtain h:= Population.groups (price_room X u y hx)
  unfold Vane.DOrd; rw [show approach (Tide.frameF Unit y) T=at4 ∘ (Z).bulk from ?_,
        show rowM (Tide.frameF Unit y) T ∘ u=(fun i=> at4 ∘ (Z).single i) from ?_]; exact h
  swap
  · -- bulk schedule
    funext k i t
    have hh:= (prom ((Diagram.income_bulk T).2 k) 4 t y)
    exact Eq.symm (congr_fun (fromLimit (t:=t) (bulkSchedule G y k) (Lift.congr
      (Outlook.live0 (Dock.gang (T.bulkOK k)).dost) hh.symm)) 0)
  funext j k i t
  have hh:= prom ((Diagram.income_mark T (u j).h (u j).item).2 k) (u j).h t y
  exact Eq.symm (congr_fun (fromLimit (t:=t) (singleSchedule X (u j) y k)
      (Lift.congr (Outlook.live0 (Dock.gang (T.markOK (u j).h (u j).item k)).dost) hh.symm)) 0)

theorem screened (T : MS_Data G X) (hx : Injective x) : ∀ t:ℝ,
    Lift ((C (Z)) s k t) (regularPart ((C (Z)) s k) t) ∧
    regularPart ((C (Z)) s k) t 0 = Dial.spine T u y x s k () t := by
  obtain hp:= perfect (gauge_cluster X u y T hx) (Dial.pin T u y hx); intro t; refine ⟨(formed (s:=s) (price_room X u y hx)).limit _,?_⟩; rw [← hp]; rfl



omit [LinearOrder I] in
lemma fixed_room (x : I→Tone.QP) (hx : Injective x) (y : ℝ) : Mesh (Tide.frameF Unit y) (fun p (_:Unit)=>x p) := by
    intro i j hi; have he:0<‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne hi)); refine ⟨⟨_,he,fun i=>?_⟩,⟨_,he,fun i=>?_⟩⟩ <;> simp [roots]

lemma collection_limits (T : MS_Data G X) (hx : Injective x) (s : Finset I) (k : ℕ) :
    Tendsto (fun t=> regularPart ((C (Z)) s k) t 0 []) atTop (𝓝 (Dial.book T u y x s k)):= by
  simp_rw [show ∀ t, regularPart _ t 0 = _ from (fun t:ℝ=> (screened X u y T (k:=k) (s:=s) hx t).2)]
  obtain hX | hV:= s.eq_empty_or_nonempty;
  · subst s; obtain he:= (Dial.pin T u y hx).1
    unfold Dial.book Vane.blade; rw [he]; exact (Fleet.allow_zero (I:=Unit) (G:=G) ()).1
  exact (Dial.reports u (fixed_room _ hx y) (Dial.pin T u y hx) hV k).1 ()

theorem identification (T : MS_Data G X) (hx : Injective x) : irRemoved X u y x = Dial.book T u y x ∧
    fullGraph X u y x = Dial.tour T u y x := by
  obtain he : irRemoved X u y x = Dial.book T u y x := funext fun i=>funext fun k=> (collection_limits X u y T hx i k).limUnder_eq
  exact ⟨he,congr_arg Puff.Mom.bouquet he⟩

-- no switching IR length across graphs necessary, even in the unconnected reading
theorem full_regulation (T : MS_Data G X) (hx : Injective x) :
    Tendsto (fun t=> Puff.Mom.bouquet (fun s i=> regularPart ((C (Z)) s i) t 0 []) s k) atTop
       (𝓝 (Dial.tour T u y x s k)) := Puff.Mom.Accord.select (f:=fun _ _ _=>_) (collection_limits X u y T hx) s k

/-- At this Links integration, UV removal (see also `Countered.cutRemoves`
for all tower length integrations on `integratePins`). -/
lemma deep_gain (hx : Injective x) (hp : 2 ≤ s.card) :
    let L := (Z).links (C (Z) s) (C (Z)) s k;
    ∀ᶠ z in dotty, ∀ t:ℝ, ∀ m, ∀ r:Legs (Shore G m),
      Tendsto (fun p:ℝ=>∫ i in p..t,L i z m r) atBot
          (𝓝 (runCloses y L 0 t z m r)) := by
  intro L; apply Eventually.mono (Countered.cutRemoves (multi_force_ok (price_room X u y hx) hp k)); intro z hz p; exact (hz p).2
end YM.MS.Graphical
