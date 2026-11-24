import YM.SignedWilsonExpansion.Warehouse.Wish
import YM.Integration.WilsonPhysicalWeakSameStation
/-! Purchase lit certified V-turns AND margins over the full punctured interval.
Do not change Φ when selecting estimates. Keep original extraction AND the full-track V agreement.
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.Integration.Election
open RG RG.Supply Extraction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot SignedWilsonExpansion.Homes
open WilsonPhysicalWeakWallStaff.ReStaff WilsonPositionThermometerCapStation WilsonPositionThermometerOrientedStation Next.UVStress Maxwell PhysMS MergeProof.East Next.Rank Next.Rank.East
open WilsonPhysicalWeakWallBooks (Shared)
open WilsonOriginalTwoFlatPublicBooks (Book)
open Function Filter Lattice Finset
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{R:Run G}{h:G.Simple}

namespace PRAY
variable (p:PRAY R h)
structure Wings (D:ℕ) where
    T:ℕ
    δ:ℝ
    pos:0<δ
    book : (s:{s:ℝ//0<s∧ s<δ})→Book p.last (l:=p.Y) p.H p.Z D T s.val
    trueB : ∀ s,∃ cap:D ≤ (p.staff s.val).1, Shared p.last (book s) (WilsonPhysicalWeakSameStation.trim cap (p.staff s.val).2)
lemma rod (D:ℕ) : Nonempty (Wings p D):=by
    obtain ⟨T,δ,hp,x,t⟩:= WilsonPhysicalWeakSameStation.books p.last h p.bliss p.staff p.rises ( p.roomy.mono fun i hi=>hi.2 ) D
    exact ⟨T,δ,hp,x,t⟩

namespace Wings
variable {p}{D m i:ℕ} (W:Wings p D)
local notation "C₀"=> R.family
abbrev OrderM:= {ρ:ℝ//0<ρ∧ρ<W.δ}
abbrev V (r:OrderM W) :=( W.book r ).V
abbrev lit (r:OrderM W):BeamT R.family:= ⟨(W.book r).k,(W.book r).W⟩
abbrev floorP (r:OrderM W):ℕ:= ( W.book r ).W.k
lemma sameV (r:OrderM W) : W.lit r = breadth (p.staff r.val) :=by
     obtain ⟨cap,u,t,y,_⟩:= W.trueB r
     exact BeamT.mk.injEq ..|>.mpr ⟨t,y⟩
-- Y rhythm
abbrev WingSpan (s:OrderM W)(g:Fin (D+1)) (Z:XSpace.Normalize.Store G) := (p.W Z s.val g).trans (W.V s g).symm
lemma ink (ρ:W.OrderM)(g:Fin (D+1))(v: (Bel R.family.book).Field g):
    ∃ Y:R.family.label g,Tendsto (fun i=>(W.lit ρ).microphone i g v) (p.Y:Filter _) (𝓝 Y) ∧ p.S.project g Y =W.V ρ g v:=by
      let A:= ( (W.book ρ).rows g ).arm true (W.V ρ g v); refine ⟨A.label,A.approaches.congr ?_,A.represents⟩; intro i
      unfold A V; rw [WilsonPositionProgramPublicStations.Pair.weak,LinearEquiv.symm_apply_apply]; unfold BeamT.microphone; rw [dif_pos ((Nat.le_of_lt_succ g.isLt).trans (W.book ρ).fits)]; rfl
open PhysMS.Frame
variable {ι:Type} (u:Filter ι) (age:ι→OrderM W) (near:Tendsto (fun i=>(age i).val) u Trace.Pilot.trail)
include near
lemma actualB : Tendsto (fun i=>(W.lit (age i)).k) u atTop ∧ ∀ᶠ i in u, (W.lit (age i)).Given (track p.f) p.H (age i).val := by
     have v:= ticketPV h p.last p.H p.staff p.rises p.roomy; refine ⟨(v.1.comp near).congr fun i=>congrArg BeamT.k (sameV W (age i)).symm,?_⟩; simp_rw [sameV]; exact near.eventually v.2
lemma provision (m:ℕ):
    ∀ᶠi in u,∀j:Fin (D+1),∀v:(Bel R.family.book).Field j,
    ‖(W.V (age i) j).symm (p.J (age i).val j v)-v‖≤WilsonPhysicalWeakWallBounded.cost R.family v*costHint m:=by
  filter_upwards [near.eventually p.roomy,near.eventually (p.rises.eventually_ge_atTop m)] with i sold live j v
  obtain ⟨cap,bought⟩:=W.trueB (age i)
  have issued:=WilsonPhysicalWeakSameStation.admitted p.last cap live h _ sold.2
  let K:= WilsonPhysicalWeakSameStation.trim cap (p.staff (age i).val).2
  have basis(k:Fin (Module.finrank ℂ ((Bel R.family.book).Field j))):
      ‖K.room.change j (Module.finBasis ℂ _ k)-Module.finBasis ℂ _ k‖≤costHint m:=
    ((issued.2.2 m le_rfl).2).2.2.2.2.2 ⟨j,k⟩
  have rooted:=WilsonPhysicalWeakWallBounded.atBasis (Module.finBasis ℂ _) (K.room.change j) (costHint m) basis v
  unfold K at rooted; rw [issued.2.1 j] at rooted
  rw [V,bought.2.2.2]; exact rooted

lemma pivots (Z:XSpace.Normalize.Store G): ∀ᶠ i in u,∀ j:Fin (D+1),
    Coherent p.H.spin p.H.spin j (W.WingSpan (age i) j Z) ∧ W.WingSpan (age i) j Z ((Bel R.family.book).unit j)= (Bel R.family.book).unit j:=by
  filter_upwards [near.eventually p.roomy] with i sold j
  obtain ⟨cap,bought⟩:=W.trueB (age i); let K:= WilsonPhysicalWeakSameStation.trim cap (p.staff (age i).val).2
  have issued:=WilsonPhysicalWeakSameStation.admitted p.last cap (Nat.zero_le _) h _ sold.2
  let E:= WilsonPositionPrescribedFrame.change p.last p.J Z j (age i).val
  have hm: Coherent p.H.spin p.H.spin j (K.room.change j) ∧ K.room.change j ((Bel R.family.book).unit j)= (Bel R.family.book).unit j:= ⟨((issued.2.2 0 le_rfl).2.2.2.2.2.1 j).1,((issued.2.2 0 le_rfl).2.2.2.2.2.1 j).2.1⟩ -- right tails
  have hX: W.WingSpan (age i) j Z= E.trans ( K.room.change j ):=by
     unfold K WingSpan V; rw [bought.2.2.2, issued.2.1]; rfl
  let φ:= WilsonPositionCorrectedCap.signed p.last p.J Z p.H.spin j (age i).val
  rw [hX]; refine ⟨⟨fun x=>?_, fun s x=>?_⟩,?_⟩
  · exact (congrArg (K.room.change j) (φ.stars x)).trans (hm.1.stars _)
  · exact (congrArg (K.room.change j) (φ.signed s x)).trans (hm.1.signed s _)
  exact (congrArg (K.room.change j) (WilsonPositionThermometerCorrectedUnit.corrected_unit p.last p.J Z j (age i).val)).trans hm.2
lemma oriented (Z:XSpace.Normalize.Store G)(j:Fin (D+1))(v:(Bel R.family.book).Field j):
    Tendsto (fun i=>W.WingSpan (age i) j Z v) u (𝓝 v):=by
  let y(i:ι):=( p.J (age i).val j ).symm (p.W Z (age i).val j v)
  have tends:Tendsto y u (𝓝 v):=by
     simp_rw [y,PRAY.W,WilsonPositionPrescribedFrame.positioned,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]; exact (WilsonPositionPrescribedLeading.applied p.last p.J Z p.VFrame.2 j v).comp near -- W scope W projection shadow
  let w: (Bel R.family.book).Field j→ℝ:= WilsonPhysicalWeakWallBounded.cost R.family (d:=j)
  have hw : Continuous w := by
      unfold w WilsonPhysicalWeakWallBounded.cost
      apply continuous_finsetSum _ fun i _=>?_
      change Continuous (fun v=>‖((Module.finBasis ℂ ((Bel R.family.book).Field j)).coord i) v‖)
      exact (LinearMap.continuous_of_finiteDimensional _).norm
  have cap:= ((hw.tendsto v).comp tends).eventually_lt_const (lt_add_one _)
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have prices:= cost_clears.const_mul (w v+1); rw [mul_zero] at prices
  obtain ⟨m,small⟩:=(prices.eventually_lt_const (half_pos ep)).exists
  have known:= provision W u age near m
  filter_upwards [cap,known, Metric.tendsto_nhds.mp tends (ε/2) (half_pos ep)] with i income ok direct
  have tagged:p.J ( age i ).val j (y i)=p.W Z (age i).val j v:=LinearEquiv.apply_symm_apply _ _
  have first:=ok j (y i); rw [tagged] at first
  have below : dist (W.WingSpan (age i) j Z v) (y i)<ε/2:=by
     rw [dist_eq_norm]; exact lt_of_le_of_lt (first.trans (mul_le_mul_of_nonneg_right income.le (cost_pos m).le)) small
  linarith [dist_triangle (W.WingSpan (age i) j Z v) (y i) v]
end Wings
end PRAY
end YM.Integration.Election
