import YM.Integration.WilsonIndependentMatchedOwnHomePinnedPlacement
import YM.Integration.WilsonIndependentMatchedOwnHomeIntegratedMaster

/-! Coordinate the complete pinned ordinary product with the two-top source
on its own vacuum and the same finite Rarity menu at both cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomePinnedRoster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedCoverProfile (word)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedOwnHomePinnedPlacement (moved)
open WilsonIndependentMatchedOwnHomePinnedMaster (point)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonSeparatedPrefixMovingPinHearing (hear shiftHom)
open WilsonPositionProgramPinnedHearthHistory (pin)
variable {G:Gauge}{n e:ℕ}{E:Credit}

theorem gathered {p:Cover}(P:Fin (n+1)→Era G ℝ):
    shifted (MassP G ℝ n P) p=MassP G ℝ n (fun i=>shifted (P i) p):=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change shifted (agateV _ _) p=agateV _ _
    rw [WilsonSeparatedPrefixMovingPinProduct.grouped,ih (Fin.tail P)]
    rfl

def translated (Q:Fin (n+1)→SealR G)(φ:Wilt Q)(x:Point4):Wilt Q:=fun i=>moved (φ i) x

theorem bough (Q:Fin (n+1)→SealR G)(φ:Wilt Q)(v:Point4)(Z y:ℝ)(B:Fin (n+1)→ℝ)(inlet:Bough Q φ y Z B):
    Bough Q (translated Q φ v) y (Z+‖v‖) B:=by
  have width:Z ≤ Z+‖v‖:=le_add_of_nonneg_right (norm_nonneg _)
  refine ⟨inlet.pos.trans width,?_,?_,inlet.room.trans width,?_⟩
  · intro i
    refine ⟨(inlet.lanes i).1,?_⟩
    intro j hj w x
    exact (WilsonIndependentFittedExteriorProfile.shifted (φ i).ψ v w x) ▸ (inlet.lanes i).2 j hj w (-v+x)
  · intro i
    change ‖v‖+(φ i).radius ≤ _
    linarith only [inlet.rents i]
  · intro i j distinct a ha b hb
    have inside:=inlet.seats i j distinct (-v+a) (WilsonIndependentMatchedOwnHomePinnedPlacement.support _ _ ha)
      (-v+b) (WilsonIndependentMatchedOwnHomePinnedPlacement.support _ _ hb)
    rw [dist_add_left] at inside
    exact (inv_anti₀ (zero_lt_one.trans_le inlet.pos) width).trans inside

theorem placed (A:Levels G)(O:ChartRatio G)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)
    (m c K N:ℕ)(enrolled:c ≤ K)(y:ℝ)(o:CellR)(s:Cover):
    shifted (Ashore Q A O φ X m K N y o) (pin A.S c K s)=
      Ashore Q A O (translated Q φ (paceT A.S m c • actualW s)) X m K N y o:=by
  unfold Ashore
  rw [gathered]
  apply congrArg (MassP G ℝ n)
  funext i
  let P:=polarP A O (Q i).ans (Q i).path N m K (X i)
  change shifted (word P (φ i) (paceT A.S m K) y o (Q i).h) (pin A.S c K s)=
    word P (moved (φ i) _) (paceT A.S m K) y o (Q i).h
  rw [WilsonIndependentMatchedOwnHomePinnedPlacement.original _ _ _ _ (pace_pos ..),
    WilsonIndependentMatchedOwnHomePinnedPlacement.pin A.S m c K enrolled s]

theorem original (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(b:Herit Q)
    (m c old K N:ℕ)(enrolled:c ≤ K)(ear:old ≤ m)(cut:m ≤ K)(y:ℝ)(o:CellR)(s:Cover):
    point R Q φ b m c old K N y o s=
        ground (stopped R.draws R.paid Q (translated Q φ (paceT R.draws.S m c • actualW s)) b m K N old y o):=by
  unfold WilsonIndependentMatchedOwnHomePinnedMaster.point hear
  change ground (cruises _ _ _ _ _ _ (shifted _ _))=_
  rw [placed _ _ Q φ _ m c K N enrolled y o s,cruisesMore R.draws R.paid _ ear cut]
  rfl

end YM.Integration.WilsonIndependentMatchedOwnHomePinnedRoster
end
