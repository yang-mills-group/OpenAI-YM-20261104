import YM.Integration.WilsonMarkedIndependentMixedSpatial

/-! Restrict the incoming source only outside the actual compact set of
relative positions. Every occupied filed row and the entire squarefree
polynomial agree there, including every disconnected product. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedCompact
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}{D k:ι→ℕ}

def clipped (M:ℕ)(Y:Outerm G D):Outerm G D:=open Classical in
  fun q I=>if crestCard q I≤M then Y q I else 0

theorem subprice (q:ι → Cover){J I:Finset ι}(sub:J⊆I):crestCard q J≤crestCard q I:=by
  apply league_le
  intro i j
  exact leg_le terrain (fun s:I=>q s.val) ⟨i.val,sub i.property⟩ ⟨j.val,sub j.property⟩

theorem healthy [DecidableEq ι]{Y:Outerm G D}(M:ℕ)(old:Wellness k Y):Wellness k (clipped M Y):=by
  refine ⟨fun q=>?_,fun q I=>?_,fun q q' I agree=>?_⟩
  · unfold clipped;split
    · exact old.quiet' q
    · rfl
  · unfold clipped;split
    · exact old.level' q I
    · exact unstamped
  · have same:(fun i:I=>q i.val)=(fun i:I=>q' i.val):=funext fun i=>agree i.val i.property
    have size:crestCard q I=crestCard q' I:=congrArg (league terrain) same
    unfold clipped;rw [size];split
    · exact old.filial q q' I agree
    · rfl

theorem payment [DecidableEq ι](S:Schedule)(m M:ℕ)(ρ:ℝ)(Y:Outerm G D)(q:ι → Cover)(I:Finset ι)
    (known:cleared S m m ρ q I)(fits:crestCard q I≤M):
    levelsO (clipped M (reserveGood S m m ρ Y) q) I=levelsO (Y q) I:=by
  apply levels_g
  intro J sub
  rw [clipped,if_pos ((subprice q sub).trans fits),reserveGood,if_pos]
  exact fun a ha b hb ne=>known a (sub ha) b (sub hb) ne

end YM.Integration.WilsonMarkedIndependentMixedCompact
end
