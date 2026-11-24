import YM.Integration.WilsonCenteredFourSpatialNodes
import YM.Integration.WilsonPublicForkMoving
import YM.Integration.WilsonPublicForkLabels

/-! The moving reflected two-input salary from the already chosen public
filter, at every physical view and with both positioned leaves retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSingleSalary
open Function Finset Filter Set Climb Table Spec OPE OPE.Orbits OPE.Prescription OPE.Log
open EveryPhase OPE.Nesting Trace Trace.Pilot Trace.Terrace RG17 PhysMS PhysMS.Frame
open GapsContact GapsContact.Seams OPE.Levy Extraction Maxwell XSpace
open GapsContact.Ascent Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open WilsonThermometerWeakMovingCorner WilsonThermometerWeakPairClock OPE.Arboreal XSpace.Normalize
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
universe u
private abbrev I₀ := {i:Fin 5 // i∈WilsonThermometerWeakPairRooms.near}
local notation "pair" => WilsonThermometerWeakPairRooms.near
local notation "sites" => WilsonThermometerWeakPairFork.position
local notation "seat" => (WilsonPublicForkLabels.index (I:=I₀))
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
private def homes (x y:E4)(i:I₀):E4:=if i.1=2 then x else y

private theorem layout (r t:ℝ)(x y z:E4):
    crop (sites r t x y z) pair=(fun i=>r • homes x y i):=by
  funext ⟨i,h⟩
  rcases (by simpa [WilsonThermometerWeakPairRooms.near] using h : i=2 ∨ i=3) with rfl|rfl <;> rfl

private theorem room {x y:E4}{M δ:ℝ}(hx:‖x‖≤M)(hy:‖y‖≤M)(xy:δ≤‖x-y‖):
    (∀i,‖homes x y i‖≤M) ∧ ∀i j,i≠j→δ≤‖homes x y i-homes x y j‖:=by
  constructor
  · intro i;unfold homes;split <;> assumption
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ diff
    rcases (by simpa [WilsonThermometerWeakPairRooms.near] using hi : i=2 ∨ i=3) with rfl|rfl <;>
      rcases (by simpa [WilsonThermometerWeakPairRooms.near] using hj : j=2 ∨ j=3) with rfl|rfl
    · exact (diff rfl).elim
    · exact xy
    · change δ≤‖y-x‖;rwa [norm_sub_rev]
    · exact (diff rfl).elim

private theorem read {d:I₀→ℕ}{e h:ℕ}(q:Viewers F)(x:I₀→E4)(v:Labels S d)(z:E4)(w:S.Field e)
    (sep:Injective (beside x (sole z)))(ext:Injective (beside (sole (0:E4)) (sole z))):
    formula F Q (x ∘ seat) 0 (d:=d ∘ seat) (fun i=>v (seat i)) (sole z) (sole w:Labels S (fun _:Unit=>e)) h q =
    formula F Q x 0 v (sole z) (sole w:Labels S (fun _:Unit=>e)) h q:=by
  let b:Labels S (fun _:Unit=>e):=sole w
  rw [formula,formula,←packet_read F Q _ _ _ _ _ q h ext,←packet_read F Q _ _ _ _ _ q h ext,WilsonPublicForkLabels.grouped F Q]
  exact congrArg (fun a=>a-upon (spectator F q) h 0 (sole z) b (Q.packet h x v 0))
    (whole_perm (spectator F q) (d:=d) seat (Equiv.refl Unit) (spectate F q) sep)

theorem original {simple:G.Simple}{L:Almanac F}(H:Roll.{u} F simple L)
    {l:Ultrafilter (ℕ×ℕ)}{arch:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F l arch Y)(ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    (bank:LogTrace F Q.port)(book:Foundation F Q)(J:ℝ→tower S)(lead:Leading F J):
    WilsonThermometerWeakPairSector.Salary F Q J:=by
  intro V g hg I _ d e h v w view M δ m0 d0
  choose A C cp shell using fun i=>WilsonPublicForkMoving.original (I:=I₀) F H bliss ledger Q.spans bank Q book J V lead g hg
    (d i ∘ seat) (e i) h (fun j=>v i (seat j)) (w i) (view i) m0 d0
  refine ⟨∑i,A i,?_⟩
  intro o ε ep B paid
  dsimp only
  apply eventually_all.mpr;intro i
  have ax:A i≤∑j,A j:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have budget:A i+o+1≤B:=by omega
  have rebate:=WilsonThermometerWeakPairAxes.refund simple g hg (cp i) (A i) o h B budget ep
  have gap:=WilsonThermometerWeakPairDetector.gap simple g hg (B:=B) (by omega) (M:=M) d0
  filter_upwards [shell i B,rebate,gap,ordered simple g hg B,self_mem_nhdsWithin] with r earn restore clear rt rp
  intro x y z hx hy hz fz xy
  have pairroom:=room hx hy xy
  have gates:=WilsonThermometerWeakPairDistinct.actual (show 0<r from rp) rt d0 hx hy fz xy clear
  let t:=scale g B r
  let X:=crop (sites r t x y z) pair
  have bill:=earn (homes x y) z pairroom.1 hz fz pairroom.2 clear
  rw [WilsonPublicForkLabels.slots,←layout r t x y z] at bill
  have same:=congrArg (fun a:ℂ=>‖a‖) (read F Q (e:=e i) (h:=h) (view i) X (born J r (v i)) (t • z)
    (far F J (e i) t (w i)).2 gates.2.1 gates.2.2.2)
  exact same.symm.trans_le (bill.trans restore)


end YM.Integration.WilsonCenteredFourSingleSalary
