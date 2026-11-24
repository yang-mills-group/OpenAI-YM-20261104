import YM.Integration.WilsonMeasuredPublicEntranceNativeLeading

/-! All original two-home surveys use the dates already appointed at each radius.
Their finite signed receipts select one physical leading tower on that same course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeAppointment
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWheelOffers
open WilsonPhysicalWeakWallBounded (atBasis slot head cost)
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open WilsonMeasuredPublicEntranceNativeStaff
open WilsonMeasuredPublicEntranceNativeLeading WilsonMeasuredPublicEntranceNativeFrame
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{H:(Bel C.book).Hierarchy}
  {l:Ultrafilter (ℕ×ℕ)}{z:Trace.Terrace.Arch C}(F:Final C f S)(prior:ℝ→tower S)
  {radius:ℝ}(horizon:Set.Ioc (0:ℝ) radius→ℕ)(survey:∀s,Vane C (horizon s))

theorem original (lead:Leading F prior)(made:C.Makes)(simple:G.Simple)(bliss:Bliss F l z H)
    (wide:0<radius)(located:∀s,(survey s).wheel.r=s.val)
    (checked:∀s,(survey s).checked f H (horizon s))
    (calendar:∀xs:ℕ→Set.Ioc (0:ℝ) radius,Tendsto (fun i=>(xs i).val) atTop (𝓝 0) →
      Tendsto (fun i=>horizon (xs i)) atTop atTop ∧ Tendsto (fun i=>(survey (xs i)).k) atTop atTop):
    ∃J:ℝ→tower S,Leading F J ∧ localCost trail (atRadius l horizon survey prior) J ∧
      ∀m,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l horizon survey prior r) (J r) m:=by
  apply WilsonMeasuredPublicEntranceNativeLeading.original
  intro m
  by_contra missing
  obtain ⟨xs,fall,bad⟩:=contradictionTrail _ missing
  have zero:Tendsto xs atTop (𝓝 0):=fall.mono_right nhdsWithin_le_nhds
  obtain ⟨a,valid⟩:=eventually_atTop.mp (zero.eventually_lt_const wide)
  let outer (i:ℕ):Set.Ioc (0:ℝ) radius:=⟨xs (a+i),(bad _).1,(valid _ (by omega)).le⟩
  let inner (i:ℕ):Set.Ioc (0:ℝ) radius:=⟨(outer i).val/2,half_pos (outer i).property.1,
    (half_le_self (outer i).property.1.le).trans (outer i).property.2⟩
  have shift:Tendsto (fun i:ℕ=>a+i) atTop atTop:=tendsto_atTop.mpr
    fun n=>(eventually_ge_atTop n).mono fun i hi=>by omega
  have drop:Tendsto (fun i=>(outer i).val) atTop (𝓝 0):=zero.comp shift
  have sub:Tendsto (fun i=>(inner i).val) atTop (𝓝 0):=by
    simpa only [inner,zero_div] using drop.div_const (2:ℝ)
  obtain ⟨up,age⟩:=calendar outer drop
  obtain ⟨down,later⟩:=calendar inner sub
  obtain ⟨c,X,school,dates,coordinates,_⟩:=WilsonMeasuredPublicEntranceNativeProgram.original
    F prior horizon survey outer inner lead made simple bliss up down (by simpa only [located] using drop)
    (by simpa only [located] using sub) (Eventually.of_forall (fun i=>by
      simp only [located]; exact half_lt_self (outer i).property.1)) age later
    (fun i=>checked (outer i)) (fun i=>checked (inner i))
  obtain ⟨A,earned⟩:=WilsonMeasuredPublicEntranceNativeStaff.along simple F H X school
  have ev:Tendsto (fun i:ℕ=>2*i) atTop atTop:=tendsto_atTop.mpr
    fun n=>(eventually_ge_atTop n).mono fun i hi=>by omega
  have issued:∀ᶠ i in atTop,
      Offered (Y:=l) simple F H (atRadius l horizon survey prior) (outer (c.pick i)).val m:=by
    filter_upwards [eventually_all.mpr (fun j:Fin (m+1)=>ev.eventually (earned j)),
      eventually_all.mpr (fun d:Fin (m+1)=>coordinates d)] with i buys funded
    have date:X.r (2*i)=(outer (c.pick i)).val:=(dates i).1.trans (located _)
    refine ⟨A (2*i),fun j hj=>?_⟩
    have draw:=buys ⟨j,Nat.lt_succ_of_le hj⟩
    refine ⟨date ▸ draw.1,fun d hd v=>?_⟩
    rw [(funded ⟨d,Nat.lt_succ_of_le (hd.trans hj)⟩).1]
    exact draw.2 d hd v
  obtain ⟨i,purchased⟩:=issued.exists
  exact (bad (a+c.pick i)).2 purchased

end YM.Integration.WilsonMeasuredPublicEntranceNativeAppointment
end
