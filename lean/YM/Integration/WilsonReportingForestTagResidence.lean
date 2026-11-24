import YM.Integration.WilsonReportingForestTagCalendar

/-! One original macro plaquette window per declared site contains the
chart faces and the tag-prediction faces of every incident crossing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Lattice RG Wilson Tree Pressure Filter PhysicalNext.Repeat.Legato
open WilsonReportingRegisteredAction WilsonReportingForestBlocks WilsonPhysicalLocalPlaquetteForest
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

private theorem membership {n:Side} (o:Site n) (r:ℕ) (p:Face (Per n)) :
    p∈WilsonAxialWindow.cells o r ↔ separation o p.1≤r := by
  constructor
  · intro h
    obtain ⟨z,hz,e⟩:=Finset.mem_image.mp (Finset.mem_product.mp h).1
    rw [separation_comm,←e,separation,add_sub_cancel_right]
    exact Work.E01.pdist_wrap_le hz
  · intro h
    have cell:=WilsonAxialWindow.cell o r (Work.E08.lift_mem_box h) p.2
    rwa [wrap_lift,sub_add_cancel] at cell

/-- The same occupied site houses every predictor face for any crossing in
its parent fibre. The roster and its grades are fixed before all periods. -/
theorem tag_residence (R:Run G) (d:I→ℕ) : ∀ᶠ m:ℕ in atTop,∀per
    (o:I→Site (R.family.side (m+1) per)),
    (∀i,faces R m per (d i) (o i)⊆tagCells R m per (o i)) ∧
    ∀(T:Forest (R.family.path.levels.clock.op m per).ratio) (e:T.Free),e∈incident R T d o→
      ∃i:I,predictorFaces T (pivot T e)⊆tagCells R m per (o i) := by
  let A:=R.family.path.levels
  let D (i:I):=depth R (d i)+3
  filter_upwards [(A.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (Finset.univ.sup D)] with m booked per o
  let S:=A.clock.op m per
  let L:=S.ratio.count.val
  let j:=S.patch.J
  let M:=macroR S.patch
  have l0:0<L:=S.ratio.count.property
  have sizeM:M=(j+7)*L:=by change (j+3)*L+4*L=(j+7)*L;ring
  have house (i:I):radius (extent (D i) L) L≤2*M:=by
    have height:D i≤j:=(Finset.le_sup (f:=D) (Finset.mem_univ i)).trans booked
    have grow:=Nat.le_mul_of_pos_right j l0
    unfold radius extent
    rw [sizeM]
    nlinarith only [height,grow,l0]
  constructor
  · intro i p hp
    apply (membership (o i) (4*M) p).mpr
    exact ((membership (o i) (radius (extent (D i) L) L) p).mp hp).trans
      ((house i).trans (show 2*M≤4*M by omega))
  · intro T e he
    obtain ⟨i,root⟩:=anchored R T d o e he
    let a:=pivot T e
    have start:= (root a (pair_of T e)).1
    change separation (o i) a.val.1≤extent (D i) L at start
    let b:=S.ratio.embed (S.ratio.parent a.val.1)
    have tip:2*separation a.val.1 b≤L:=Corona.near S.ratio a.val.1
    refine ⟨i,?_⟩
    intro p used
    apply (membership (o i) (4*M) p).mpr
    have inside:separation b p.1≤M:=(membership b M p).mp used
    have tri:=separation_triangle (o i) a.val.1 b
    have last:=separation_triangle (o i) b p.1
    have sized:=house i
    unfold radius at sized
    omega

end YM.Integration.WilsonReportingForestPivots
