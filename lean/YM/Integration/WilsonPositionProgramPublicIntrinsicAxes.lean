import YM.Integration.WilsonPositionProgramPublicAllOrderPreframe

/-! The common public coordinates retain the original horizon of each
letter before the finite determining test has mixed its columns. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicIntrinsicAxes
open Filter Lattice Wilson RG Source Extraction Table Spec RG17 FullVolume Climb
open PhysicalNext.Repeat.Legato Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register MS MS.Fleet MS.Land MS.Menus Local.Physical
open WilsonPositionHomogeneousFrame WilsonPositionProgramPublicMeasuredAxes
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(B:Deck G){d e:ℕ}

def includeAt (h:d≤e)(i:Glyph B d):Glyph B e:=
  ⟨⟨i.1.val,lt_of_lt_of_le i.1.isLt (Nat.succ_le_succ h)⟩,i.2⟩

theorem basis (h:d≤e)(i:Glyph B d):axes R B e (includeAt B h i)=
    (Maxwell.Free.scheme R.family.labels).rise h (axes R B d i):=by
  apply Maxwell.Free.address_inj R.family.labels e
  rw [Maxwell.Free.address_rise]
  simp only [Maxwell.Free.address_eval,WilsonPositionProgramPublicMeasuredAxes.filed,Theater.readHeight]
  rfl

variable {R}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}
    {g:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ:Prescription (Press.portDeck G)}{dial:Bool}(H:Main.Match Z g M σ dial)
    (lead:Leading F J)(income:∀d,∀ᶠ r in trail,PhysMS.Frame.obedient F Y (J r) d)

include H lead income in
theorem original (h:d≤e):∀ᶠ r in trail,∀i:Glyph B d,
    WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) (includeAt B h i)=
    F.sector.derivatives.rise h (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i):=by
  have nested (h:d≤e):∀ᶠ r in trail,∀x:RG17.Free R.family d,
      homogeneous F J Z r e ((Maxwell.Free.scheme R.family.labels).rise h x)=
      F.sector.derivatives.rise h (homogeneous F J Z r d x):=by
    induction h with
    | refl =>
      exact .of_forall fun r x=>by
        rw [(Maxwell.Free.scheme R.family.labels).arrival (Maxwell.table_sym _) (Maxwell.Free.scheme_filters _),
          F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection]
    | @step n small prev =>
      have nextDate:=WilsonPositionHomogeneousFrame.adjacent F J Z lead income g
        (WilsonPositionHomogeneousCoefficients.purchased Z H) n
      filter_upwards [prev small,nextDate] with r carried next x
      rw [←(Maxwell.Free.scheme R.family.labels).transit (Maxwell.table_sym _) (Maxwell.Free.scheme_filters _)
        small (Nat.le_succ n),next,carried,
        F.sector.derivatives.transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]
  filter_upwards [nested h] with r heard i
  simpa only [WilsonPositionProgramPublicMeasuredAxes.position,basis] using heard (axes R B d i)

include H lead income in
theorem all (d:ℕ):∀ᶠ r in trail,∀i:Glyph B d,
    let k:=i.size
    let child:Glyph B k:=⟨⟨k,Nat.lt_succ_self _⟩,i.2⟩
    F.sector.derivatives.rise (Nat.le_of_lt_succ i.1.isLt)
      (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) child)=
      WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i:=by
  apply eventually_all.mpr
  intro i
  let child:Glyph B i.size:=⟨⟨i.size,Nat.lt_succ_self _⟩,i.2⟩
  filter_upwards [original B F J Z H lead income (Nat.le_of_lt_succ i.1.isLt)] with r read
  exact (read child).symm

end YM.Integration.WilsonPositionProgramPublicIntrinsicAxes
