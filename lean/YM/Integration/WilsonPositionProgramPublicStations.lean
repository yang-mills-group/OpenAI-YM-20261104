import YM.Integration.WilsonThermometerUnitFilingFourWeakWall
import YM.Integration.WilsonMeasuredPublicFamily
import YM.Integration.WilsonPositionProgramPublicContrast

/-! The two actually elected stations on one entire public space. The
pooled department may be the one already issued for a wider measurement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicStations
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent Trace MergeProof.East
open Maxwell XSpace XSpace.Normalize Trace.Terrace FVA2 FVA2.Register
open WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank WilsonMeasuredPublicSlots
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    {l : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
    {D d : ℕ} {s r B : ℝ}

private def rename {x y:S.Field d} (a : Arm R.family S (l:Filter _) d x) (eq : x=y) :
    Arm R.family S (l:Filter _) d y := ⟨a.source,a.label,a.approaches,a.represents.trans eq⟩

structure Pair (stock : Bank F l D s B) (cap : d≤D) {k : ℕ} (W : Vane R.family k)
    (fits : D≤k) (T : Spin.change S d) (r : ℝ) where
  arm : Bool → (v : S.Field d) → Arm R.family S (l:Filter _) d v
  pooled v : arm false v = ((stock.department d cap).print v).arm
  weak v z : (arm true v).source z =
    W.wheel.atCut z ⟨d,Nat.lt_succ_of_le (cap.trans fits)⟩ (T.symm v)
  reflected v : ∀ᶠ z : ℕ×ℕ in f.fuse, Cards.PaidAt R.family.S z.1 z.2 (purchaseWidth W)
    (R.family.beta z.1 z.2) (dock r*‖T.symm v‖) (R.family.O z.1 z.2 ((arm true v).source z) 0)

def Booked (stock : Bank F l D s B) (r : ℝ) : Prop :=
  ∃ (k : ℕ) (fits : D≤k) (W : Vane R.family k),
    W.checked f H k ∧ W.wheel.r=r ∧ D≤W.k ∧
    (0<purchaseWidth W ∧ 20*R.family.S.a (purchaseWidth W) < R.family.S.a (purchaseWidth W-1) ∧
      R.family.S.a (purchaseWidth W-1)<r*LogV r/32) ∧
    ∀ d (cap:d≤D), ∃ T : Spin.change S d, Nonempty (Pair F stock cap W fits T r)

theorem accepted (weak : WilsonThermometerUnitFilingFourWeakWall.Purchased F H l r D)
    (stock : Bank F l D s B) : Booked F (H:=H) stock r := by
  obtain ⟨k,hk,W,good,atR,live,width,available⟩ := weak.station
  refine ⟨k,hk,W,good,atR,live,width,?_⟩
  intro d hd
  obtain ⟨T,filed⟩ := available ⟨d,Nat.lt_succ_of_le hd⟩
  choose arm hold cards using filed
  let v (y:S.Field d) := rename (arm (T.symm y)) (T.apply_symm_apply y)
  let arms (b:Bool) (y:S.Field d) : Arm R.family S (l:Filter _) d y :=
    if b then v y else ((stock.department d hd).print y).arm
  refine ⟨T,⟨⟨arms,fun _=>rfl,fun y z => hold (T.symm y) z,fun y => ?_⟩⟩⟩
  exact cards (T.symm y)

theorem original {z : Arch R.family} (simple : G.Simple) (bliss : Bliss F l z H) (D : ℕ) :
    ∃ T : ℕ, ∀ᶠ r in trail, let s:=WilsonThermometerUnitFilingFourPoolShell.radius z T r
      (∃ stock : Bank F l D s (dock s^T), Booked F (H:=H) stock r) ∧
      ∀ (s B : ℝ) (stock : Bank F l D s B), Booked F (H:=H) stock r := by
  obtain ⟨T,banks⟩ := WilsonMeasuredPublicBank.before F l simple bliss D
  have all := banks Unit (fun _ r=>r) (fun _=>tendsto_id)
  refine ⟨T,?_⟩
  filter_upwards [all,WilsonThermometerUnitFilingFourWeakWall.original F simple bliss D] with r bought weak
  let stock := bought.some ()
  exact ⟨⟨stock,accepted F weak stock⟩,fun _ _ any=>accepted F weak any⟩

end YM.Integration.WilsonPositionProgramPublicStations
