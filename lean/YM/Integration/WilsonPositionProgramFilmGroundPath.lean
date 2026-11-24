import YM.Integration.WilsonPositionProgramFilmGroundLaw

/-! The original positioned finite source evolves through the same chronological Gaussian conditionals on every intervening page. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramFilmGroundPath
open MeasureTheory Function Filter Finset Lattice Wilson Exterior Precision Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.Symmetry
open Comparison.RG02.Valence YM.Next.SectorChange WilsonThermometerPositionFilmCubicGeometry
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Binding RegulatorIR.Geometry
open PertExtension.Series PertExtension.Series.Tested Booth Pipeline Period.Field RG
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] [Fintype I] {X:Type} {j:X→ℕ} {n:Page j→Side}
  {Q:KernelChoices} {Γ:RG.History G} {E:Circuit j n} (K:Bulk.Chain Γ) (P:SeriesT E Q Γ)
  (S:Census I) (u:I) {m:ℕ} (B:X→Boot.Scout (G:=G) m) (L:Page j→Binding.Scale) (per r:ℕ) (T:See.Times L r)
  (Z:See.Agenda P S per) (law:See.Setup K P S u B (p:=per) L r T Z) (k:Flap j)

local notation "tree" => Halo.bios (P.stepData E Γ per k)
local notation "draw" => directive (P.stepData E Γ per k)
local notation "op" => P.readyKin E Γ K per k
local notation "intake" => See.before P k (Z k.prev)



abbrev Position (z:Page j) := fieldDir G (Γ.S.side (P.vol z) per) 1 → ℂ

def launched (w:X):Position P per (Page.opening j w):=
  fun x=>(QuadraticLocal.Earn.Air.discharge (Boot.ink S u Γ (P.vol (Page.opening j w)) per (B w)) 0 x).part (S.fire u)

def push (f:Position P per k.prev):Position P per k.next :=
  fun x=>∫ z,(See.castF (X:=fun t=>fieldDir G (Γ.S.side t per) 1→ℂ) (P.links k) f)
    (direction tree (Bulk.translated op tree x z).2) ∂(Gaussian.cloud ((op).covariance tree draw))

def path (z:Page j):Position P per z:=
  Halo.seriesC (X:=Position P per) (launched P S u B per) (push K P per) z

include law in
theorem original (z:Page j)(x:fieldDir G (Γ.S.side (P.vol z) per) 1):
    (QuadraticLocal.Earn.Air.discharge (Z z) 0 x).part (S.fire u)=path K P S u B per z x:=by
  suffices all:∀z:Page j,∀x,(QuadraticLocal.Earn.Air.discharge (Z z) 0 x).part (S.fire u)=path K P S u B per z x
    from all z x
  apply Page.proves
  · intro w x
    rw [law.top w]
    rfl
  · intro k old x
    rw [WilsonPositionProgramFilmGroundLaw.original K P S u B L per r T Z law k x]
    unfold path
    rw [Halo.laterC]
    unfold push
    have rest:=See.transferred
      (fun i (W:Bulk.Colors S G (Γ.S.side i per)) (f:fieldDir G (Γ.S.side i per) 1→ℂ)=>
        ∀a,(QuadraticLocal.Earn.Air.discharge W 0 a).part (S.fire u)=f a)
      (Z k.prev) (path K P S u B per k.prev) (P.links k) old
    apply integral_congr_ae
    filter_upwards with z
    exact rest _

end YM.Integration.WilsonPositionProgramFilmGroundPath
end
