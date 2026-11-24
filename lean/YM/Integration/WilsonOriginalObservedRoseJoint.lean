import YM.Integration.WilsonOriginalObservedRoseCellPair
import YM.Integration.WilsonMaxwellThermometerReleasedSlope

/-! The actual unsubtracted physical Rose, the moving public Galop and the finite Maxwell ground. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseJoint

open Filter Finset Function MeasureTheory Lattice Wilson Labels Source Extraction Table Spec
open Climb Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Precision
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonSeparatedOriginalThermometerCells (positions placed weight tested)
open WilsonMaxwellThermometerShiftedPanel (translated cell measurable_cell)
open WilsonPositionThermometerConnected (value)
open WilsonPositionThermometerCapStation (Group)
open WilsonMaxwellThermometerFiniteTangent (credit roster)
open WilsonOriginalObservedRoseFaces (unpaid remainder fine)
open WilsonOriginalObservedRoseCellPair (mass)
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (D : ChartRatio G) (W : Initialize G) {V : Store G}
    (K : Pick V)
variable {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (A : ℝ → Group R.family 6)
local notation "fit" => WilsonPositionCorrectedCap.adjusted F J V A
abbrev locations (z : ℕ×ℕ) := Fin 3 → Site (R.family.side z.1 z.2)

def lowerSite (k : ℕ) (r : ℝ) (z : ℕ×ℕ) (live : k≤z.1) (o : locations R z) : Sample 3 :=
  let m:=WilsonMaxwellThermometerSignedWallet.board R k r z.2
  translated m (Mesh.back m ((R.family.S.toDepth live z.2).parent ∘ o))

/-- Both cofactor charges and the exact quadratic/cubic proper-face contribution. -/
def fees (r : ℝ) (z : ℕ×ℕ) (h : (fit r).station.k≤z.1) (m : Mesh)
    (p a : Tags G 6 3) (t : ℂ) : Prod ℂ ℂ :=
  let k:=(fit r).station.k
  let data:=WilsonPositionThermometerGradedReading.row (fit r) z
  let x:=lowerSite R k r z h
  let μ:=mass (Rose.test K) (positions (R:=R) r z) (cell m)
  (∑o:locations R z × m.Tuple (n:=3),μ o*unpaid R D W (V:=V) (x o.1) p
     (data o.1) (fine W m o.2 a) t,
   ∑o:locations R z,weight (Rose.test K) (positions (R:=R) r z) o*
     remainder W (V:=V) (x o) p t)

open WilsonMaxwellThermometerPublicStation (report)
open WilsonPositionGradedThermometerHearing (offer)

/-- Equality before either original cutoff is removed.  Each field is on its own true grid. -/
theorem original (law : LocalRatio D) (r : ℝ) (z : ℕ×ℕ) (h : (fit r).station.k≤z.1)
    (m : Mesh) (p : Tags G 6 3) (u : Sec G 6) (a b : Sec G 4) (t : ℂ) :
    let k:=fun y=>(fit y).station.k
    let e:=fees R D W K F J A r z h m p (roster u a b) t
    offer F J V K A r z - credit W K m u a b - t*report R W K k r z p =
      e.1 + t^2*e.2 := by
  let φ:=Rose.test K
  let χ:=positions (R:=R) r z
  let γ:=cell m
  let d:=WilsonPositionThermometerGradedReading.row (fit r) z
  let p₀:=roster u a b
  let x:=lowerSite R (fit r).station.k r z h
  let μ:=mass φ χ γ
  let Q (o:locations R z):=WilsonMaxwellThermometerPublicGalop.node W (V:=V) (x o) p
  let T (o:locations R z):=remainder W (V:=V) (x o) p t
  let B (o:m.Tuple (n:=3)):=fine W m o p₀
  let L (o:locations R z × m.Tuple (n:=3)):=unpaid R D W (V:=V) (x o.1) p (d o.1) (B o.2) t
  have same (g:locations R z→ℂ): ∑o,weight φ χ o*g o=∑s,μ s*g s.1 :=
    WilsonOriginalObservedRoseCellPair.left φ χ γ (placed (R:=R) r z) (measurable_cell m) g
  have other (g:m.Tuple (n:=3)→ℂ): ∑o,weight φ γ o*g o=∑s,μ s*g s.2 :=
    WilsonOriginalObservedRoseCellPair.right φ χ γ (placed (R:=R) r z) (measurable_cell m) g
  have top : offer F J V K A r z=∑s,μ s*value (d s.1) :=
    (tested φ χ (placed (R:=R) r z) (fun o=>value (d o))).trans (same _)
  have bottom : credit W K m u a b=∑s,μ s*value (B s.2) := other _
  have head : report R W K (fun y=>(fit y).station.k) r z p=∑s,μ s*Q s.1 := by
    rw [report,dif_pos h]
    exact same Q
  dsimp only
  rw [top,bottom,head]
  change _ = (∑s,μ s*L s) + t^2*(∑o,weight φ χ o*T o)
  rw [same T,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have paid:=WilsonOriginalObservedRoseFaces.original R D W (V:=V) (x s.1) p law (d s.1) (B s.2) t
  change value (d s.1)-value (B s.2)-t*Q s.1=L s + t^2*T s.1 at paid
  linear_combination μ s * paid

end YM.Integration.WilsonOriginalObservedRoseJoint
