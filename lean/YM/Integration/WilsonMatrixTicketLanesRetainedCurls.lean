import YM.Integration.WilsonMatrixTicketLanesRetainedBid
import YM.Integration.WilsonMatrixTicketLanesReflectedPropagator

/-! The four actual free-link entries of each genuine microscopic finite-Wilson curl. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedCurls
open FVA2.CityHistory Matrix
open Function Filter Finset Lattice Gauge RG Tree Wilson Precision Push.BetaTransport Exterior Bloch Laurent
open PertExtension PertExtension.GaussianScore RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Lumen
open RGComparison.Core16.Spool ThermalShortcuts.ThermalJets WilsonMatrixTicketLanesReflectedInner WilsonMatrixTicketLanesRetainedBid
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (T : Forest S.ratio)
local notation "D" => Descent.push S T Descent.nil

/-- A tree link is fixed. On a genuine free link its edge/color slot is unchanged. -/
def wire (e : Edge (Site f)) (i : G.ColorIndex) : Module.Dual ℝ (Future G S T) :=
  if h:e∈T.trunks then 0 else WilsonMatrixTicketLanesReflectedInner.axis S T (⟨e,h⟩,i)

def corners (z : Face (Per f)) : Fin 4→Edge (Site f) :=
  ![(z.1+step z.2.val.1,z.2.val.2),(z.1,z.2.val.2),(z.1+step z.2.val.2,z.2.val.1),(z.1,z.2.val.1)]

def orientation : Fin 4→ℝ := ![1,-1,-1,1]

def curl (z : Face (Per f)) (i : G.ColorIndex) := (leg G D z i).comp (upstairs S T)

private theorem component (e : Edge (Site f)) (i : G.ColorIndex) (v : Future G S T) :
    (topDir D (upstairs S T v) (e.1,coord e.2)) i=wire S T e i v := by
  have base : linearCopy S.ratio (collect G (0 : Push.In G c)) e=0 := by
    unfold linearCopy;split <;> rfl
  change (Bid.stretch T (0,v) (e.1,coord e.2)) i=_
  rw [Bid.stretch]
  simp only [show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _,Prod.mk.eta,base,zero_add]
  by_cases h:e∈T.trunks <;> simp [wire,h,WilsonMatrixTicketLanesReflectedInner.axis]

/-- There is no sum over the torus in the deposited registered face field. -/
theorem placed (z : Face (Per f)) (i : G.ColorIndex) : curl S T z i =
    ∑ j : Fin 4,orientation j • wire S T (corners z j) i := by
  apply LinearMap.ext;intro v
  change ((d 1 f *ᵥ parts G 1 (topDir D (upstairs S T v)) i) (z.1,plaquette z.2))=_
  rw [d_plaquettes]
  simp only [parts,Fin.sum_univ_four,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  change _=orientation 0*wire S T (corners z 0) i v+orientation 1*wire S T (corners z 1) i v+
    orientation 2*wire S T (corners z 2) i v+orientation 3*wire S T (corners z 3) i v
  rw [component S T (z.1+step z.2.val.1,z.2.val.2),component S T (z.1,z.2.val.2),
    component S T (z.1+step z.2.val.2,z.2.val.1),component S T (z.1,z.2.val.1)]
  simp [orientation,corners];ring

end YM.Integration.WilsonMatrixTicketLanesRetainedCurls
