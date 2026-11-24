import YM.Integration.WilsonOriginalSignedFullQuadratic
import YM.Integration.ManuscriptQLocalStationaryGeometry

/-! The untruncated affine Gaussian precision on the same actual step of
the existence proof, including its restriction to the chosen forest. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedFullMatrix
open Function Filter Lattice Wilson RG RG.Patch Pressure Pressure.Stores Pressure.Tube
open Pressure.Testing Precision Exterior Tree Push Push.SectorMeasure Push.SectorMeasure.Oriented Matrix
open Bid Work.F03 FreeResolvent FreeResolvent.Affine Next.Fluctuations Next.SectorChange
open Progress.StationaryScenes PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AnalyticNext.ConnectedActivity.Aff PhysicalAffineScalarStationary
open scoped Topology BigOperators Classical RealInnerProductSpace

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)

theorem whole {P : Teller G} {A B : Bed} (path : Alongside A B T) (fund : P.Funds S T)
    (tag : S.Choices) :
    block S tag T.high T.up all 0 = fullMatrix G S A.metric := by
  let Q := block S tag T.high T.up all 0
  let H := fullMatrix G S A.metric
  have diag (u : Vec G f 1) : u ⬝ᵥ (Q *ᵥ u) = u ⬝ᵥ (H *ᵥ u) := by
    rw [show Q=block S tag T.high T.up all 0 from rfl,←PhysicalAffineScalarMetric.responses T tag all 0]
    simp_rw [real_inner_self_eq_norm_sq, WilsonOriginalSignedFullQuadratic.chamber T path fund]
    simp [nsmul_eq_mul,H]
  have left (u v : Vec G f 1) : u ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (Q *ᵥ u) := by
    rw [show Q=block S tag T.high T.up all 0 from rfl,←PhysicalAffineScalarMetric.responses T tag all 0,
      ←PhysicalAffineScalarMetric.responses T tag all 0]
    congr 1
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  obtain ⟨_,_,bounds,_⟩ := fund.feeds
  obtain ⟨_,_,_,_,floor,_⟩ := path.budgets
  rw [←fund.high] at bounds
  have gauge (x y : LogField G f) : gaugeFiscal A x y = gaugeFiscal A y x := by
    rw [metric_pair A bounds path.inbound x y floor,metric_pair A bounds path.inbound y x floor]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (faceCurl i x) (faceCurl i y),
      real_inner_comm (ellLine T.up i x) (ellLine T.up i y)]
  have right (u v : Vec G f 1) : u ⬝ᵥ (H *ᵥ v) = v ⬝ᵥ (H *ᵥ u) := by
    change flatten (decode u) ⬝ᵥ (fullMatrix G S A.metric *ᵥ flatten (decode v)) =
      flatten (decode v) ⬝ᵥ (fullMatrix G S A.metric *ᵥ flatten (decode u))
    rw [fiscal_eq,fiscal_eq]
    change gaugeFiscal A (decode u) (decode v) + _ = gaugeFiscal A (decode v) (decode u) + _
    rw [gauge]
    congr 2
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  ext i j
  let a : Vec G f 1 := Pi.single i 1
  let b : Vec G f 1 := Pi.single j 1
  have hp := diag (a+b)
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add] at hp
  have result : a ⬝ᵥ (Q *ᵥ b) = a ⬝ᵥ (H *ᵥ b) := by
    linarith only [hp,diag a,diag b,left a b,right a b]
  simpa [a,b,Q,H] using result

theorem original (R : Run G) (N m per : ℕ) (hm : m<N)
    (F : Forest (R.alloy.B.a.clock.op m per).ratio) (tag : (R.alloy.B.a.clock.op m per).Choices) :
    let S := R.alloy.B.a.clock.op m per
    let T := ships R.alloy.B N m per
    primary S F tag T.high T.up all 0 = treeMatrix G S F (R.alloy.B.M.H N (m+1)).metric := by
  intro S T
  have h := whole T (ManuscriptQLocalStationaryGeometry.alongside R N m per hm)
    (ManuscriptQLocalStationaryGeometry.funds R N m per hm) tag
  exact congrArg (fun M => M.submatrix (plant (G:=G) F) (plant (G:=G) F)) h

end YM.Integration.WilsonOriginalSignedFullMatrix
