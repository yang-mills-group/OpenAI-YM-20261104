import YM.Integration.MSFixedRatioCalibration
import YM.FormalBulk08.Copula.Taut

/-! The finite position detector and the fixed-ratio physical iteration
have the same genuine forecast at each chronological page. In particular
the chosen, priced detector metric induces precisely the Maxwell Hessian
of the manuscript's independently iterated two-form row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioGaussianForecast
open Lattice RG Next.Free RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger
open MSFixedRatioGeometry MSFixedRatioCalibration FormalBulk08
open scoped Classical

theorem train (p : Patch) (w : Page history) : (lattice p).training w=Copula.Diagram p w.downW := by
  apply Page.proves (g:=fun j=>(lattice p).training j=Copula.Diagram p j.downW) _ _ w
  · intro x
    exact Halo.earlierC x
  · intro i ih
    rw [Circuit.crest]
    change (Copula.headV p ((lattice p).training i.prev)).land =
      (Copula.headV p (Copula.Diagram p i.prev.downW)).land
    rw [ih]

theorem flight (p : Patch) (w : Flap history) : (lattice p).crew w=Copula.flyP p w.offset := by
  change Copula.headV p ((lattice p).training w.prev)=Copula.headV p (Copula.Diagram p w.prev.downW)
  rw [train p w.prev]

theorem stationary {K : KernelChoices} (p : Patch) (Y : Program K) (w : Flap history) :
    (lattice p).tells Y w=((Copula.flyP p w.offset).duo K.penalty).A0 := by
  change ((Copula.headV p ((lattice p).training w.prev)).duo K.penalty).A0=
    ((Copula.headV p (Copula.Diagram p w.prev.downW)).duo K.penalty).A0
  exact congrArg (fun t=>(show Bloch.Cross p.L (Exterior.TypeFace 1) (Exterior.TypeFace 1) from ((Copula.headV p t).duo K.penalty).A0)) (train p w.prev)

theorem bed {K : KernelChoices} (p : Patch) (Y : Program K) (w : Page history) :
    Next.Free.Defined K.penalty (Y.fees p.J) (Copula.Diagram p w.downW) ((lattice p).tables Y w) := by
  rw [←train p w]
  exact ((lattice p).honored Y w).flight_s

/-- Equality before any contraction or momentum projection. The gauge
extension of a bed disappears on the exact exterior derivative in
both Maxwell precision matrices. -/
theorem precision {K : KernelChoices} (p : Patch) (Y : Program K) (w : Page history) (n : Side) :
    Precision.K (((lattice p).tables Y w).metric.acts n)=
      Precision.K ((Next.Free.pink K.penalty (Copula.Diagram p w.downW)).acts n) := by
  unfold Precision.K
  rw [(bed p Y w).metric,Matrix.mul_assoc,Matrix.mul_assoc]
  rw [(Next.Free.obligations K.penalty (Y.fees p.J) K.penalty_pos (Y.hailed.net _) p.order_cut
    (Copula.Diagram p w.downW) n).2.2.1]

end YM.Integration.MSFixedRatioGaussianForecast
