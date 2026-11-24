import YM.Integration.FVA1Physical.Wilson.AngleGeneric
import YM.MSbar.Tonic.Loan

/-! Normalized integral underlying one angular forest comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Lattice RG YM.Wilson Tree MSbar MSbar.Bulk MSbar.Heath MSbar.Heath.Cottage
open scoped Classical Topology
variable {G : Gauge} {c f : Side} (S : StepData c f) (R : Rep G f) (V : Config G c)
variable (F : Forest S.ratio) (X : Support f) (A : Set (Config G f)) (r B φ : Config G f→ℝ)

def compass (t : IV F (board F X) G) : ℝ :=
  let h := twirl F (board F X) t
  let q := Rota.ghat (F:=F) (X:=board F X) r t φ A
  S.push R.beta (fun U=>q U*(R.eval (h U)*Real.exp (B U-B (h U)))) V/(S.push R.beta R.eval V)

variable {S R V F X A r B φ} {Y : Support f} {a κ σ C δ Λ w : ℝ}
theorem compass_meas (adm : Admitted V R S σ C δ Λ w)
    (rota : Rota (S:=S) R V Y F (board F X) A r a κ)
    (mB : Measurable B) (hf : GaugeLocal S Y φ) : Measurable (compass S R V F X A r B φ) := by
  let tw := fun p:IV F (board F X) G × Config G f=>twirl F (board F X) p.1 p.2
  let wt := fun p:IV F (board F X) G × Config G f=>Rota.ghat (F:=F) (X:=board F X) r p.1 φ A p.2
  exact rotated_integral_meas adm tw (twirlD F (board F X) G).measurable wt
    (Rota.stereo adm rota φ hf).meas B mB
end YM.Integration.FVA1Physical.Wilson
