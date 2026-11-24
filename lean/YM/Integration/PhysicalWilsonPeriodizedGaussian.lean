import YM.Integration.OriginalMarkedHeatCovariance

/-! The independently prescribed covering Gaussian at a finite physical RG02
step, in its actual original translated flat forest and free-key coordinates.
The analytic cover is chosen before the side and every contraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalWilsonPeriodizedGaussian
open Function Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix Bloch
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV Stationary
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

private theorem recover {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e:I→J) (he:Injective e) (M:Matrix I I ℝ):
    (insertion e*M*(insertion e)ᵀ).submatrix e e=M:=by
  let P:=insertion e
  have h:Pᵀ*P=1:=insertion.orthogonal e he
  calc _=Pᵀ*(P*M*Pᵀ)*P:=(insertion.compress e _).symm
       _=(Pᵀ*P)*M*(Pᵀ*P):=by simp only [Matrix.mul_assoc]
       _=M:=by rw [h,Matrix.one_mul,Matrix.mul_one]

variable {G:Gauge} (R:Run G) (N m p:ℕ) (hm:m<N)
local notation "A" => R.family.path.levels
local notation "S" => (A).clock.op m p
local notation "F₀" => repeatF (S)
local notation "base" => (RunFormalChain.fromRun R).step N m p hm
local notation "periodic" => (conditional (A) N m).acts ((A).S.side m p)
local notation "pf" => plant (G:=G) (F₀)
local notation "blocks" => unitSplit G (S) 1

theorem owned : Next.Free.Whole (conditional (A) N m):=(cond_laws (A) m N).2.1

theorem ambient (t:((R.family.path.levels).clock.op m p).Choices):
    (periodic)=repackM (blocks) (blocks) (insertion (pf)*(base).covariance (F₀) t*reduce G (S) (F₀)):=by
  rw [OriginalMarkedHeatCovariance.ambientCovariance R N m p hm (F₀) t]
  exact (cond_laws (A) m N).2.2 _ _ (S).sizes

theorem entry (t:((R.family.path.levels).clock.op m p).Choices) (i j:Key (F₀) G):
    (base).covariance (F₀) t i j=(periodic) ((blocks) ((pf) i)) ((blocks) ((pf) j)):=by
  rw [ambient R N m p hm t]
  simp only [repackM,Matrix.submatrix_apply,Equiv.symm_apply_apply,reduce]
  exact (congr_fun (congr_fun (recover (pf) (plant_inj (F₀)) ((base).covariance (F₀) t)) i) j).symm

theorem contractions {Z:Type*} (t:((R.family.path.levels).clock.op m p).Choices)
    (evaluate:Matrix (Key (F₀) G) (Key (F₀) G) ℝ→Z):
    evaluate ((base).covariance (F₀) t)=
      evaluate (fun i j=>(periodic) ((blocks) ((pf) i)) ((blocks) ((pf) j))) := by
  exact congrArg evaluate (funext fun i=>funext fun j=>entry R N m p hm t i j)

end YM.Integration.PhysicalWilsonPeriodizedGaussian
end
