import YM.Integration.WilsonVacuumPreResetFiniteCovarianceIncome
import YM.Integration.WilsonConditionalTaylorWheelAffine
import YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
import YM.WilsonCoeffUV.Winding.Receipt

/-! The enrolled finite covariance tariff pays the actual Schur matrix on every canonical torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteAffineIncome
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Wick
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}

variable (R:Run G)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)



private theorem on_active {c f:Side} (S:StepData c f)(F:Forest S.ratio)
    (u:Pine G S F→ℝ)(i:Pine G S F):Reef.offer G F u i.val=u i:=by
  change ∑a:Pine G S F,(1:Matrix (wire G f) (wire G f) ℝ) a.val i.val*u a=u i
  have eq (a:Pine G S F) : (a.val=i.val) ↔ a=i := ⟨Subtype.ext, fun h=>congrArg Subtype.val h⟩
  simp [Matrix.one_apply,eq]

/-- Price of the complete affine mean on the real coarse unit box, directly
from the same enrolled periodized predictor as the Schur calculation. -/
theorem original (N j:ℕ)(live:j<N)(cash:Usage V R.metals.O j)(n:Side):
    let P:=destination V N j
    let H:=Reef.ferry P (b j) (wood j) n
    ∀(B:wire G n→ℝ), (∀a,|B a|≤1) → ∀i,|traceP B (H.drift i)|≤Fintype.card (wire G n)*nimbus cash.gear:=by
  intro P H B bounded i
  let S:=primary P.patch (V).clock.kernel n
  let F:=Reef.floor (V).clock.kernel P (wood j) n
  let M:=installed S.ratio (P.duo (V).clock.kernel.penalty).A0
  let A:=extractV G S F M
  have eqf:xree (loose V j) (V).clock.kernel n=F:=WilsonConditionalTaylorWheelCanonicalForest.original S
  have inc:=(snowM (R:=V) (Ñ:=R.metals.O) live cash n).1.bow
  let w:=weaveFine (ratioN P.patch.L n) G
  have price (v:Woods G n):|A i.val v|≤nimbus cash.gear:=by
    have paid:=inc.2 (w i.val) v
    change |allotM w (Equiv.refl _) (teller G (loose V j) (V).clock.kernel (WilsonCoeffUV.Bank.roam V N j) n) (w i.val) v|≤_ at paid
    have rep:teller G (loose V j) (V).clock.kernel (WilsonCoeffUV.Bank.roam V N j) n=A:=by
      simp only [teller,eqf]
      rfl
    simp only [allotM,Matrix.submatrix_apply,Equiv.symm_apply_apply,Equiv.refl_symm,Equiv.refl_apply,rep] at paid
    apply paid.trans
    apply (mul_le_mul_of_nonneg_left _ inc.1).trans_eq (mul_one _)
    apply Real.exp_le_one_iff.mpr
    have nonneg:=cash.width.le.trans cash.win.le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have drift: (fun v=>traceP B (H.drift v))=Flat.rawMean G S F M *ᵥ B:=Reef.draught_fee (Reef.pMean G (V).clock.kernel P n F) B
  have fine:=congrFun (WilsonConditionalTaylorWheelAffine.stationary S F M B) i.val
  rw [on_active] at fine
  rw [congrFun drift i,←fine]
  change |∑v:Woods G n,A i.val v*B v|≤_
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _≤∑_v:Woods G n,nimbus cash.gear:=Finset.sum_le_sum fun v _=>by
      rw [abs_mul]
      simpa using mul_le_mul (price v) (bounded v) (abs_nonneg _) inc.1
    _= _:=by simp [nsmul_eq_mul]

end YM.Integration.WilsonVacuumPreResetFiniteAffineIncome
end
