import YM.Integration.WilsonVacuumPreResetFiniteWindingBudget
import YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
import YM.WilsonCoeffUV.Winding.Receipt

/-! The enrolled finite covariance tariff pays the actual Schur matrix on every canonical torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteCovarianceIncome
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


private theorem installed_entry {c f:Side} (S:StepData c f) (F:Forest S.ratio) (Y:FreeResolvent.FaceRow) (x y:Active G F):
    covariance G S F Y (plant F x) (plant F y) = treeInverse G S F Y 0 x y:=by
  classical
  simp [covariance,reduce,Matrix.mul_apply,Matrix.transpose_apply,insertion,(plant_inj F).eq_iff]

/-- Even for a winding cluster the datum is the original restricted Gaussian.
The same dated treasury pays every covariance entry, before the UV top or period. -/
theorem original (N j:ℕ)(live:j<N)(cash:Usage V R.metals.O j)(n:Side):
    let P:=destination V N j
    let H:=Reef.ferry P (b j) (wood j) n
    ∀x y, |H.saddle.q x y|≤nimbus cash.gear:=by
  intro P H x y
  let S:=primary P.patch (V).clock.kernel n
  let F:=Reef.floor (V).clock.kernel P (wood j) n
  let E:=Reef.pines (G:=G) F
  let Y:=freeForms V N (j+1)
  have eqf:xree (loose V j) (V).clock.kernel n=F:=
    WilsonConditionalTaylorWheelCanonicalForest.original S
  have prec:=WilsonVacuumPreResetCanonicalBlock.precision P (b j) (wood j) n Y rfl
  let a:=E.symm x
  let b':=E.symm y
  have obs:treeInverse G S F Y 0 a b'=H.saddle.q x y:=by
    have s:=congrFun (congrFun prec a) b'
    change treeInverse G S F Y 0 a b'=H.saddle.q (E a) (E b') at s
    rw [show E a=x from E.apply_symm_apply _,show E b'=y from E.apply_symm_apply _] at s
    exact s
  rw [←obs,←installed_entry S F Y a b']
  have income:=(snowM (R:=V) (Ñ:=R.metals.O) live cash n).2.1.bow
  let w:=weaveFine (ratioN P.patch.L n) G
  have earned:=income.2 (w (plant F a)) (w (plant F b'))
  have eq:allotM w w (mer (G:=G) (loose V j) (V).clock.kernel Y n) (w (plant F a)) (w (plant F b'))=
        covariance G S F Y (plant F a) (plant F b'):=by
    simp only [allotM,Matrix.submatrix_apply,Equiv.symm_apply_apply,mer,eqf]
    rfl
  change |allotM w w (mer (G:=G) (loose V j) (V).clock.kernel Y n) (w (plant F a)) (w (plant F b'))|≤_ at earned
  rw [eq] at earned
  apply earned.trans
  apply (mul_le_mul_of_nonneg_left _ income.1).trans_eq (mul_one _)
  apply Real.exp_le_one_iff.mpr
  have nonneg:=cash.width.le.trans cash.win.le
  have gap:0≤(tor n).gap (w (plant F a)).1 (w (plant F b')).1:=by
    unfold tor
    positivity
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by exact_mod_cast gap)

end YM.Integration.WilsonVacuumPreResetFiniteCovarianceIncome
end
