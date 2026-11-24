import YM.Integration.WilsonCenteredFullDensity

/-! The whole singleton physical moment and the linear reweighting
of its original hard owner. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredSingletonMass
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories Extra.Histories Comparison.RG02.Cumulants
open WilsonCenteredHardWallet WilsonCenteredHardMount WilsonCenteredHardAnswers 
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n} {y : Site n}

theorem scaled (z : ℂ) (f : ℕ → Config G n → ℂ) {d : ℝ} (fit : ForceFormat P.p P.activities y f)
    (due : ForceCost P.p P.activities f d) :
    ForceFormat P.p P.activities y (z•f) ∧ ForceCost P.p P.activities (z•f) (‖z‖*d) := by
  constructor
  · refine ⟨?_,?_,fun i g U=>?_,fun i U W links flags=>?_,fun i=>?_⟩
    · intro i U hi
      exact fit.forcing i U (fun e=>hi (by simp [e]))
    · intro i hi
      exact fit.carried i (fun e=>hi (by simp [e]))
    · exact congrArg (fun v : ℂ=>z*v) (fit.invariant i g U)
    · exact congrArg (fun v : ℂ=>z*v) (fit.supported i U W links flags)
    exact measurable_const.mul (fit.borel i)
  obtain ⟨e,paid,cap⟩:=due
  refine ⟨fun i=>‖z‖*e i,?_,fun i=>⟨mul_nonneg (norm_nonneg _) (cap i).1,fun U=>?_⟩⟩
  · simpa only [BudgetPoint.mass,mul_left_comm,mul_assoc] using Push.RelayDifference.scale_budget (norm_nonneg z) paid
  exact (norm_mul z (f i U)).le.trans (mul_le_mul_of_nonneg_left ((cap i).2 U) (norm_nonneg _))

variable {V X ι : Type} [DecidableEq V] [Fintype V] {R : Census V} {o : V→Site n}

omit [Fintype V] in
theorem first (H : Hard X P.p P.activities.forced P.activities.K o R) (K : Guard.Keeper P.p P.activities)
    (Z : Support n) (x : X) (U : Config G n) (c : V) (serial : ℕ×Finset ℕ ↪ ℕ) {t v : ℝ}
    (paid : ForceCost P.p P.activities (WilsonCenteredHardMount.first H K Z (R.fire c) x serial) t)
    (quiet : P.activities.KBound P.p v) (born : Summable (Fusion.Attached.packet P.activities P.p (H.hard x) U)) :
    WilsonCenteredHardAnswers.read (P:=P) (WilsonCenteredHardMount.first H K Z (R.fire c) x serial) U=
      (WilsonCenteredAbsoluteHard.gas H x U).part (R.fire c) := by
  have q:=first_sum H K Z x U (R.fire c) serial paid quiet
  have hs : HasSum (fun F=>(Fusion.Attached.packet P.activities P.p (H.hard x) U F).part (R.fire c))
      ((WilsonCenteredAbsoluteHard.gas H x U).part (R.fire c)) := (Poly.get _).hasSum born.hasSum
  apply q.unique
  apply hs.congr_fun
  intro F
  by_cases valid : P.activities.admissible P.p U F <;>
    simp [valid,Fusion.Attached.packet,Multi.first_of_prod,H.quiet,once,leg]

theorem ordinary (A : Gallery X ι o P R) (x : X) (U : Config G n) (c : V)
    (regular : Summable (fun i=>A.E.frame i x U)) (hard : Summable (Fusion.Attached.packet P.activities P.p (A.K.hard x) U)) :
    (A.density x U).part (R.fire c)=(P.eval U:ℂ)*(A.E.log x U).part (R.fire c)+
      (Real.exp (P.exponent U):ℂ)*(A.gas x U).part (R.fire c) := by
  let L:=A.E.log x U
  have zero : L.part R.quiet=0 := Lamps.quiet_of_hasSum x U regular
  have noMark := Hard.packet_of_quiet A.K x U hard
  change (A.gas x U).part R.quiet=(P.activities.gas P.p U:ℂ) at noMark
  have f : (Poly.pass L).part (R.fire c)=L.part (R.fire c) := by
    rw [←lamp c _ (Poly.pass_part L zero),connected_pass zero]
  simp only [Gallery.density,Poly.part_smul,Multi.first_mul]
  rw [f,Poly.pass_part L zero,noMark,Rep.eval,Complex.ofReal_mul]
  dsimp [L]
  ring

end YM.Integration.WilsonCenteredSingletonMass
