import YM.Integration.WilsonPhysicalHistoryRetainedCoat

/-! The original raised activity changes at its omitted regular address on the
same affine sample. The other Wilson, blocking and Haar letters coincide. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson Pressure Pressure.Tube Tree
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Bloch Laurent Push Push.AbsoluteSums Precision Exterior Shell Channel
open PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge} {c f : Side}

private theorem term {P : Rep G f} {b : ℕ→ℝ} {δ : ℝ}
    (earned : ∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
      P.p.mass (P.activities.reg i).support (b i) else 0) δ) (i : ℕ) : 0≤b i ∧ b i ≤ δ := by
  have pay := earned (P.activities.reg i).site
  have n := pay.1 i
  have h := (pay.2.1.le_tsum i (fun k _=>pay.1 k)).trans pay.2.2
  simp only at n h
  have pos : 0≤b i := nonneg_of_mul_nonneg_right n (Real.exp_pos _)
  exact ⟨pos,(P.p.loMass _ _ pos).trans h⟩

private theorem exp_change {x y b : ℝ} (h : |x-y|≤b) (small : b≤1) :
    |(Real.exp x-1)-(Real.exp y-1)| ≤ 2*(1+|Real.exp x-1|)*b := by
  have cost : |y-x|≤b := (abs_sub_comm y x).le.trans h
  have fact : Real.exp x*Real.exp (y-x)=Real.exp y := by rw [←Real.exp_add]; congr 1; ring
  have ex : Real.exp x≤1+|Real.exp x-1| := by linarith only [le_abs_self (Real.exp x-1)]
  have tiny := Real.abs_exp_sub_one_le (cost.trans small)
  calc
    |(Real.exp x-1)-(Real.exp y-1)| = |Real.exp x*(1-Real.exp (y-x))| := by
      congr 1
      nlinarith only [fact]
    _ = Real.exp x*|Real.exp (y-x)-1| := by
      rw [abs_mul,abs_of_pos (Real.exp_pos _),abs_sub_comm]
    _ ≤ (1+|Real.exp x-1|)*(2*b) := mul_le_mul ex
      (tiny.trans (mul_le_mul_of_nonneg_left cost (by norm_num))) (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem other {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} (X : Coat T F)
    (P : Rep G f) (K : Activities G f) (a : ℝ) (C : ChartRatio G) (z : Air f G)
    (l : LogIndex c f) (away : ∀ i : ℕ,l≠.inl (.inl i)) :
    X.raiseAir P a C z l=X.raiseAir {P with activities:=K} a C z l := by
  unfold Coat.raiseAir Coat.farLog
  rcases l with (i|i)|i
  · exact (away i rfl).elim
  · simp only [Sum.elim_inl]
    unfold Coat.inhale Raw.expo Raw.space
    rcases i with u|u|u|u|u <;> simp only [Sum.elim_inl,Sum.elim_inr]
  · rcases i <;> simp only [Sum.elim_inl,Sum.elim_inr]

theorem raised_rows (R : Run G) {N n j d : ℕ} (hj : j<N) (A : Comparison R (p:=n) hj d) :
    let P:=R.family.path.rep N n j
    let Q:=approximation R (p:=n) hj d
    let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)
    ∃ b : ℕ→ℝ, (∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
      P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
      (∀ i,0≤b i ∧ b i ≤ δ) ∧
      ∀ {c : Side} {S : StepData c (R.family.side j n)} {T : Tube G S} {F : Forest S.ratio}
        (X : Coat T F) (a : ℝ) (C : ChartRatio G) (z : Air (R.family.side j n) G),
        (∀ i : ℕ,δ≤1 →
          let l : LogIndex c (R.family.side j n):=.inl (.inl i)
          |X.raiseAir P a C z l-X.raiseAir Q a C z l| ≤ 2*(1+|X.raiseAir P a C z l|)*b i) ∧
        ∀ l : LogIndex c (R.family.side j n),(∀ i : ℕ,l≠.inl (.inl i)) →
          X.raiseAir P a C z l=X.raiseAir Q a C z l := by
  dsimp only
  obtain ⟨b,pay,rows⟩ := coat_rows R hj A
  have each := term pay
  refine ⟨b,pay,each,?_⟩
  intro c S T F X a C z
  constructor
  · intro i small
    exact exp_change (rows X a C z i).2.1 ((each i).2.trans small)
  · intro l away
    let Q:=approximation R (p:=n) hj d
    have same := (retained_rows R hj A).1
    change X.raiseAir _ a C z l=X.raiseAir Q a C z l
    exact (other X _ Q.activities a C z l away).trans
      (congrArg (fun P=>X.raiseAir P a C z l) same.symm)

end YM.Integration.OriginalMarkedRunAction
