import YM.Integration.WilsonPhysicalHistoryBoundary

/-! The true inverse transport of all calibrated fields on the soft return
interval. All steps of one physical trajectory act on the same raw label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryInverse

open Filter Real Lattice Wilson RG RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph Work.G08
open scoped Topology

variable {G : Gauge}

private theorem coin_limit (R : Run G) (hG : G.Simple) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k≤N → regulatorRun R.family N n k ≤ exp (-(Lambda R.family.path.levels k)/4) := by
  let C := R.family
  let L := Lambda C.path.levels
  filter_upwards [(lambda_leads C hG).eventually_ge_atTop (4*log (2*exp 1))] with k big N n live
  have price := (g_band C R.makes (p:=n) live).2
  apply price.trans
  change 2*exp 1*exp ((-(1:ℝ)/2)*L k) ≤ exp (-(L k)/4)
  have pos : 0<2*exp (1:ℝ) := by positivity
  calc
    _ = exp (log (2*exp 1)+(-(1:ℝ)/2)*L k) := by rw [exp_add,exp_log pos]
    _ ≤ _ := exp_le_exp.mpr (by change 4*log (2*exp 1)≤L k at big; linarith)

/-- In measured coordinates the inverse string of true transfer matrices
costs an arbitrarily small negative power of the physical reporting coupling.
The threshold precedes every cutoff, period, interval and input vector. -/
theorem coordinates (R : Run G) (hG : G.Simple) (d : ℕ) (B : ℝ) (hB : 0 ≤ B) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n j t, k≤j → j≤t → t≤N →
      R.family.S.scale t - R.family.S.scale j ≤ B*Lambda R.family.path.levels k →
      ∀ w, mCost R.family d N n t w ≤ (regulatorRun R.family N n k)^(-η)*mCost R.family d N n j w := by
  let C := R.family
  let L := Lambda C.path.levels
  let γ := η/(4*(B+1))
  have gp : 0<γ := div_pos hη (by positivity)
  have gd : γ*(4*(B+1))=η := div_mul_cancel₀ η (by positivity)
  have slice : γ*B ≤ η/4 := by nlinarith only [gd,gp]
  filter_upwards [ActualOneMarkGraphStep.gates R hG d gp zero_lt_one,coin_limit R hG] with k opened clock
  intro N n j t kj jt tN span w
  let X := fun i => mCost C d N n i w
  have walk (b : ℕ) (jb : j ≤ b) : b ≤ N → X b ≤ exp (γ*(C.S.scale b-C.S.scale j))*X j := by
    induction b,jb using Nat.le_induction with
    | base => intro live; simp
    | succ b jb old =>
      intro live
      have hpre := old (Nat.le_trans (Nat.le_succ b) live)
      have gain := (opened b (kj.trans jb) n N live).2.1 w
      have fb : 0<factor C b := zero_lt_one.trans (factor_positive C b)
      have id : (factor C b)^γ * exp (γ*(C.S.scale b-C.S.scale j)) = exp (γ*(C.S.scale (b+1)-C.S.scale j)) := by
        rw [Real.rpow_def_of_pos fb,←exp_add,C.S.scale_succ]
        congr 1
        change log ((C.S.block b).val:ℝ)*γ + γ*(_-_) = _
        ring
      calc
        X (b+1) ≤ (factor C b)^γ * X b := gain
        _ ≤ (factor C b)^γ * (exp (γ*(C.S.scale b-C.S.scale j))*X j) :=
          mul_le_mul_of_nonneg_left hpre (rpow_pos_of_pos fb _).le
        _ = _ := by rw [←mul_assoc,id]
  have lk := (lambda_pos C k).le
  have age : γ*(C.S.scale t-C.S.scale j) ≤ η*L k/4 := by
    have a := mul_le_mul_of_nonneg_left span gp.le
    have b := mul_le_mul_of_nonneg_right slice lk
    change γ*(C.S.scale t-C.S.scale j) ≤ γ*(B*L k) at a
    linarith only [a,b]
  have kc := clock N n (kj.trans (jt.trans tN))
  have pos : 0 < regulatorRun C N n k := g_pos R.makes (kj.trans (jt.trans tN))
  have econ := rpow_le_rpow_of_nonpos pos kc (neg_nonpos.mpr hη.le)
  rw [rpow_def_of_pos (exp_pos _),log_exp] at econ
  have cost : exp (γ*(C.S.scale t-C.S.scale j)) ≤ (regulatorRun C N n k)^(-η) := by
    apply (exp_le_exp.mpr age).trans
    simpa only [show η*L k/4 = (-L k/4)*(-η) by ring] using econ
  exact (walk t jt tN).trans (mul_le_mul_of_nonneg_right cost (size_nonneg _ _))

/-- This is precisely the inverse matrix product: pull the input through the
    original measured fitting at the earlier level, then read the very same
    bare vector in the genuine fitting at the later level. -/
theorem inverse (R : Run G) (hG : G.Simple) (d : ℕ) (B : ℝ) (hB : 0 ≤ B) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n j t (_ : k≤j) (jt : j≤t) (tN : t≤N),
      R.family.S.scale t-R.family.S.scale j ≤ B*Lambda R.family.path.levels k →
        ∃ a : Opened R.family d j n, ∃ b : Opened R.family d t n, ∀ x,
          (R.family.labels.level d).coeffSize ((fitting d N n t R.makes b tN)
            ((fitting d N n j R.makes a (jt.trans tN)).symm x)) ≤
            (regulatorRun R.family N n k)^(-η)*(R.family.labels.level d).coeffSize x := by
  obtain ⟨cut,hcut⟩ := eventually_atTop.mp (open_late R.family hG d)
  filter_upwards [coordinates R hG d B hB hη,eventually_ge_atTop cut] with k all opened
  intro N n j t kj jt tN age
  let a := hcut j (opened.trans kj) n
  let b := hcut t (opened.trans (kj.trans jt)) n
  refine ⟨a,b,?_⟩
  intro x
  let Fj := fitting d N n j R.makes a (jt.trans tN)
  let Ft := fitting d N n t R.makes b tN
  have h := all N n j t kj jt tN age (Fj.symm x)
  change _ ≤ _*(R.family.labels.level d).coeffSize (Fj (Fj.symm x)) at h
  rw [Fj.apply_symm_apply x] at h
  exact h

end YM.Integration.WilsonPhysicalHistoryInverse

