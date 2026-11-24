import YM.Integration.WilsonIndependentCollarConnectedFilm

/-! Sum the true far relative-copy and group-atom leases on a finite
physical board. The bound is uniform in the choice and size of the board. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarFarCopies
open Function Finset Filter Lattice Wilson RG Precision PhysicalNext.Repeat.Legato Exterior Work.F08 MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open FundedMarkedPathSelection WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e m N l j:ℕ} {A:ℝ}

theorem tail {α:Type*} {w M:ℝ} (d f:α→ℝ) (positive:0≤w)
    (paid:SumBudget (fun u=>Real.exp (w*d u)*f u) M)(seats:Finset α) (R:ℝ)
    (far:∀u∈seats,R≤d u):
    ∑u∈seats,f u ≤ Real.exp (-(w*R))*M:=by
  have sign (u):0≤f u:=(mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (paid.1 u)
  have bound:Real.exp (w*R)*(∑u∈seats,f u) ≤ M:=calc
    _=∑u∈seats,Real.exp (w*R)*f u:=Finset.mul_sum _ _ _
    _≤∑u∈seats,Real.exp (w*d u)*f u:=Finset.sum_le_sum fun u h=>
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (far u h) positive)) (sign u)
    _≤_:= (paid.2.1.sum_le_tsum seats (fun u _=>paid.1 u)).trans paid.2.2
  calc
    _=Real.exp (-(w*R))*(Real.exp (w*R)*(∑u∈seats,f u)):=by
      rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
    _≤_:=mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le

omit [Fintype ι] in
theorem original {S J:Finset ι}{c:ι}(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)
    (X:Input Q hm S k D A){o:Cover}{r:Fin (l+j+1)}{t B:ℝ}(positive:0≤t)
    (paid:Rooted Q hm X J c l N t B o j r):
    let pkg:=fun x:Frill J c × RadP G r.val=>packetH J (output X J N) l (e+1) c o x.1 j r x.2
    ∃ μ:(Frill J c × RadP G r.val)→Stationary.Ink G r.val→Measure (Sky D),
      (∀x,Barn (pkg x) (μ x)) ∧
      (∀x (test:Case D) {n:Side} (field:Config G n) (p:Site n),
        (Rolls.dip (pkg x) (touch test J)).unmasked field p =
        ∑a,(∫y:Sky D,Express.mica test J y ∂μ x a)*(sprigB (pkg x) a).unmasked field p) ∧
      (∀ (seats:Finset (Frill J c × RadP G r.val)) R,
        (∀x∈seats,R≤feeH (toe J c o x.1) c J) →
        ∑x∈seats,lease (pkg x) (μ x) t ≤ Real.exp (-(t*R))*B):=by
  intro pkg
  obtain ⟨μ,born,exactWord,salary,_⟩:=paid
  refine ⟨μ,born,exactWord,?_⟩
  intro seats R far
  exact tail (α:=Frill J c × RadP G r.val) (w:=t) (M:=B)
    (fun x=>(feeH (toe J c o x.1) c J:ℝ)) (fun x=>lease (pkg x) (μ x) t) positive salary seats R
    (fun x hx=>by exact_mod_cast far x hx)

end YM.Integration.WilsonIndependentCollarFarCopies
end
