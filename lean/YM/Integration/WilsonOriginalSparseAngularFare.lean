import YM.Integration.WilsonOriginalCensusChildReading

/-! Pay each short ordered tuple on the occupied hull and use the individual
exponential wages of both prints for everything outside it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseAngularFare
open Finset
open scoped Classical BigOperators
variable {I:Type} [Fintype I]

def pegs (H:Finset I)(r:ℕ) : Finset (Fin r→I):=Fintype.piFinset (fun _=>H)

omit [Fintype I] in
theorem count (H:Finset I)(r:ℕ):(pegs H r).card=H.card^r:=by
  simp [pegs,Fintype.card_piFinset]

private theorem weight {a R d:ℝ}(pos:0≤a)(outside:R≤d)(q:ℝ)(hq:0≤q):
    q≤Real.exp (-(a*R))*(Real.exp (a*d)*q):=by
  rw [←mul_assoc,←Real.exp_add]
  exact le_mul_of_one_le_left hq ((Real.one_le_exp_iff).mpr (by nlinarith))

theorem rank (H:Finset I)(r:ℕ)(L U:(Fin r→I)→ℂ)(span:(Fin r→I)→ℝ)
    (R σ τ δ costL costU:ℝ)(spos:0≤σ)(tpos:0≤τ)
    (localRead:∀z, (∀j,z j∈H) → ‖L z-U z‖≤δ)
    (away:∀z,z∉pegs H r → R ≤ span z)
    (left:∑z,Real.exp (σ*span z)*‖L z‖≤costL)
    (right:∑z,Real.exp (τ*span z)*‖U z‖≤costU):
    ∑z,‖L z-U z‖≤(H.card:ℝ)^r*δ+Real.exp (-(σ*R))*costL+Real.exp (-(τ*R))*costU:=by
  classical
  let A:=pegs H r
  have localSum:(∑z:Fin r→I,if z∈A then δ else 0)=(H.card:ℝ)^r*δ:=by
    simp [A,Finset.sum_ite_mem,count]
  calc
    _ ≤ ∑z,((if z∈A then δ else 0)+Real.exp (-(σ*R))*(Real.exp (σ*span z)*‖L z‖)+
        Real.exp (-(τ*R))*(Real.exp (τ*span z)*‖U z‖)):=by
      apply sum_le_sum
      intro z _
      by_cases h:z∈A
      · rw [if_pos h]
        apply (localRead z (Fintype.mem_piFinset.mp h)).trans
        have lo:0≤Real.exp (-(σ*R))*(Real.exp (σ*span z)*‖L z‖):=by positivity
        have hi:0≤Real.exp (-(τ*R))*(Real.exp (τ*span z)*‖U z‖):=by positivity
        linarith
      · rw [if_neg h,zero_add]
        exact (norm_sub_le _ _).trans (add_le_add
          (weight spos (away z h) _ (norm_nonneg _)) (weight tpos (away z h) _ (norm_nonneg _)))
    _ ≤ _:=by
      rw [sum_add_distrib,sum_add_distrib,localSum,←mul_sum,←mul_sum]
      exact add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left left (Real.exp_nonneg _)) _)
        (mul_le_mul_of_nonneg_left right (Real.exp_nonneg _))

theorem mass (H:Finset I)(d:ℕ)(L U:(r:ℕ)→(Fin r→I)→ℂ)(span:(r:ℕ)→(Fin r→I)→ℝ)
    (R σ τ:ℝ)(δ costL costU:ℕ→ℝ)(spos:0≤σ)(tpos:0≤τ)
    (localRead:∀r≤d,∀z,(∀j,z j∈H)→‖L r z-U r z‖≤δ r)
    (away:∀r≤d,∀z,z∉pegs H r→R ≤ span r z)
    (left:∀r≤d,∑z,Real.exp (σ*span r z)*‖L r z‖≤costL r)
    (right:∀r≤d,∑z,Real.exp (τ*span r z)*‖U r z‖≤costU r):
    WilsonEmittedAngularJointFare.mass (fun r z=>L r z-U r z) d ≤
      ∑r∈range (d+1),((H.card:ℝ)^r*δ r+Real.exp (-(σ*R))*costL r+Real.exp (-(τ*R))*costU r):=by
  unfold WilsonEmittedAngularJointFare.mass
  apply sum_le_sum
  intro r hr
  have h:=Nat.le_of_lt_succ (mem_range.mp hr)
  exact rank H r (L r) (U r) (span r) R σ τ (δ r) (costL r) (costU r)
    spos tpos (localRead r h) (away r h) (left r h) (right r h)

end YM.Integration.WilsonOriginalSparseAngularFare
end
