import YM.FormalOPE.RG10.Linear

/-! More linear primitives needed to carry Ward and boundary corrections. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open MeasureTheory Filter PowerSeries
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] {F : FlatFeed Θ E}
    {W : Vertices (Θ × E)} {f b : Kernel (Θ × E)} {a : Θ × E → ℂ}
namespace FlatFeed
lemma Pays.neg (h : F.Pays a) : F.Pays (-a) := by simpa using h.smul (-1)
lemma Funded.neg (h : F.Funded f) : F.Funded (-f) := by
  intro i; rw [show row i (-f) = -row i f from funext (fun x=> by simp [row])]; exact (h i).neg
lemma average_neg (F : FlatFeed Θ E) (f : Kernel (Θ×E)) : F.average (-f) = -F.average f := by
  apply PowerSeries.ext; intro i
  have h := F.mean_smul (-1) (row i f)
  simp only [FlatFeed.average_coeff, map_neg]
  rw [show row i (-f) = -row i f from funext (fun x=> by simp [row])]; simpa using h
lemma step_add (hf : F.Funded (W.weight*f)) (hb : F.Funded (W.weight*b)) :
    F.step W (f+b) = F.step W f + F.step W b := by
  simp only [step, mul_add, FlatFeed.average_add hf hb, add_mul]
lemma step_neg : F.step W (-f) = -F.step W f := by
  simp only [step, mul_neg, FlatFeed.average_neg, neg_mul]
lemma step_sub (hf : F.Funded (W.weight*f)) (hb : F.Funded (W.weight*b)) :
    F.step W (f-b) = F.step W f - F.step W b := by
  rw [sub_eq_add_neg, step_add hf (by rw [mul_neg]; exact hb.neg), step_neg, sub_eq_add_neg]
lemma both_neg (hf : F.Funded (W.weight*f)) : F.Funded (W.weight*(-f)) := by rw [mul_neg]; exact hf.neg
lemma both_add (hf : F.Funded (W.weight*f)) (hb : F.Funded (W.weight*b)) : F.Funded (W.weight*(f+b)) := by
  rw [mul_add]; exact hf.add hb
lemma both_sub (hf : F.Funded (W.weight*f)) (hb : F.Funded (W.weight*b)) : F.Funded (W.weight*(f-b)) := by
  rw [sub_eq_add_neg]; exact both_add hf (both_neg hb)
lemma delayable (d : ℕ) (hf : F.Funded (W.weight*f)) : F.Funded (W.weight*delay d f) := by
  rw [show delay d f = outside (X^d) * f from rfl, mul_left_comm]
  exact hf.external _
lemma inSpite (d : ℕ) (hf : F.Funded (W.weight*delay d f)) : F.Funded (W.weight*f) := by
  apply F.funded_of_delay _ d
  rw [show delay d (W.weight*f) = _ from step_delay.delay_mul_right W f d]
  exact hf
end FlatFeed
end YM.FormalOPE.RG10
