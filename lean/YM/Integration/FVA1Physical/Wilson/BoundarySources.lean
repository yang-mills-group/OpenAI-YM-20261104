import YM.Integration.FVA1Physical.Wilson.LeadingMass

/-! Actual localized exponential insertions at a retained boundary. The entire
inherited action cancels in the tilt, leaving only the changed noise link factors
on the immediately incoming field. For disjoint supports the factors multiply
before integrating against the actual joint conditional law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Set MeasureTheory Lattice RG YM.Wilson Tree Push.BetaTransport Pressure
open RGComparison.Core16 RGComparison.Core16.Descent
open scoped Classical BigOperators
variable {G : Gauge} {n c f : Side} (d : Descent n c)

def boundaryGain (β : ℕ → ℝ) (U V : Config G c) (t : d.Tags) (x : Fields G d) : ℝ :=
  Real.exp (d.account β t U x - d.account β t V x)

def boundaryRead (β : ℕ → ℝ) (U V : Config G c) : ℝ :=
  (∑ t, ∫ x, d.integrand β t 1 U x * boundaryGain d β U V t x ∂d.measure G) / massAt d β U

theorem boundary_read_eq (h : d.OK G) (β : ℕ → ℝ) (U V : Config G c) :
    boundaryRead d β U V = d.vacuum β V / d.vacuum β U := by
  have kernel (t : d.Tags) (x : Fields G d) : d.integrand β t 1 U x * boundaryGain d β U V t x =
      d.integrand β t 1 V x := by
    simp only [integrand,Pi.one_apply,mul_one,boundaryGain,mul_assoc,←Real.exp_add]
    congr 2
    ring
  rw [boundaryRead,mass_density d h β V,mass_density d h β U,mul_div_mul_left _ _ (scalar_pos G d β).ne']
  simp_rw [kernel]
  rfl

variable {S : StepData c f} (F : Forest S.ratio) (p : Descent n f)

def varyBonds (A : Finset (Bond c)) (U V : Config G c) : Config G c := fun e => if e∈A then V e else U e

def linkGain (S : StepData c f) (β : ℝ) (Q U V : Config G c) (e : Bond c) : ℝ :=
  Real.exp (β * (linkEnergy S (U e * (Q e)⁻¹) - linkEnergy S (V e * (Q e)⁻¹)))

/-- Exact outer-edge factors for the actual block on every predecessor history. -/
theorem gain_at_bonds (β : ℕ→ℝ) (A : Finset (Bond c)) (U V : Config G c)
    (t : (push S F p).Tags) (x : Fields G (push S F p)) :
    boundaryGain (push S F p) β U (varyBonds A U V) t x =
      ∏ e ∈ A, linkGain S (β 1) (S.prediction (F.drape (x ∘ Sum.inl)) t.1) U V e := by
  let Q := S.prediction (F.drape (x ∘ Sum.inl)) t.1
  let price (V : Config G c) (e : Bond c) := linkEnergy S (V e*(Q e)⁻¹)
  have sum : (∑ e, (price U e - price (varyBonds A U V) e)) = ∑ e∈A, (price U e - price V e) := by
    have small := Finset.sum_subset (Finset.subset_univ A) (f:=fun e=>price U e-price (varyBonds A U V) e)
      (fun e _ he=>by simp only [varyBonds,price,if_neg he,sub_self])
    exact small.symm.trans (Finset.sum_congr rfl (fun e he=>by simp only [price,varyBonds,if_pos he]))
  unfold boundaryGain linkGain
  rw [←Real.exp_sum,account,account,add_sub_add_right_eq_sub,←mul_sub,tagEnergy,tagEnergy,noiseEnergy,noiseEnergy,←Finset.sum_sub_distrib]
  change Real.exp (β 1*(∑ e, (price U e-price (varyBonds A U V) e))) = Real.exp (∑ e∈A,β 1*(price U e-price V e))
  rw [sum,Finset.mul_sum]

/-- The joint insertion is literally the product of the single supported insertions.
The likelihood, common tree and all inner actions remain in the reference law. -/
theorem gain_disjoint (β : ℕ→ℝ) {A B : Finset (Bond c)} (hAB : Disjoint A B)
    (U V : Config G c) (t : (push S F p).Tags) (x : Fields G (push S F p)) :
    boundaryGain (push S F p) β U (varyBonds (A∪B) U V) t x =
      boundaryGain (push S F p) β U (varyBonds A U V) t x *
        boundaryGain (push S F p) β U (varyBonds B U V) t x := by
  simp only [gain_at_bonds,Finset.prod_union hAB]

end YM.Integration.FVA1Physical.Wilson
