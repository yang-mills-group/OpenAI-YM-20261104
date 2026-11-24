import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite

/-! A previous curvature atom only spends the face at each of its stored
path ends. The compact transporter on the full original path acts isometrically. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson WilsonCoeffUV.Bank.Mosaic
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {k : ℕ}

def tip (a : Slot) (U : Config G n) (x : Site n) : ℝ :=
  G.chord (faceValue (expandAt x U) (a.offset,a.plaq))

theorem atom_tips (a : Atom G k) (x : Site n) (U : Config G n) :
    |a.unmasked U x| ≤ a.magnitude * ∏ i,tip (a.leg i) U x := by
  have coordinate (i j) : |(a.leg i).atSite U x j|≤tip (a.leg i) U x := calc
    _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) ((a.leg i).atSite U x)| := by
      simp only [EuclideanSpace.basisFun_inner]
    _ ≤ _ := (abs_real_inner_le_norm _ _).trans <| by
      rw [OrthonormalBasis.norm_eq_one,one_mul]
      unfold Slot.atSite Slot.eval tip
      rw [G.norm_adjoint]
      exact G.curvature_norm _
  unfold Atom.unmasked Atom.poly Atom.magnitude
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_)
  intro b _
  rw [abs_mul,Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=>abs_nonneg _)
    (fun i _=>coordinate i (b i))) (abs_nonneg _)

theorem site_tips (A : ℕ→Atom G k) {σ C : ℝ} (pos : 0<σ)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (U : Config G n)
    {b : ℝ} (hb : 0≤b)
    (tips : ∀ s : Signed,∀ i : ℕ,∀ j : Fin k,tip ((A i).leg j) (pull s 0 U) x≤b) :
    |sitePacket A x U|≤ C*b^k := by
  apply mean_bound
  intro s
  let f:=fun i : ℕ=>(A i).unmasked (pull s 0 U) x
  let B:=fun i : ℕ=>(A i).budget σ*b^k
  have sum : Summable B:=paid.2.1.mul_right _
  have bound (i : ℕ) : ‖f i‖≤B i := by
    have all : (∏ h,tip ((A i).leg h) (pull s 0 U) x)≤b^k := by
      have hh : (∏ h,tip ((A i).leg h) (pull s 0 U) x)≤∏ _h : Fin k,b :=
        Finset.prod_le_prod (fun h _=>show 0≤tip ((A i).leg h) (pull s 0 U) x from G.chord_nonneg _)
          (fun h _=>tips s i h)
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
    exact (atom_tips (A i) x (pull s 0 U)).trans (mul_le_mul
      ((A i).lower_budget σ pos) all (Finset.prod_nonneg fun _ _=>G.chord_nonneg _)
      (paid.1 i))
  have hnorm : Summable (fun i=>‖f i‖) :=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) bound sum
  apply (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum bound sum).trans ?_)
  change ∑' i,(A i).budget σ*b^k≤C*b^k
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right paid.2.2 (pow_nonneg hb _)

end YM.Integration.OriginalMarkedRunAction
