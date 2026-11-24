import YM.Integration.WilsonMatrixOriginalDeckSignedMeasurements

/-! The measured two-point signed Gram and cross-Gram bound the full transport along all dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckSignedHorizon
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato Trace.Pilot
open WilsonMatrixOriginalDeckPath WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckRelative
open WilsonMatrixOriginalDeckSignedMeasurements
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {S:Table R.family.book} {f:Extraction.Order}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- The same spatially localized original test pays a growing full-height signed error. The
input bill is the limit of the finite regulated experiment, including all off-grade entries. -/
theorem original (leading:PhysMS.Leading F J) (M:MS_Data G O) {p:E4} (hp:(0:E4)≠p)
    (U:Set (Points 2)) (near:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃ (g:Test 2) (A C:ℝ), 1≤A ∧ 0<C ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧ (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      ∀η:ℝ,0<η → ∃ready:Set ℝ,ready∈trail ∧ ∀ (r:ℕ→ℝ) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ)
        (n:ℕ) (pos:∀i,0<r i), Monotone r → (∀i≤n,r i∈ready) →
        (∀ (u:Filter (ℕ×ℕ)) [u.NeBot],u≤f.fuse →
          Tendsto (finite R B J h g r pos V n) u (𝓝 (invoice R B F J h g r V n))) ∧
        let bill := C*invoice R B F J h g r V n
        amount (steps V n-change B J h (r n) (r 0)) ≤ A^2*(r n/r 0)^η*bill*Real.exp (A*bill) := by
  obtain ⟨g,C,hC,supp,real,point,mass,all,read⟩ := WilsonMatrixOriginalDeckReturn.measured R B F J h leading M hp U near
  obtain ⟨base,basein,rows⟩ := Filter.Eventually.exists_mem read
  obtain ⟨A,hA,trajectory⟩ := WilsonMatrixOriginalDeckHorizon.original R B F J h leading
  refine ⟨g,A,C,hA,hC,supp,real,point,mass,all,?_⟩
  intro η hη
  obtain ⟨region,window,bound⟩ := trajectory η hη
  refine ⟨base∩region,inter_mem basein window,?_⟩
  intro r V n pos ordered dates
  refine ⟨fun u _ hu=>WilsonMatrixOriginalDeckSignedMeasurements.limit R B F J h g r pos V n u hu,?_⟩
  let D := ∑i∈range n,amount (V i-change B J h (r (i+1)) (r i))
  let ink := invoice R B F J h g r V n
  have estimate := bound r V n pos ordered fun i hi=>(dates i hi).2
  have signedBill : D≤C*ink := by
    dsimp only [D,ink,WilsonMatrixOriginalDeckSignedMeasurements.invoice]
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    apply WilsonMatrixOriginalDeckSignedMeasurements.columns
    intro b
    exact (rows (r (i+1)) (dates (i+1) (mem_range.mp hi)).1 (r i)).2 (V i) b
  have inkpos : 0 ≤ ink := sum_nonneg fun _ _=>WilsonMatrixOriginalDeckError.nonneg _
  have scale : 0≤A^2*(r n/r 0)^η := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (div_nonneg (pos n).le (pos 0).le) _)
  apply estimate.trans
  apply mul_le_mul (mul_le_mul_of_nonneg_left signedBill scale)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left signedBill (by linarith : 0≤A))) (Real.exp_pos _).le
  exact mul_nonneg scale (mul_nonneg hC.le inkpos)

end YM.Integration.WilsonMatrixOriginalDeckSignedHorizon
