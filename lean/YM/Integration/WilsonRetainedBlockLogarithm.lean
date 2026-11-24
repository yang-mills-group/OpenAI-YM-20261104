import YM.LocalTaylorR2.Exponent.Shill
import YM.LocalLTE.Weft.Valued

/-! The signed nonlinear block coefficient, with its inherited coarse mean on the original forest. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedBlockLogarithm

open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port LocalTaylorR2.Pavilion LocalTaylorR2.Exponent
open Work.G05 Analysis
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
  {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
  {R : Rep G f} {H : Cash W s μ L Q o C T R}

def letter (i : Coat.Stream c f) : LogIndex c f := .inr (.inl (.inl i))

private theorem mean_head (funds : P.Funds S T) (X : Coat T F) (i : Coat.Stream c f) :
    Pavilion.meanV X i 0=0 ∧ fderiv ℝ (Pavilion.meanV X i) 0=0 := by
  let Y:=X.wrapY 1
  have a : Pavilion.drip X (0 : ZipP G c f)=Y.blank := by
    unfold Pavilion.drip dry
    simp only [Prod.fst_zero,Work.G07.at_zero_increment]
    rfl
  have b : timeΛ Y 0=Y.blank := by
    unfold timeΛ Vine.pass dry
    simp only [Prod.snd_zero,Work.G07.at_zero_increment]
    rfl
  have hz : voltage Y.blank=0 := b ▸ LocalLTE.Fan.volt0 Y funds
  have zero : Pavilion.meanV X i 0=0 := by
    unfold Pavilion.meanV
    rw [a,hz]
    apply Finset.sum_eq_zero
    intro k _
    unfold Vine.pot
    split
    · rw [LocalLTE.Fan.strain0 funds Y i.1 k,norm_zero]
      norm_num
    · rfl
  refine ⟨zero,IsLocalMin.fderiv_eq_zero ?_⟩
  apply Filter.Eventually.of_forall
  intro x
  change Pavilion.meanV X i 0 ≤ Pavilion.meanV X i x
  rw [zero]
  apply Finset.sum_nonneg
  intro k _
  unfold Vine.pot
  split <;> positivity

/-- A single spatial occurrence keeps its two measured directions separate. -/
def row (n : ℕ) (X : Coat T F) (i : Coat.Stream c f) (a : ℝ) (v y : ZipP G c f) : ℝ :=
  if Inside (rowSite S i) X.seeds (200*X.B) then 0 else
    -Raw.orientation * (a * Tensor.diagonal (Tensor.coeff (ivy T X.x (choice i.1 X.k) i.2) n 0) v +
      Tensor.diagonal (Tensor.coeff (Pavilion.meanV X i) n 0) y)

theorem starts (simple : G.Simple) (funds : P.Funds S T) (X : Coat T F) (i : Coat.Stream c f)
    (a : ℝ) (v y : ZipP G c f) : row 0 X i a v y=0 ∧ row 1 X i a v y=0 := by
  have m:=mean_head funds X i
  have k : fderiv ℝ (ivy T X.x (choice i.1 X.k) i.2) 0=0 := by
    by_cases h : DifferentiableAt ℝ (ivy T X.x (choice i.1 X.k) i.2) 0
    · exact LocalLTE.Fan.criticalV simple _ _ _ funds h
    · exact fderiv_zero_of_not_differentiableAt h
  by_cases inside : Inside (rowSite S i) X.seeds (200*X.B)
  · simp [row,inside]
  · constructor
    · simp only [row,if_neg inside,Tensor.diagonal,Tensor.coeff_apply_zero]
      rw [LocalLTE.Fan.valence₀ funds,m.1]
      ring
    · simp [row,inside,Tensor.diagonal,Tensor.coeff,iteratedFDeriv_one_apply,k,m.2]

def value (p : ℕ) (X : Coat T F) (i : Coat.Stream c f) (a : ℝ) (u : Directions G f) : ℝ :=
  if Inside (rowSite S i) X.seeds (200*X.B) then 0 else
    -R.beta*Raw.orientation*(a*Canvas.rootTaylor (Canvas.primary G) X i (p+2) u +
      blockTaylor (p+2) (Pavilion.meanV X i) (Pavilion.pitch (Canvas.primary G) X (rowSite S i)))

theorem physical (H : Cash W s μ L Q o C T R) (p : ℕ) (X : Coat T F) (i : Coat.Stream c f) (z : Air f G) :
    let u := worldZ X R.beta z
    let a := X.enforce (2*o.a) u (X.booth (rowSite S i))
    Pavilion.mosaics H p (letter i) F X z = value (R:=R) p X i a u ∧
      Exponent.iceberg H p (letter i) F X z = value (R:=R) p X i 1 u := by
  change Canvas.pineCone _ X _ R i _ _ - Pavilion.delta (p+2) i R X = _ ∧
    (Canvas.pineCone _ X _ R i _ _ - Pavilion.delta (p+2) i R X) + trunkInc H (p+2) i F X z = _
  by_cases h : Inside (rowSite S i) X.seeds (200*X.B) <;>
    simp only [Canvas.pineCone,Pavilion.delta,Pavilion.voltageV,Pavilion.tune,Exponent.trunkInc,value,
      h,if_true,if_false] <;> constructor <;> ring

private theorem scale (p : ℕ) (X : Coat T F) (i : Coat.Stream c f) (a g : ℝ) (hg : g ≠ 0)
    (u : Directions G f) :
    value (R:=R) p X i a u =
      R.beta*∑ n∈Finset.range (p+3), g^n * row n X i a
        (g⁻¹ • Canvas.arbor (Canvas.primary G) X i u)
        (g⁻¹ • Pavilion.pitch (Canvas.primary G) X (rowSite S i)) := by
  by_cases h : Inside (rowSite S i) X.seeds (200*X.B)
  · simp [value,row,h]
  simp only [value,row,if_neg h,Canvas.rootTaylor,blockTaylor,Finset.sum_apply]
  rw [Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have weighted (K : Tensor.T (ZipP G c f) ℝ n) (v : ZipP G c f) :
      g^n * Tensor.diagonal K (g⁻¹ • v) = Tensor.diagonal K v := by
    rw [← show Tensor.diagonal K (g • g⁻¹ • v) = g^n * Tensor.diagonal K (g⁻¹ • v) from
      Tensor.homogeneous K (g⁻¹ • v) g,smul_smul,mul_inv_cancel₀ hg,one_smul]
  rw [← weighted _ (Canvas.arbor (Canvas.primary G) X i u),
    ← weighted _ (Pavilion.pitch (Canvas.primary G) X (rowSite S i))]
  ring

/-- The beta prefactor consumes precisely the first two field degrees.
The cutoff and corrected readings use the same signed coefficient map. -/
theorem measured (simple : G.Simple) (H : Cash W s μ L Q o C T R) (p : ℕ)
    (X : Coat T F) (i : Coat.Stream c f) (z : Air f G) :
    let g:=gStep R.beta
    let u:=worldZ X R.beta z
    let A:=X.enforce (2*o.a) u (X.booth (rowSite S i))
    let read a := ∑ k∈Finset.range (p+1),g^k * row (k+2) X i a
      (g⁻¹ • Canvas.arbor (Canvas.primary G) X i u)
      (g⁻¹ • Pavilion.pitch (Canvas.primary G) X (rowSite S i))
    Pavilion.mosaics H p (letter i) F X z = read A ∧ Exponent.iceberg H p (letter i) F X z = read 1 := by
  have hβ:=H.laws.intake.positive
  let g:=gStep R.beta
  have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hs : R.beta*g^2=1 := by
    dsimp [g,gStep]
    rw [inv_pow,Real.sq_sqrt hβ.le,mul_inv_cancel₀ hβ.ne']
  let u:=worldZ X R.beta z
  let v:=g⁻¹ • Canvas.arbor (Canvas.primary G) X i u
  let y:=g⁻¹ • Pavilion.pitch (Canvas.primary G) X (rowSite S i)
  have calculate (a : ℝ) : value (R:=R) p X i a u =
      ∑ k∈Finset.range (p+1),g^k*row (k+2) X i a v y := by
    rw [scale p X i a g hg.ne' u]
    change R.beta*(∑ n∈Finset.range (p+3),g^n*row n X i a v y) = _
    have head:=starts simple H.laws.data.room.accepted X i a v y
    have zero : (∑ n∈Finset.range 2,g^n*row n X i a v y)=0 := by
      simp only [Finset.sum_range_succ,Finset.sum_range_zero,head.1,head.2,mul_zero,add_zero]
    rw [show p+3=2+(p+1) by omega,Finset.sum_range_add,zero,zero_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm 2 k,pow_add]
    calc
      _ = (R.beta*g^2)*(g^k*row (k+2) X i a v y) := by ring
      _ = _ := by rw [hs,one_mul]
  exact ⟨(physical H p X i z).1.trans (calculate _),(physical H p X i z).2.trans (calculate 1)⟩

end YM.Integration.WilsonRetainedBlockLogarithm
end
