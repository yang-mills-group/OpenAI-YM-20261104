import YM.Integration.WilsonGaussianMeasuredFourthTest

/-! The forward quartic coefficient along one scalar field ray. On the diagonal the three
polarized source pairings produce a sum of squares at the original root. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianMeasuredFourthRay
open Marker Function Filter Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarIdealSquare
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

private theorem size_repeat {E : Type} [Norm E] (n : ℕ) (v : E) :
    WilsonGaussianMeasuredFourthTest.size (List.replicate n v)=‖v‖^n := by
  simp [WilsonGaussianMeasuredFourthTest.size]

private theorem divide {x y L q ε : ℝ} (estimate : |x-y| ≤ ε) (formula : y/24=L-q) (hq : 0 ≤ q) :
    |x/24-(L-q)| ≤ ε/24 ∧ x/24 ≤ L+ε/24 := by
  have h : |x/24-y/24| ≤ ε/24 := by
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<24)]
    exact div_le_div_of_nonneg_right estimate (by norm_num)
  rw [formula] at h
  exact ⟨h,by linarith [(abs_le.mp h).2]⟩

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

def squares (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (v : E) : ℝ :=
  ∑ i : Rows.Receipt G S, if PhysicalAffineScalarComparison.rowRoot (G:=G) S i=o then
    (jet id (fun B => residual T k F B i) [v,v] 0)^2 else 0

theorem squares_nonneg (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (v : E) :
    0 ≤ squares R d k F o v :=
  by
    unfold squares
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

theorem diagonal (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (v : E) :
    ManuscriptQLocalGaussianQuartic.completeCoefficient R d k F o id v v v v / 24 =
      g₀^4/24 * jet id (PhysicalAffineScalarSpectralRoot.halfLog T k F o) [v,v,v,v] 0 -
      g₀^2/8 * squares R d k F o v := by
  have pairs : ManuscriptQLocalGaussianQuartic.coefficient R d k F o id v v v v =
      3*squares R d k F o v := by
    unfold ManuscriptQLocalGaussianQuartic.coefficient squares
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : PhysicalAffineScalarComparison.rowRoot (G:=G) S i=o
    · simp only [hi,if_true,ManuscriptQLocalGaussianQuartic.pairings]; ring
    · simp only [hi,if_false,mul_zero]
  rw [ManuscriptQLocalGaussianQuartic.completeCoefficient,pairs]
  ring

theorem measured [Fintype I] {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalStoredGaussianScalar.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (t : ℝ) (z : Site c₀)
    (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen (PhysicalAffineScalarAperture.noHole S) (R.alloy.B.a.clock.hatBeta d.level) d.forest))
    (Z : LinkArray G (Frozen (PhysicalAffineScalarAperture.noHole S) (R.alloy.B.a.clock.hatBeta d.level) U.val))
    (o : Site c₀) (v : E) (h₄ : 4 ≤ n (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))
    {m : ℕ} {C : ℝ} (hm : 4 ≤ m) (bound : Through m (ManuscriptQLocalScalarFields.regular R d k q t Y o) 0 C) :
    let observed := jet id (ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q t Y o) [v,v,v,v] 0 / 24
    let det := g₀^4/24 * jet id (PhysicalAffineScalarSpectralRoot.halfLog T k d.forest o) [v,v,v,v] 0
    let price := g₀^4*(C*‖v‖^4)/24
    |observed-(det-g₀^2/8*squares R d k d.forest o v)| ≤ price ∧ observed ≤ det+price := by
  have law := (ManuscriptQLocalMeasuredQuartic.original R d p k q t z U Y Z o h₄ id v v v v).1
  have h := WilsonGaussianMeasuredFourthTest.error_of_jet [v,v,v,v] hm g₀ law bound
  have size : WilsonGaussianMeasuredFourthTest.size [v,v,v,v]=‖v‖^4 := size_repeat 4 v
  rw [size] at h
  exact divide h (diagonal R d k d.forest o v)
    (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (squares_nonneg R d k d.forest o v))

end YM.Integration.WilsonGaussianMeasuredFourthRay
