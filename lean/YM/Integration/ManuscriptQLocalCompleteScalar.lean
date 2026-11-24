import YM.Integration.ManuscriptQLocalGaussianRootPrice
import YM.Integration.PhysicalAffineScalarGlobalLog

/-! The complete actually represented scalar and its prescribed independent
Gaussian reference, at a fixed translation and one changed actual tree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalCompleteScalar
open Marker Bloch Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarGlobalLog PhysicalAffineScalarCutResidual ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "Coarse" => Gaussian.Vec (Raw G c₀)
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "ρ" => ConditionalAffineSourcePrices.rate (Pt) (S).patch.L
local notation "a₀" => (Pt).top.paths
local notation "b₀" => (Pt).top.width

/-- True four terms in the represented scalar comparison, with an arbitrary
complete independent-field list and one actual changed tree site. -/
def error (k : (S).Choices) (q : Chi) (b : ℝ) (tag : Site c₀)
    (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (g : ℝ) (o : Site c₀)
    (B : Coarse) : ℝ :=
  (PhysicalAffineScalarJets.actualRoot T θ k A F'.val q b Z g o B - PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b Y g o B) -
    (PhysicalAffineScalarUncut.scalarAt T θ k F'.val g o B - PhysicalAffineScalarUncut.scalarAt T θ k d.forest g o B)

/-- Complete regular output on the original single forest, before taking
any marked tree variation. -/
def regular (k : (S).Choices) (q : Chi) (b : ℝ) (Y : LinkArray G (Frozen A θ d.forest)) (g : ℝ)
    (o : Site c₀) (B : Coarse) := PhysicalAffineScalarJets.actualRoot T θ k A d.forest q b Y g o B-
      PhysicalAffineScalarUncut.scalarAt T θ k d.forest g o B

def logFee (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (a b : ℝ) :=
  (Fintype.card (Co P.L (PAC G 1)):ℝ)*(diminish G P K p (n+1) 0 a b 0/2)

omit [Fintype I] in
private theorem lower {δ s N : ℝ} (h : δ ≤ s) (o z : Site c₀) (l : List (raw G c₀)) (x : ℝ)
    (hx : (marks G c₀ s).pay l o*((native c₀).weight s o z*|x|)≤N) :
    (marks G c₀ δ).pay l o*((native c₀).weight δ o z*|x|)≤N := by
  exact (mul_le_mul (ConditionalAffineRootContraction.pay_le (D := native c₀) (p := hearth (G := G) (r := 1)) h l o)
    (mul_le_mul_of_nonneg_right ((native c₀).weight_mono h o z) (abs_nonneg _))
    (mul_nonneg ((native c₀).weight_nn ..) (abs_nonneg _)) ((marks G c₀ s).pay_pos ..).le).trans hx

omit [Fintype I] in
theorem original {order : ℕ→ℕ→ℕ} (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit) :
    let n := order (j₁) (j₀)
    let r := paid.choose (j₁) (j₀)
    let u := ConditionalAffineLoadPrices.fullFee G (S).patch.L n r.ordinary r.discarded ρ θ
    let κ := min ρ (b₀/4)
    let w := width G (S).patch (S).kernel (T).high (n+1) a₀ b₀
    let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G (S).patch (S).kernel (T).high (Pt) n r.spatial
    let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G (Pt) (S).patch.L n
    0<δ ∧ 0<M ∧ 0 < min δ w ∧ 0<κ ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ) (tag : Site c₀)
    (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (g : ℝ) (o : Site c₀)
    (l : List (raw G c₀)), l.length≤n →
      ((marks G c₀ (min δ w)).pay l o*((native c₀).weight (min δ w) o tag*
        |jet (ray G c₀) (error R d k q b tag F' Y Z g o) l 0|) ≤
      (ManuscriptQLocalGaussianRootPrice.prefactor G (S).patch (S).kernel (T).high n a₀ b₀ δ (u+|slip| * M) u (|slip| * M) g+
        logFee G (S).patch (S).kernel (T).high n a₀ b₀)*Real.exp (-κ*(till θ:ℝ))) ∧
      ((marks G c₀ (min δ w)).pay l o*|jet (ray G c₀) (regular R d k q b Y g o) l 0|≤
      (ManuscriptQLocalGaussianRootPrice.prefactor G (S).patch (S).kernel (T).high n a₀ b₀ δ (u+|slip| * M) u (|slip| * M) g+
        logFee G (S).patch (S).kernel (T).high n a₀ b₀)*Real.exp (-κ*(till θ:ℝ))) := by
  intro n r u κ w δ M
  obtain ⟨hδ,hM,hκ,hS⟩ := ManuscriptQLocalGaussianRootPrice.original R d paid
  have hb := (Pt).top.width_pos
  have ha := (Pt).top.paths_pos.le
  have hw := (gauged G (S).patch (S).kernel (T).high (n+1) hb ha).pos
  refine ⟨hδ,hM,lt_min hδ hw,hκ,?_⟩
  have hPt := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hW₀,_⟩ := hPt.feeds
  have hW : Sheet (T).up b₀ a₀ := hW₀.rows
  obtain ⟨τ,K,Λ,hp,hT⟩ := ManuscriptQLocalRootWeights.purchased R d
  have he := ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below
  intro k q b tag F' Y Z g o l hl
  let X := ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o
  let L := fun B => logGap T θ k F'.val o B-logGap T θ k d.forest o B
  let t := min δ w
  let W := (marks G c₀ t).pay l o*(native c₀).weight t o tag
  have hW₁ : 0≤W := mul_nonneg ((marks G c₀ t).pay_pos ..).le ((native c₀).weight_nn ..)
  have qpos := ManuscriptQLocalRootWeights.positive R d k
  have h₁ := hS k q b tag F' Y Z g o l hl
  have h₂ := PhysicalAffineScalarGlobalLog.charged T θ k d.forest F'.val o tag F'.prop hb ha hW he hp hT qpos n l hl
  have s₂ : ContDiffAt ℝ n L 0 := (PhysicalAffineScalarGlobalLog.regular T θ k F'.val o hb ha hW he hp hT (qpos F'.val)).sub
    (PhysicalAffineScalarGlobalLog.regular T θ k d.forest o hb ha hW he hp hT (qpos d.forest))
  have hsplit : error R d k q b tag F' Y Z g o=fun B => X B+L B := by funext B; unfold X L error ManuscriptQLocalRootPrice.error; ring
  have z₁ := lower R d (min_le_left δ w) o tag l _ h₁.1.2
  have z₂ := lower R d (min_le_right δ w) o tag l _ h₂
  have e : Real.exp (-(b₀/4)*(till θ:ℝ))≤Real.exp (-κ*(till θ:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right ..)) (by positivity))
  have hz : 0≤logFee G (S).patch (S).kernel (T).high n a₀ b₀ :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (cut_nonneg hb ha (by norm_num) 0) (by norm_num))
  constructor
  · rw [hsplit,jet_add (ray G c₀) l (smooth_of_le h₁.1.1 hl) (smooth_of_le s₂ hl),←mul_assoc]
    calc
      _ ≤ W*(|jet (ray G c₀) X l 0|+|jet (ray G c₀) L l 0|) := mul_le_mul_of_nonneg_left (abs_add_le ..) hW₁
      _ = W*|jet (ray G c₀) X l 0|+W*|jet (ray G c₀) L l 0| := mul_add ..
      _ ≤ _ := by
        rw [add_mul]
        rw [←mul_assoc] at z₁ z₂
        exact add_le_add z₁ (z₂.trans (mul_le_mul_of_nonneg_left e hz))
  · let E : Coarse → ℝ := squareGap T θ k d.forest q b Y g o
    let H : Coarse → ℝ := logGap T θ k d.forest o
    have hH : ContDiffAt ℝ n H 0 := PhysicalAffineScalarGlobalLog.regular T θ k d.forest o hb ha hW he hp hT (qpos d.forest)
    have hE : ContDiffAt ℝ n E 0 := h₁.2.1
    have hsum : regular R d k q b Y g o=fun B => E B+H B := by
      funext B; exact (PhysicalAffineScalarCutResidual.root T θ k d.forest q b Y g o B).trans (add_comm _ _)
    have gH := PhysicalAffineScalarGlobalLog.ordinary T θ k d.forest o hb ha hW he hp hT (qpos d.forest) n l hl
    have smallSquare := (mul_le_mul_of_nonneg_right (ConditionalAffineRootContraction.pay_le (D := native c₀) (p := hearth (G := G) (r := 1)) (min_le_left δ w) l o) (abs_nonneg (jet (ray G c₀) E l 0))).trans h₁.2.2
    have smallLog := (mul_le_mul_of_nonneg_right (ConditionalAffineRootContraction.pay_le (D := native c₀) (p := hearth (G := G) (r := 1)) (min_le_right δ w) l o) (abs_nonneg (jet (ray G c₀) H l 0))).trans gH
    rw [hsum,jet_add (ray G c₀) l (smooth_of_le hE hl) (smooth_of_le hH hl)]
    calc
      _ ≤ (marks G c₀ t).pay l o*(|jet (ray G c₀) E l 0|+|jet (ray G c₀) H l 0|) :=
        mul_le_mul_of_nonneg_left (abs_add_le ..) ((marks G c₀ t).pay_pos ..).le
      _ = _ := mul_add ..
      _ ≤ _ := by rw [add_mul]; exact add_le_add smallSquare (smallLog.trans (mul_le_mul_of_nonneg_left e hz))

end YM.Integration.ManuscriptQLocalCompleteScalar

