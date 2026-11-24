import YM.Integration.WilsonGaussianSourcePartitions

/-! On the actual no-hole step, every marked coefficient of the independently
prescribed Gaussian is an explicit polynomial of the running coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianSourcePolynomial
open Marker Bloch FullQLocal.RenderedStep Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarIdealSquare
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "rp" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

def polynomial {ι : Type*} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (v : ι→E) (l : List ι) (g : ℝ) : ℝ :=
  g^l.length * jet v (PhysicalAffineScalarSpectralRoot.halfLog T k F o) l 0 -
    g^(l.length-2)/2 * WilsonGaussianSourcePartitions.source R d k F o v l

omit [Fintype I] in
theorem first_orders {ι : Type*} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (v : ι→E) (l : List ι) (g : ℝ) (few : l.length ≤ 3) :
    polynomial R d k F o v l g = g^l.length*jet v (PhysicalAffineScalarSpectralRoot.halfLog T k F o) l 0 := by
  rw [polynomial,WilsonGaussianSourcePartitions.below_four R d k F o v l few,mul_zero,sub_zero]

private theorem one {ι : Type*} {m : ℕ} {δ C : ℝ} (k : (S).Choices) (F : Forest (S).ratio)
    (o : Site c₀) (g : ℝ) (hg : 0 < g) (v : ι→E) (l : List ι) (hl : l.length ≤ m)
    (hm : 1 ≤ m) (H : ConditionalAffineLoadPrices.Paid rp δ C m (residual T k F))
    (hL : ContDiffAt ℝ l.length (PhysicalAffineScalarSpectralRoot.halfLog T k F o) 0) :
    let f := fun B : E => PhysicalAffineScalarSpectralRoot.halfLog T k F o (g • B)+
      ManuscriptQLocalIdealSquare.graded R d k F g o B
    ContDiffAt ℝ l.length f 0 ∧ jet v f l 0=polynomial R d k F o v l g := by
  intro f
  let L := PhysicalAffineScalarSpectralRoot.halfLog T k F o
  have atZero : ContDiffAt ℝ l.length L (g • (0:E)) := by simpa only [smul_zero] using hL
  have logSmooth : ContDiffAt ℝ l.length (fun B : E => L (g • B)) 0 :=
    atZero.comp 0 (g • ContinuousLinearMap.id ℝ E).contDiff.contDiffAt
  have sqSmooth := smooth_of_le (ManuscriptQLocalIdealSquare.graded_smooth R d k F g o H) hl
  refine ⟨logSmooth.add sqSmooth,?_⟩
  calc
    jet v f l 0 = jet v (fun B : E => L (g • B)) l 0 +
        jet v (ManuscriptQLocalIdealSquare.graded R d k F g o) l 0 := jet_add v l logSmooth sqSmooth
    _ = _ := by
      rw [PhysicalAffineScalarIdealGrading.pulled_jet g v L l hL,
        WilsonGaussianSourcePartitions.graded_jet R d k F o H hm hg v l hl]
      unfold polynomial L
      ring

/-- The same paid row data determine the coefficient for every positive coupling,
with the physical operators, rooted set and marked directions held fixed. -/
theorem running {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (v : ι→E) (l : List ι)
    (hl : l.length ≤ n j₁ j₀) (g : ℝ) (hg : 0<g) :
    let f := fun B : E => PhysicalAffineScalarSpectralRoot.halfLog T k F o (g • B)+
      ManuscriptQLocalIdealSquare.graded R d k F g o B
    ContDiffAt ℝ l.length f 0 ∧ jet v f l 0 = polynomial R d k F o v l g := by
  let P := query R.metals.p R.metals.K j₁ j₀
  have funded := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hW,_⟩ := funded.feeds
  have unchanged : changed S F F o := fun _ _ => Iff.rfl
  have H := ManuscriptQLocalIdealSquare.realized R d p k F F o unchanged
  have logPrice := ManuscriptQLocalGaussianScalar.logarithm T k (n:=l.length)
    P.top.width_pos P.top.paths_pos.le hW.rows
    (ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below) F F o o unchanged [] (by simp)
  exact one R d k F o g hg v l (hl.trans (le_max_right ..)) (le_max_left ..) H.left logPrice.1

theorem physical {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (v : ι→E) (l : List ι)
    (hl : l.length ≤ n j₁ j₀) :
    ContDiffAt ℝ l.length (ManuscriptQLocalGaussianScalar.scalar R d k F o) 0 ∧
    jet v (ManuscriptQLocalGaussianScalar.scalar R d k F o) l 0=polynomial R d k F o v l g₀ := by
  have e : ManuscriptQLocalGaussianScalar.scalar R d k F o = fun B : E =>
      PhysicalAffineScalarSpectralRoot.halfLog T k F o (g₀ • B)+ManuscriptQLocalIdealSquare.graded R d k F g₀ o B := by
    funext B
    unfold ManuscriptQLocalGaussianScalar.scalar ManuscriptQLocalIdealSquare.graded
    abel
  rw [e]
  exact running R d p k F o v l hl g₀ (ManuscriptQLocalIdealSquare.fine R d p).1

theorem changed {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (F : Forest (S).ratio) (z : Site c₀) (U : {U : Forest (S).ratio // FreeResolvent.Affine.changed S F U z})
    (o : Site c₀) (v : ι→E) (l : List ι) (hl : l.length ≤ n j₁ j₀) :
    jet v (fun B => ManuscriptQLocalGaussianScalar.scalar R d k U.val o B-
      ManuscriptQLocalGaussianScalar.scalar R d k F o B) l 0 =
      polynomial R d k U.val o v l g₀-polynomial R d k F o v l g₀ := by
  obtain ⟨hu,eU⟩ := physical R d p k U.val o v l hl
  obtain ⟨hf,eF⟩ := physical R d p k F o v l hl
  let subJet := @FreeResolvent.TestD.jet_sub ι E ℝ Pi.normedAddCommGroup Pi.normedSpace Real.normedAddCommGroup _ v
  exact (subJet l (A:=ManuscriptQLocalGaussianScalar.scalar R d k U.val o) (B:=ManuscriptQLocalGaussianScalar.scalar R d k F o) hu hf).trans (congrArg₂ (fun x y : ℝ => x-y) eU eF)

end YM.Integration.WilsonGaussianSourcePolynomial
