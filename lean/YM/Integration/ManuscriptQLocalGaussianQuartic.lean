import YM.Integration.ManuscriptQLocalGaussianScalar

/-! The first surviving mixed quartic in the independently prescribed
stationary square on the measured no-hole step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalGaussianQuartic
open Marker Bloch FullQLocal.RenderedStep Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarIdealSquare
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section polarization
variable {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def pairings (v : ι→X) (f : X→ℝ) (a b c d : ι) : ℝ :=
  jet v f [a,b] 0 * jet v f [c,d] 0 + jet v f [a,c] 0 * jet v f [b,d] 0 +
    jet v f [a,d] 0 * jet v f [b,c] 0

/-- The left and right factors preserve the original order of their legs.
Repeated directions are allowed. -/
theorem square (v : ι→X) {f : X→ℝ} (h : ContDiffAt ℝ 4 f 0) (h₀ : f 0=0)
    (h₁ : fderiv ℝ f 0=0) (a b c d : ι) :
    jet v (fun x => f x*f x) [a,b,c,d] 0=2*pairings v f a b c d := by
  have H : ContDiffAt ℝ 1 f 0 := h.of_le (by norm_num)
  have empty : jet v f [] 0=0 := (zeroth v f 0).trans h₀
  have single (i : ι) : jet v f [i] 0=0 :=
    PhysicalAffineScalarIdealGrading.short v H h₀ h₁ [i] (by simp)
  have hp := leibniz v (ContinuousLinearMap.mul ℝ ℝ) [a,b,c,d] (A:=f) (B:=f) h h
  change jet v (fun x => f x*f x) [a,b,c,d] 0 =
    ∑ m : Masks [a,b,c,d],jet v f (lo [a,b,c,d] m) 0 * jet v f (hi [a,b,c,d] m) 0 at hp
  rw [hp, masks_sum a [b,c,d]]
  simp only [masks_sum b [c,d], masks_sum c [d], masks_sum d [], Fintype.sum_unique,
    FreeResolvent.TestD.lo, FreeResolvent.TestD.hi, empty, single, mul_zero, zero_mul, zero_add, add_zero, pairings]
  ring

end polarization

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "rp" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "g₀" => Next.SectorChange.coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

def coefficient {ι : Type*} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (v : ι→E) (a b c e : ι) : ℝ :=
  ∑ i : Rows.Receipt G S, if rp i=o then pairings v (fun B => residual T k F B i) a b c e else 0

theorem mass_four {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ) {ι : Type*} {n : ℕ} {δ C : ℝ} (k : ((R.alloy.B.a.clock.op d.level d.period)).Choices) (F : Forest ((R.alloy.B.a.clock.op d.level d.period)).ratio)
    (o : Site (R.alloy.B.a.clock.schedule.side d.level d.period)) (H : ConditionalAffineLoadPrices.Paid (PhysicalAffineScalarComparison.rowRoot (G:=G) (R.alloy.B.a.clock.op d.level d.period)) δ C n (residual (ships R.alloy.B d.cutoff d.level d.period) k F)) (hn : 4≤n)
    (v : ι→(FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)) (a b c e : ι) :
    jet v (mass (ships R.alloy.B d.cutoff d.level d.period) k F o) [a,b,c,e] 0 = 2*coefficient R d k F o v a b c e := by
  have hP := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  have hp : ((R.alloy.B.a.clock.op d.level d.period)).patch.Branches ((R.alloy.B.a.clock.op d.level d.period)).kernel G := hP.knobs.symm ▸ hP.kernel
  let row := fun (i : Rows.Receipt G (R.alloy.B.a.clock.op d.level d.period)) (B : (FreeResolvent.Slot G (R.alloy.B.a.clock.schedule.side d.level d.period) 1 → ℝ)) => residual (ships R.alloy.B d.cutoff d.level d.period) k F B i
  let held := fun i B => if (PhysicalAffineScalarComparison.rowRoot (G:=G) (R.alloy.B.a.clock.op d.level d.period)) i=o then row i B*row i B else 0
  have hR (i : Rows.Receipt G (R.alloy.B.a.clock.op d.level d.period)) : ContDiffAt ℝ 4 (row i) 0 :=
    smooth_of_le ((TestD.evaluate i ()).contDiff.contDiffAt.comp 0 H.smooth) hn
  have hH (i : Rows.Receipt G (R.alloy.B.a.clock.op d.level d.period)) : ContDiffAt ℝ 4 (held i) 0 := by
    by_cases hi : (PhysicalAffineScalarComparison.rowRoot (G:=G) (R.alloy.B.a.clock.op d.level d.period)) i=o
    · simp only [held,hi,if_true]; exact (hR i).mul (hR i)
    · simp only [held,hi,if_false]; exact contDiffAt_const
  change jet v (fun B => ∑ i,held i B) [a,b,c,e] 0 =
    2*∑ i : Rows.Receipt G (R.alloy.B.a.clock.op d.level d.period), if (PhysicalAffineScalarComparison.rowRoot (G:=G) (R.alloy.B.a.clock.op d.level d.period)) i=o then pairings v (row i) a b c e else 0
  rw [jet_sum v [a,b,c,e] Finset.univ held (fun i _ => hH i),Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  by_cases hi : (PhysicalAffineScalarComparison.rowRoot (G:=G) (R.alloy.B.a.clock.op d.level d.period)) i=o
  · simp only [held,hi,if_true]
    have h₀ : row i 0=0 := congrFun (PhysicalAffineScalarIdealSquare.zero (ships R.alloy.B d.cutoff d.level d.period) k hp F) i
    have h₁ : DifferentiableAt ℝ (row i) 0 := (hR i).differentiableAt (by norm_num)
    exact square v (hR i) h₀
      (PhysicalAffineScalarIdealGrading.derivative_zero h₁ h₀ (ManuscriptQLocalIdealSquare.slope R d k F i)) a b c e
  · simp only [held,hi,if_false,mul_zero]
    exact jet_const v [a,b,c,e] (by simp) _ 0

theorem pulled {ι : Type*} {n : ℕ} {δ C g : ℝ} (k : (S).Choices) (F : Forest (S).ratio)
    (o : Site c₀) (H : ConditionalAffineLoadPrices.Paid rp δ C n (residual T k F)) (hn : 4≤n)
    (hg : 0<g) (v : ι→E) (a b c e : ι) :
    jet v (ManuscriptQLocalIdealSquare.graded R d k F g o) [a,b,c,e] 0 =
      -(g^2)*coefficient R d k F o v a b c e := by
  have h := PhysicalAffineScalarIdealGrading.coefficient hg (j:=4) (by decide)
  change |-(2*g^2)⁻¹*g^4|=g^2/2 at h
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (inv_nonneg.mpr (by positivity))) (by positivity))] at h
  have he : -(2*g^2)⁻¹*g^4=-(g^2/2) := by linarith
  calc
    _ = (-(2*g^2)⁻¹*g^4)*jet v (mass T k F o) [a,b,c,e] 0 :=
      ManuscriptQLocalIdealSquare.grades R d k F g o H v [a,b,c,e] hn
    _ = _ := by rw [he, mass_four R d k F o H hn v a b c e]; ring

/-- The authentic original thermal purchase supplies all smoothness and
stationary inputs for the same two forests used in the fourth variation. -/
theorem original {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (F U : Forest (S).ratio) (z o : Site c₀) (hu : changed S F U z)
    (h₄ : 4≤n j₁ j₀) (v : ι→E) (a b c e : ι) :
    jet v (ManuscriptQLocalIdealSquare.graded R d k F g₀ o) [a,b,c,e] 0 =
      -(g₀^2)*coefficient R d k F o v a b c e ∧
    jet v (fun B => ManuscriptQLocalIdealSquare.graded R d k U g₀ o B-
      ManuscriptQLocalIdealSquare.graded R d k F g₀ o B) [a,b,c,e] 0 =
      -(g₀^2)*(coefficient R d k U o v a b c e-coefficient R d k F o v a b c e) := by
  have H := ManuscriptQLocalIdealSquare.realized R d p k F U z hu
  have hn : 4 ≤ max 1 (n j₁ j₀) := h₄.trans (le_max_right ..)
  have hg := (ManuscriptQLocalIdealSquare.fine R d p).1
  have eF := pulled R d k F o H.left hn hg v a b c e
  have eU := pulled R d k U o H.right hn hg v a b c e
  refine ⟨eF,?_⟩
  rw [jet_sub v [a,b,c,e]
    (smooth_of_le (ManuscriptQLocalIdealSquare.graded_smooth R d k U g₀ o H.right) hn)
    (smooth_of_le (ManuscriptQLocalIdealSquare.graded_smooth R d k F g₀ o H.left) hn),eU,eF,mul_sub]

def completeCoefficient {ι : Type*} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (v : ι→E) (a b c e : ι) : ℝ :=
  g₀^4*jet v (PhysicalAffineScalarSpectralRoot.halfLog T k F o) [a,b,c,e] 0-
    g₀^2*coefficient R d k F o v a b c e

/-- This includes the fourth derivative of the independently fixed paired
logarithm, with its original physical background scale. -/
theorem complete {ι : Type*} {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (F U : Forest (S).ratio) (z o : Site c₀) (hu : changed S F U z)
    (h₄ : 4≤n j₁ j₀) (v : ι→E) (a b c e : ι) :
    jet v (ManuscriptQLocalGaussianScalar.scalar R d k F o) [a,b,c,e] 0 =
      completeCoefficient R d k F o v a b c e ∧
    jet v (fun B => ManuscriptQLocalGaussianScalar.scalar R d k U o B-
      ManuscriptQLocalGaussianScalar.scalar R d k F o B) [a,b,c,e] 0 =
      completeCoefficient R d k U o v a b c e-completeCoefficient R d k F o v a b c e := by
  let P := query R.metals.p R.metals.K j₁ j₀
  have hp := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  obtain ⟨_,_,hW,_⟩ := hp.feeds
  have w := ManuscriptQLocalGaussianScalar.logarithm T k (n:=4) P.top.width_pos P.top.paths_pos.le hW.rows
    (ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below) F U z o hu [] (by simp)
  obtain ⟨hF,hU,_,_⟩ := w
  have H := ManuscriptQLocalIdealSquare.realized R d p k F U z hu
  have hn : 4 ≤ max 1 (n j₁ j₀) := h₄.trans (le_max_right ..)
  have hg := (ManuscriptQLocalIdealSquare.fine R d p).1
  let L (Y : Forest (S).ratio) := PhysicalAffineScalarSpectralRoot.halfLog T k Y o
  have one (Y : Forest (S).ratio) {δ C : ℝ} (hY : ConditionalAffineLoadPrices.Paid rp δ C
      (max 1 (n j₁ j₀)) (residual T k Y)) (hl : ContDiffAt ℝ 4 (L Y) 0) :
      ContDiffAt ℝ 4 (ManuscriptQLocalGaussianScalar.scalar R d k Y o) 0 ∧
      jet v (ManuscriptQLocalGaussianScalar.scalar R d k Y o) [a,b,c,e] 0 =
        completeCoefficient R d k Y o v a b c e := by
    have h := ManuscriptQLocalIdealSquare.graded_smooth R d k Y g₀ o hY
    have hb := smooth_of_le h hn
    have hl' : ContDiffAt ℝ 4 (L Y) (g₀ • (0:E)) := by rw [smul_zero]; exact hl
    have hl'' : ContDiffAt ℝ 4 (fun B : E => L Y (g₀ • B)) 0 :=
      hl'.comp 0 (g₀ • ContinuousLinearMap.id ℝ E).contDiff.contDiffAt
    have he : ManuscriptQLocalGaussianScalar.scalar R d k Y o =
        fun B => L Y (g₀ • B)+ManuscriptQLocalIdealSquare.graded R d k Y g₀ o B := by
      funext B
      unfold ManuscriptQLocalGaussianScalar.scalar ManuscriptQLocalIdealSquare.graded L
      abel
    rw [he]; refine ⟨hl''.add hb,?_⟩
    rw [jet_add v [a,b,c,e] hl'' hb,PhysicalAffineScalarIdealGrading.pulled_jet g₀ v (L Y) [a,b,c,e] hl,
      pulled R d k Y o hY hn hg v a b c e]
    change g₀^4*jet v (L Y) [a,b,c,e] 0 + -(g₀^2)*coefficient R d k Y o v a b c e = _
    unfold completeCoefficient L
    ring
  obtain ⟨hf,eF⟩ := one F H.left hF
  obtain ⟨hu',eU⟩ := one U H.right hU
  refine ⟨eF,?_⟩
  have subtract := jet_sub v [a,b,c,e]
    (A:=ManuscriptQLocalGaussianScalar.scalar R d k U o) (B:=ManuscriptQLocalGaussianScalar.scalar R d k F o)
    hu' hf
  exact subtract.trans (congrArg₂ (fun u v : ℝ => u-v) eU eF)

end YM.Integration.ManuscriptQLocalGaussianQuartic
end
