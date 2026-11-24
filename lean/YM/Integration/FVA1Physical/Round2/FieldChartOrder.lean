import YM.Integration.FVA1Physical.Round2.FieldTangentOrder
import YM.Integration.FVA1Physical.Round2.ChartSubsets
import YM.Integration.FVA1Physical.Round2.LocalizedBoundary

/-! Physical field derivatives on a finite set of varying coordinates at an
arbitrary nonflat background. Exterior coordinates are held fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter MeasureTheory Lattice RG YM.Wilson Push.Uniform Push.Local Push.Local.Kernel
open MSbar MSbar.Bulk MSbar.Rolling MSbar.Wave MSbar.Midpoint
open AnalyticBridge.SectorAffine.Offset Next.Foundations
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {c f : Side}

def chartOrderPrice (G : Gauge) (u : ℝ) (k m : ℕ) (a : ℝ) :=
  composeCost k (tangentOrderPrice G u k m a) (composeCost k (account k G).choose 2)

theorem reading_chart_order {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : StepData c f) (R : Rep G f) (φ : Config G f → ℝ)
    (branch : S.patch.Branches S.kernel G) (vac : Envelope R.eval)
    (pos : ∀ U, 0 < R.eval U) (field : Envelope φ) {a : ℝ} (cap : ∀ U, |φ U| ≤ a)
    (X : Edges c) (P : E →L[ℝ] Positions (Primary c G)) (thin : ‖P‖ ≤ 1)
    (held : ∀ z e, e∉X → panel G c (P z) e=0) (g : ℝ) (unit : |g| ≤ 1)
    (base : Positions (Primary c G)) (hb : ‖g•base‖ ≤ 1) (k : ℕ) :
    Through k (fun z=>expect S R (postcard G c g (base+P z)) φ) 0
      (chartOrderPrice G (R.beta*S.kernel.penalty) k X.card a) := by
  let x:=g • base
  let Y:=fun z=>x+(g•P) z
  let V:=palace x
  let H:=fun z=>chartW x (Y z)
  have y0 : Y 0=x := by simp [Y]
  have h0 : H 0=0 := by simp only [H,y0,birthday]
  have normL : ‖g•P‖ ≤ 1 := by rw [norm_smul,Real.norm_eq_abs];exact mul_le_one₀ unit (norm_nonneg _) thin
  have linear : Allows k (g•P : E→L[ℝ] Positions (Primary c G)) 0 1 :=
    allows_linear normL (by simp)
  have inner : Through k Y 0 2 := by
    simpa only [one_add_one_eq_two] using Through.control ((allows_const (0:E) hb).add linear)
  have outer : Through k (chartW x) (Y 0) (account k G).choose := by
    rw [y0];exact (account k G).choose_spec.2 c x hb
  have hThrough:=outer.comp inner
  have hRead:=reading_tangent_order S R φ branch vac pos field cap X V k
  have hRead' : Through k (fun z=>expect S R (increment V (edgeProject G X z)) φ) (H 0)
      (tangentOrderPrice G (R.beta*S.kernel.penalty) k X.card a) := by
    rw [h0];exact hRead
  have matchEdge (z:E) : edgeProject G X (H z)=H z := by
    funext e
    rw [edgeProject_at]
    split
    · rfl
    rename_i off
    have same : panel G c (Y z) e=panel G c x e := by
      change (panel G c (x+g•P z)) e=_
      simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,held z e off,smul_zero,add_zero]
    symm
    change bendLog G (G.lieExp (panel G c x e)) (panel G c (Y z) e)=0
    rw [same]
    exact congrFun (birthday x) e
  have yc : Tendsto Y (𝓝 0) (𝓝 x) := by simpa only [y0] using inner.smooth.continuousAt.tendsto
  have germ:= (bendUses x).comp_tendsto yc
  refine (hRead'.comp (show Through k H 0 _ from hThrough)).germ ?_
  filter_upwards [germ] with z hz
  rw [matchEdge]
  apply congrArg (fun W=>expect S R W φ)
  change increment (increment 1 (panel G c x)) (chartW x (Y z)) = increment 1 (panel G c (g•(base+P z)))
  simpa only [Function.comp_apply,x,Y,smul_apply,smul_add] using hz

end YM.Integration.FVA1Physical.Round2.Curvature
