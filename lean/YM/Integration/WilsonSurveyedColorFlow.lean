import YM.Integration.WilsonSurveyedColorPlot
import YM.MS.Garment.Packable

/-! The actual dimensional Landau line, its closed traces, and the connected
bilinear joining operation on the marked MS source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorFlow
open MS MS.Plane MS.Koszul MS.Heat MS.Landau MS.Arts MS.City MS.Garment
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "I" => G.ColorIndex

theorem across (a b : I) : ∑ i, entry U a i * entry U b i = if a=b then 1 else 0 := by
  let A : Matrix I I ℂ := entry U
  have h : A.transpose * A = 1 := by
    ext i j
    exact (sewn U i j).trans Matrix.one_apply.symm
  have back : A * A.transpose = 1 := mul_eq_one_comm.mp h
  exact (congrFun (congrFun back a) b).trans Matrix.one_apply

variable {D : Type} [Fintype D] [DecidableEq D]

theorem line (K : YMflow D) :
    Arts.Pilot.Transport (pilot U) (Landau.choir K id) (Landau.choir K id) := by
  intro t a b
  let X := pilot (P:=Momentum D) (D:=D) U
  let T := Landau.choir (C:=I) K id
  change (if a.2=b.2 then K a.1 b.1 t else 0) =
    ∑ u : Leg D I, ∑ v, T u v t * X.fieldC u a * X.fieldC v b
  rw [Fintype.sum_prod_type]
  have collapse (q : Landau.Atom D) (p : I) :
      ∑ i : Leg D I, T (q,p) i t * X.fieldC (q,p) a * X.fieldC i b =
        K q b.1 t * X.fieldC (q,p) a * entry U b.2 p := by
    rw [Fintype.sum_prod_type]
    simp only [T,X,pilot,Landau.choir,mul_ite,ite_mul,mul_zero,zero_mul,id_eq]
    simp
  simp_rw [collapse]
  rw [Finset.sum_eq_single a.1]
  · unfold X pilot
    simp only [if_true,mul_assoc,← Finset.mul_sum,across]
    split <;> simp [*]
  · intro i _ hi
    simp [X,pilot,hi]
  · simp

theorem loop (K : YMflow D) (p : Momentum D)
    (F : Score G D (Momentum D)) :
    turn U ((Landau.choir K id).trc p F) = (Landau.choir K id).trc p (turn U F) := by
  have fixed : (pilot (D:=D) (P:=Momentum D) U).volp p = p := rfl
  simpa only [emits,fixed] using (line U K).shuttle0 p F

theorem connected (K : YMflow D) (F H : Score G D (Momentum D)) {b : Bool}
    (closed : (Landau.choir (C:=I) K id).closed Landau.parity b) :
    turn U (Flux.tree Landau.parity (Landau.choir K id) F H) =
      Flux.tree Landau.parity (Landau.choir K id) (turn U F) (turn U H) := by
  simpa only [emits] using (line U K).gatherR F H closed closed

end YM.Integration.WilsonSurveyedColorFlow
end
