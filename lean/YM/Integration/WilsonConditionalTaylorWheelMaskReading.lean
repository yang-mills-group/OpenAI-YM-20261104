import YM.WilsonCoeffUV.Emit.RentedCapture

/-! Read the complete earlier joint mask under its very same transported
linear probe. The true root offset factors and linear sum are kept intact. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelMaskReading
open Function Filter Lattice Laurent RG Wilson Precision Tree Bloch Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical Matrix BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}

def coeff {V:Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f:V→L[ℝ]ℝ) (e r:ℕ) (v:Fin r→YForest G):Era G V →ₗ[ℝ]ℝ where
  toFun X:=f (X.2 e r v)
  map_add' X Y:=by change f (_+_)=_;rw [map_add]
  map_smul' c X:=by change f (c • _)=_;rw [map_smul];rfl

def probe (P:Patch) (S:Finset I) (f:Pen D S→L[ℝ]ℝ) (i:backRow P.L S):Pen D S→L[ℝ]ℝ:=
  f.comp (mend P (inflate P S i) D S)

theorem offset (P:Patch) (K:I→ℕ) (X:Outerm G D) (loc:I→ Cover) (S:Finset I) (f:Pen D S→L[ℝ]ℝ)
    (e r:ℕ):
    (tuftV f (unite P K X loc S)).2 e r=
      ∑ i:backRow P.L S,scalesK P K S •
        (tuftV (probe P S f i) (X (splitQ P loc S i) S)).2 e r:=by
  funext v
  let measure:=coeff f e r v
  change measure (∑i:backRow P.L S,portV P K X loc S i)=_
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [portV,map_smul]
  rfl
end YM.Integration.WilsonConditionalTaylorWheelMaskReading
end
