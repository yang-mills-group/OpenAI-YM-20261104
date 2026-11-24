import YM.Integration.WilsonOlderFreshSoftSocketSettlement
import YM.Integration.WilsonOlderFreshSoftFigures

/-! The unshifted basis inscription and its actual resolved socket have the very same original rooted one-colour input, at every rank and on the geometric cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketGeometry
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonMeasuredPointBareWords
open WilsonThermometerDeclaredSeeds (Choice)
open private atom from YM.Integration.IndependentSourcePathFamily
variable {G:Gauge}{r:ℕ}

private theorem move {E:Type}{U:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    (P Q:Gen E U)(x:ℝ)(h:∀ j z,P j z=x • Q j z)(r e:ℕ):
    moved r e P=x • moved r e Q:=by
  funext i l v
  by_cases he : e ≤ i
  · by_cases hm : r+(i-e)=l
    · subst l
      simpa [moved,he,Blue.shine_lit] using h (r+(i-e)) v
    · simp [moved,he,Blue.shine_dark hm]
  · simp [moved,he]

variable {I:Type}[Fintype I][DecidableEq I]{D:I→ℕ}(i:I)
  (path:Fin r→RG.Slot)(color:Fin r→G.ColorIndex)(x:ℝ)(κ:Knob (D i))(pt:Chamber)(e:ℕ)(z:Cover)
local notation "a_" t:max => colour path color (t:ℂ) Complex.reCLM
omit [Fintype I] in
theorem scaled:
    source D i (a_ x) κ pt e z=x • source D i (a_ (1:ℝ)) κ pt e z:=by
  let u:=claim (D i) κ pt
  have wage (j:Stationary.Ink G r):
      (current (a_ x) u).wage j=x • (current (a_ (1:ℝ)) u).wage j:=by
    simp [current,colour,smul_smul,Complex.mul_re]
  have rays (j:Stationary.Ink G r):rayOne (current (a_ x) u) j=
        rayOne (current (a_ (1:ℝ)) u) j:=rfl
  have vol:volumeR (current (a_ x) u) e=x • volumeR (current (a_ (1:ℝ)) u) e:=by
    apply Prod.ext
    · funext n
      apply move
      intro j a
      simp only [sapR,rays,wage,Finset.smul_sum,smul_comm x]
    · apply move
      intro j a
      simp only [august,rays,wage,Finset.smul_sum,smul_comm x]
  unfold source
  change cn D i (volumeR (current (a_ x) u) e) z=_
  rw [vol]
  apply Prod.ext
  · funext n j l v
    exact map_smul (petal D i) x _
  · funext j l v
    exact map_smul (petal D i) x _

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
  (κ:(i:I)→Knob (D i))(pt:I→Chamber)(b:(i:I)→(R.family.labels.level (d i)).Index)
def row (i:I)(c:Choice R d i)(a:Cover):Era G (Pen D {i}):=
  let s:=WilsonReceivedCanonicalVerseBasis.basis R d κ pt i c
  source D i (colour s.path s.color 1 Complex.reCLM) (κ i) (pt i) s.rank a

omit [Fintype I] in
theorem original (i:I)(z:Cover):
    IndependentSourcePathFamily.single (WilsonOlderFreshSoftFigures.seed R D d b κ pt) i z=
      ∑m:Term R (d i) (b i),weight R (d i) (b i) m • row R d κ pt i (.inr ⟨b i,m⟩) z:=by
  unfold IndependentSourcePathFamily.single
  apply Finset.sum_congr rfl
  intro m _
  exact scaled i _ _ (weight R (d i) (b i) m) (κ i) (pt i) _ z

end YM.Integration.WilsonOlderFreshSoftSocketGeometry
end
