import YM.FVA2.FpWarm
/-!
# Parameter and chart freedoms that keep the FP convention

A RAW complement lift is allowed to parameterize ordinary directions if we normalize its global
value (at base). In particular if a Landau strict-gauge-type section already annihilates action on
constants infinitesimally, every complement lift gives that same determinant even using a raw
lift; MS uses strictly mean-zero on that slice, see also `Harmonic.mean_at`. Not a theorem in
arbitrary global conventions if no global reset performed or a Jacobian computed without it.
Explicit formula using only actual `turn` here. No statement about general (not used) gauge BV
flows whose marks are not the given physical ones.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.TreeBasis
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge PertExtension PertExtension.Chart Filter
open Function Set Gauge SectionBasis Repoint Metric
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
variable {V E W:Type}[Fintype V][Fintype E]{G:Gauge} {D:Loom V E}{T:D.Truss}

/-- complement parameterized by any W+linear map.Spin with correct reset at base. -/
def reset_root (D:Loom V E) : Sites V G→ₗ[ℝ] Root D G:= LinearMap.pi fun i=> (LinearMap.proj i.val: Sites V G→ₗ[ℝ] G.Color)-LinearMap.proj D.origin

def literal_root (q:Sites V G) := q D.origin
omit [Fintype E] [Fintype V] in
lemma global_reset (q:Sites V G)(v:V): guarded G D (reset_root D q) v=q v-q D.origin:= by
     by_cases h: v=D.origin
     · subst v; simp
     exact guard_off G D (reset_root D q) (⟨v,h⟩:Nonroot D)
omit [Fintype E] [Fintype V] in
lemma before_reset (q:Sites V G) : q=guarded G D (reset_root D q)+fun _=>literal_root (D:=D) q:= funext (fun i=> by rw [Pi.add_apply,global_reset]; exact (sub_add_cancel ..).symm)

section
variable [AddCommGroup W] [Module ℝ W]
-- all linear complements to constant sites are in this form
abbrev Schema (G : Gauge)(D:Loom V E)(v:W→ₗ[ℝ] Sites V G) := Bijective (reset_root D ∘ₗ v)
abbrev gauge_direction (G:Gauge)(D:Loom V E)(v:W→ₗ[ℝ] Sites V G)(h:Schema G D v): W≃ₗ[ℝ] Root D G:= LinearEquiv.ofBijective _ h
variable (Z:SectionBasis D T G)(A: Links E G)(v:W→ₗ[ℝ] Sites V G)(h: Schema G D v)
local notation "J"=> gauge_direction G D v h

def amended (u:Sites V G) := TreeBasis.turn G D A (fun i=> u i - literal_root (D:=D) u)
omit [Fintype V][Fintype E] in
lemma amended_t (x:W): amended (D:=D) A (v x)= directed G D A ((J) x):= by
    apply congr_arg (turn G D A); exact ( funext ( fun i=>global_reset (D:=D) (v x) i )|>.symm )
-- For computing with the same global base. Used at and off slice. Mean-zero shorthand below
lemma amended_ghost (x : W): (J).symm (Z.projection (amended (D:=D) A (v x)))=(LinearEquiv.conj (J).symm (Aghost Z A)) x:= by rw [amended_t A v h x]; rfl
/-- Normalized matrix in any bases (including using complement coords and usual adjoint
 ghost volume) is similar to AP. Need still check normalization of fields and selecting FP
 condition values when quoting another determinant formula. -/
lemma compensated : LinearMap.det ((J).symm.toLinearMap ∘ₗ Z.projection ∘ₗ (directed G D A) ∘ₗ reset_root D ∘ₗ v)= Z.AP A:= by
     rw [show ((J).symm.toLinearMap ∘ₗ Z.projection ∘ₗ (directed G D A) ∘ₗ reset_root D ∘ₗ v)=_ from ?_]; apply LinearMap.det_conj (Z.Aghost A) (J).symm; apply LinearMap.ext; intro x; rfl

-- check correctness of raw determinant only when anchored with stability
lemma raw_identity (he:∀ c:G.Color, Z.projection (turn G D A (fun _=>c))=0):
    LinearMap.det ((J).symm.toLinearMap ∘ₗ Z.projection ∘ₗ TreeBasis.turn G D A ∘ₗ v) = Z.AP A:= by
     rw [← compensated Z A v h]; congr 1; apply LinearMap.ext; intro x; simp only [LinearMap.comp_apply]; congr 1; nth_rw 1 [before_reset (D:=D) (v x)]; rw [map_add,map_add,he,add_zero]; rfl
end
namespace Unicum
open Push.Loops Precision GermLaplace GermLaplace.Rates Wilson Lattice
variable {I:Type}[Fintype I](U Z:ChartRatio G)(hu:LocalRatio U)(hz: LocalRatio Z)
include hu hz
lemma homeJ : U.J=ᶠ[𝓝 0] Z.J:= by filter_upwards [Metric.ball_mem_nhds (0:G.Color) hu.patch,Metric.ball_mem_nhds (0:G.Color) hz.patch] with p h hz'; rw [← exp_delta_det hu h,← exp_delta_det hz hz']
lemma priceJ : density I U=ᶠ[𝓝 0] density I Z:= by
    filter_upwards [Filter.eventually_all.mpr (fun i=>(homeJ U Z hu hz).comp_tendsto ((continuous_apply i).tendsto (0:Links I G)))] with p hp; exact Finset.prod_congr rfl (fun i _=> hp i)
variable {n:Side}(L:GaugeSlice G n) {O:Wilson.Observable G n}(hp:Physical O) (he:Honest O)
lemma laws : sliceRows L U O= sliceRows L Z O:= by
     refine congr_arg PowerSeries.mk (local_moments _ _ (Chart.tangent G (staple n).Bulk) (Filter.EventuallyEq.rfl (f:=WilsonPull L)) ?_)
     filter_upwards [ (show Tendsto L.L (𝓝 0) (𝓝 0) from (by simpa using L.L.continuous_of_finiteDimensional.tendsto 0)).eventually (priceJ (I:=Orb.OEdge n) U Z hu hz) ] with x hx
     unfold sliceK; rw [show density _ U _= _ from hx] -- ambiguous
include hp he L
lemma individual (hn:_root_.Even n.val): PowerSeries.mk (Orb.diagonalWith U (Orb.restrictedO O))=PowerSeries.mk (Orb.diagonalWith Z (Orb.restrictedO O)):= by rw [ tree_identity L hn U hu hp he, tree_identity L hn Z hz hp he,sliceEval,sliceEval,laws U Z hu hz L,laws U Z hu hz L ]
end Unicum
end YM.FVA2.TreeBasis
