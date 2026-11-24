import YM.FormalOPE.RG10.Sync.Layout
/-!
 # Core one-step ticket in both multiplicative register and chart
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp MarkovChain.Router
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {E F K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
 [NormedAddCommGroup K][NormedSpace ℝ K]
variable (Γ: Law F)
variable {I B:Type}[Fintype I] [Fintype B]
variable (L:Layout I E)(Q: Layout B K) (d:F→ₗ[ℝ] E) (k:E→ₗ[ℝ] F)
local notation "σ"=> Row (Space F)
local notation "q"=> matrix Γ L d
local notation "P"=> across L Q
-- pre-composed with centering operator.B
variable (T:Ticket (F×K)) (r:E×K→ₗ[ℝ] E)
local notation "μ"=> d.prodMap (LinearMap.id (R:=ℝ) (M:=K))
-- k active.Public.Sem. Use parentheses notation.
local notation "R"=> k.prodMap (LinearMap.id (R:=ℝ) (M:=K))
 def voltage : Channel (I⊕B):= digital P (boost (R) (decant T))
omit [FiniteDimensional ℝ F] in
lemma voltage_zero : coeff 0 (voltage L Q k T)=0:=by unfold voltage digital; rw [PowerSeries.coeff_map, coeff_zero_eq_constantCoeff_apply, vacant _ (onceBlank T),map_zero]
 def station : Episode I B (Space F) where
 spur := spurs L P r
 vertices:= voltage L Q k T
 law := voltage_zero L Q k T
 joint := q
local notation "e"=> station Γ L Q d k T r
omit [FiniteDimensional ℝ F] in
lemma generated (h:incline T) : advance (voltage L Q k T)=digital P (boost R T):= by unfold voltage; rw [← authority,← boost_exp,soluble h]

variable (H:∀ x,k (d x)=x)
include H
omit Γ L Q r T [Fintype I] [Fintype B] [FiniteDimensional ℝ F] in
lemma confinement (u: Ticket (F × K)): boost μ (boost R u)=u:= by apply Stack.into; rintro ⟨x,y⟩; rw [caught,caught]; simp [H]

variable [MeasurableSpace F][BorelSpace F]
variable (ν:Measure F)[Measure.IsAddHaarMeasure ν]
local notation "D"=> simpleMean (K:=K) Γ ν
lemma revenue (h:incline T): Bulk.income (B:=B) q (voltage L Q k T)=digital Q (D T):= by unfold Bulk.income; rw [generated _ _ _ _ h,moving Γ L Q d ν]; change digital Q ((D) (boost μ _))=_; rw [confinement d k H]
lemma income (h:incline T)(u:Ticket E):
 Bulk.move q (advance (voltage L Q k T) * (replot (spurs L P r)) (digital L u))= digital Q (D (T*(boost (r ∘ₗ (μ)) u))):= by
 rw [generated _ _ _ _ h,reassess,←map_mul,moving Γ L Q d ν]; change digital Q (D (boost μ _ ))= _; rw [map_mul,confinement d k H, OpenSlots.boosts]
lemma current (h:incline T)(u:Ticket E): (e).floats (digital L u) = digital Q (D (T*boost (r ∘ₗ (μ)) u) * Return (D T)):= by
 change Bulk.move q (Route.advance (voltage L Q k T) * replot (spurs L P r) (digital L u))*PowerSeries.invOfUnit (Bulk.income q (voltage L Q k T)) 1=_
 rw [income Γ L Q d k T r H ν h,revenue Γ L Q d k T H ν h,_root_.map_mul (digital Q)]; congr 1
 let W:= D T; have hs :incline W:= simply Γ ν h; change invOfUnit (digital Q W) 1=_
 apply ((worth hs).map (digital Q)).mul_left_cancel; rw [←map_mul (digital Q),spend_it hs,map_one,PowerSeries.mul_invOfUnit]
 unfold digital; rw [← coeff_zero_eq_constantCoeff_apply ..,PowerSeries.coeff_map,coeff_zero_eq_constantCoeff_apply,hs,map_one]; rfl
end YM.FormalOPE.RG10.Sync
