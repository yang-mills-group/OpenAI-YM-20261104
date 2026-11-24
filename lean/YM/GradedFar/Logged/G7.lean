import YM.GradedFar.Logged.Unmoved
import YM.OPE.Eye.Fast

/-!
# (G.7) fixed clearance as well (on the physical Reader)
 Additional progress towards the OPE comparison.
-/
namespace YM.OPE.Logged.Unmoved
noncomputable section
open Function Filter MeasureTheory Set Orbits Spec
open Extraction OPE.Log Table Stroke Subtable Economy
open scoped Topology BigOperators Classical ContDiff
variable {I J L:Type} [Fintype I][Fintype J]
variable {G:Gauge}{C:Family G}{f: Extraction.Order}{S: Table C.book} (F: Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (U:LogTrace F R.port)
    (V: Services C f S)
variable {d:I→ℕ} {e:J→ℕ} {c M η:ℝ}(hc:0<c) (w:Labels S e)(v:Labels S d)
local notation "T"=> spectator F
local notation "τ"=>𝓝[>] (0:ℝ)
structure Ann (F: Final C f S) (d:I→ℕ)(M η L:ℝ) where
    r:ℝ
    x:I→E4
    o:E4
    h:WithinRoom r M η x o
    b:Labels S d
    priced: ∀ i, ‖b i‖ ≤ L
    viewer:Viewers F
structure Listed (F: Final C f S) (d:I→ℕ)(e:J→ℕ)(M η c L L':ℝ) extends Ann F d M η L where
    w:Labels S e
    mw : ∀ j, ‖w j‖≤ L'
    y : J→E4
    head : ClearOf o y c

variable (hm:0≤ M)(hη:0<η) (h:ℕ)
include U hm hη
-- can combine costs in each of these estimates if wanted. `∀ᶠ k atTop`
theorem G7_price (d:I→ℕ) (L:ℝ) (a:R.channels h) : ∀ᶠ k:ℕ in atTop, ∃ D:ℝ,0<D ∧ ∀ᶠ r:ℝ in τ, ∀(x:I→E4) (o:E4), WithinRoom r M η x o → ∀ v:Labels S d,
    (∀ i, ‖v i‖ ≤ L) → ‖R.coef h a x v o‖≤ D*badge r^k*(Trace.core d h r) := by
   let T':= Ann F d M η L; let P:Economy.Small T':= ⟨comap Ann.r τ, Ann.r,tendsto_comap⟩
   have h:= scored F R U P h Ann.x Ann.o hm hη (Eventually.of_forall (fun i=> i.h)) (show ∀ j,Paint P (fun _=>1) (fun i=> Ann.b i j) from fun j=> Paint.bounded L (Eventually.of_forall fun i=> i.priced j)) a
   obtain ⟨D,hD,k,hk⟩:=h; filter_upwards [eventually_ge_atTop k] with k' hk'; refine ⟨D,hD,?_⟩
   filter_upwards [eventually_comap.mp hk, self_mem_nhdsWithin, (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const zero_lt_one] with r hr (hp: 0< r) (he : r<1) x o hx v hv
   have h:=hr (⟨r,x,o,hx,v,hv,none⟩:T') rfl; change ‖R.coef _ a x v o‖ ≤ D*badge r^ k * |Trace.core d _ r| at h; unfold Trace.core at *; rw [abs_of_nonneg (by positivity)] at h
   have hx:1≤badge r:= by unfold badge run; linarith [Real.log_nonpos hp.le he.le]; -- extension
   apply h.trans; gcongr

include V hc
-- horizon spatial remainder (fixed geometry price separate estimate in the text)
theorem G7_spatial (d:I→ℕ)(e:J→ℕ) (L L':ℝ):
    ∀ᶠ k:ℕ in atTop, ∃ D:ℝ,0<D ∧ ∀ᶠ r:ℝ in τ, ∀(x:I→ E4)(o:E4), WithinRoom r M η x o→ ∀(y:J→E4), ClearOf o y c →
       ∀(s:Viewers F) (v:Labels S d)(w:Labels S e), (∀ i, ‖v i‖≤ L) → (∀ i,‖w i‖≤ L') →
          ‖whole (T s) x v y w -upon (T s) h o y w (R.packet h x v o)‖ ≤ D * badge r^k*lifetime d h r := by
    let T':= Listed F d e M η c L L'; let P:Economy.Small T':= ⟨comap (fun i=>i.toAnn.r) τ, (fun i=> i.toAnn.r), tendsto_comap⟩
    let s (i:T'):= Ann.viewer i.toAnn
    let x (i:T'):= i.toAnn.x; let z (i:T'):= i.toAnn.o; let v' (i:T'):=i.toAnn.b
    have hp:= nonlinear F R U V hc (e:=e) P s h x z (y:=Listed.y) hm hη (Eventually.of_forall (fun i:T'=>i.toAnn.h)) (Eventually.of_forall fun i=>i.head)
       (v:=v') (w:=Listed.w) (fun j=>Paint.bounded L (Eventually.of_forall fun i:T'=>i.toAnn.priced j)) (fun j=>Paint.bounded L' (Eventually.of_forall fun i=>i.mw j))
    obtain ⟨D,hD,k,H⟩:=hp; filter_upwards [eventually_ge_atTop k] with k' hk'; refine ⟨D,hD,?_⟩
    filter_upwards [eventually_comap.mp H,self_mem_nhdsWithin, (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const zero_lt_one] with r hr (hp:0<r) (he:r<1) x o hx y hy s v w hv hw
    have ht:= hr (⟨⟨r,x,o,hx,v,hv,s⟩,w,hw,y,hy⟩:T') rfl
    change ‖rate F R w v s h x o y‖≤ D*badge r^k * |lifetime d h r| at ht; unfold lifetime at *; rw [abs_of_nonneg (by positivity)] at ht
    have hx:1≤badge r:= by unfold badge run; linarith [Real.log_nonpos hp.le he.le]
    apply ht.trans; gcongr
end
end YM.OPE.Logged.Unmoved

