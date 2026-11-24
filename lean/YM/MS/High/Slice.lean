import YM.MS.High.Sphere
/-!
# Rank-wise needed Taylor limits

Function `slice` chooses the limit candidate even if the lower dimension
has not yet been set. Later resetting parameters changes these allocations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm
open scoped Topology ContDiff
variable {G : Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
   {B B' F G' : Recount G} {M : Reading G} {P : Law G}
   {h q v:ℤ} {r d n j:ℕ} {b : Bool} {w : Wire (Branch G Axis) E FourP}
section limit
-- bound estimates support `Payment.mature`; build for meeting each step.
structure Mature (F : Reading G) (b : Bool) (r : ℕ) (h:ℤ): Prop where
    smooth (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Wire (Branch G Axis) E FourP) (hp : Course b w) (he:w.length=r) x t : ContDiff ℝ ∞ (Domain.tape F w x t)
    needs (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Wire (Branch G Axis) E FourP) (hp : Course b w) (he:w.length=r) (j : ℕ) (hz : fieldDim wfield w+j ≤ h) (x:ℝ): ∃ v, Origin F w j x v

open Classical in
def slice (F : Reading G) (b : Bool) (r : ℕ) (v : ℤ) (x:ℝ) : Law G:= fun w=> if Course b w ∧ w.length=r then limUnder atTop (fun t:ℝ=> skin wfield v (F (x,t)) w) else 0
lemma rank_slice {x}: Ranked b r (slice M b r v x):= fun w he hp=> by simp [slice,hp]
lemma slice_drop {x} (w : List (Lane4 G)) (hx : ¬ Course b w) : slice M b r v x w=0:= by simp [slice,hx]
lemma slice_extra {x} {w : List (Lane4 G)} (hv:v < fieldDim wfield w): slice M b r v x w=0:= by
   unfold slice; split; swap; rfl
   have hv: ¬ fieldDim wfield w≤v:= by omega
   simp_rw [skin,if_neg hv]; exact Filter.Tendsto.limUnder_eq (f:=atTop) (g:=fun _:ℝ=>(0:ℂ)) tendsto_const_nhds

lemma slice_torch (H : Mature M b r h) (x:ℝ) {u : List (Lane4 G)} (hw : Course b u) (hL : u.length=r) (hp : fieldDim wfield u+j=v) (he:v≤h):
    Tendsto (fun t=> torch j (M (x,t)) u) atTop (𝓝 (slice M b r v x u)):= by
   obtain ⟨t,ht⟩:= H.needs ℝ (ray u) (ray_course hw) (by simp only [ray_len,hL]) j (by rw [ray_dim,hp]; exact he) x
   have hv:= origin_test ht (H.smooth ℝ (ray u) (ray_course hw) (by simp only [ray_len,hL]) x) 1; simp only [ray_sail] at hv
   rw [slice, if_pos ⟨hw,hL⟩]; simp_rw [skin_eq (f:=M (_,_)) _ v hp, Filter.Tendsto.limUnder_eq hv]; exact hv

lemma accumulates (H : Mature M b r h) {u : List (Lane4 G)} (hw : Course b u) (hL : u.length=r) (x:ℝ) (hv:v≤h):
    Tendsto (fun t=> skin wfield v (M (x,t)) u) atTop (𝓝 (slice M b r v x u)):= by
   rcases lt_or_ge v (fieldDim wfield u) with he|he
   · simp_rw [slice_extra he, skin, if_neg he.not_ge]; exact tendsto_const_nhds
   simp_rw [skin_eq (f:=M (_,_)) wfield v (show fieldDim wfield u+(↑(v-fieldDim wfield u).toNat:ℤ)=v by omega)]; exact slice_torch H x hw hL (by omega) hv
lemma slice_form (H : Mature M b r h) {x} (hp:v≤h): Form (slice M b r v x) wfield v b:= by
   intro E _ _ w hw; rcases lt_or_ge v (fieldDim wfield w) with he|he
   · rw [show fieldVal (slice M b r v x) w=0 from funext fun i=> slice_extra (w:=sail w i) (by rwa [sail_dim])]; exact form_zero _
   by_cases hL : List.length w=r; swap;
   · rw [show fieldVal (slice M b r v x) w=0 from funext fun i=> rank_slice (M:=M) (sail w i) (sail_course i hw) (by rwa [sail_len])]; exact form_zero _
   let p:=(v-fieldDim wfield w).toNat; have hU : v-fieldDim wfield w=p:= by unfold p; omega
   obtain ⟨t,ht⟩:= H.needs E w hw hL p (by omega) x
   let T:= (Nat.factorial p:ℝ)⁻¹ • t
   have hv : fieldVal (slice M b r v x) w= Tensor.diagonal T:= funext fun i=> tendsto_nhds_unique (slice_torch (j:=p) H x (u:=sail w i) (sail_course i hw) (by rwa [sail_len]) (by rw [sail_dim]; omega) hp) (origin_test ht (H.smooth E w hw hL x) i)
   rw [hv]; exact form_diag _ _ hU

-- Vanishing lower Taylor limits after tuning. At rank with Born movement.
def Absent (M : Reading G) (b : Bool) (r : ℕ) (h:ℤ):= ∀ (w: List (Lane4 G)), Course b w→ w.length=r→∀ (j:ℕ), fieldDim wfield w+j<h → ∀ x:ℝ,Tendsto (fun t=> torch j (M (x,t)) w) atTop (𝓝 0)
namespace Mature
variable (H : Mature M b r h)
include H
lemma uses (hv:v≤h) (hl:Absent M b r v) (x:ℝ) : Frozen b wfield r M (slice M b r v x) v x := by
    refine ⟨fun w hw he j hq=>?_, slice_form H hv⟩
    split; · exact slice_torch H x hw he (by assumption) hv
    exact hl _ hw he j (by omega) x
lemma enough (hl:Absent M b r (h+1)) (hw : Course b w) (hp:w.length=r) (hz : weak (fieldDim wfield w-h) eps_gain j) (x:ℝ) : Origin M w j x 0:= by
    have he : fieldDim wfield w+j ≤ h := by have hv:=(int_need p_gain s_gain).mp hz; omega
    exact (origin_ray_iff (H.needs E w hw hp j he x) (H.smooth E w hw hp x)).mpr (fun p=> hl (sail w p) (sail_course p hw) ((sail_len ..).trans hp) j (by rw [sail_dim]; omega) x)
end Mature
end limit
end YM.MS.High
