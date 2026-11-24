import YM.SchemeRG11.MSDetector.Vertex
/-!
Double-link term. `solo` line to x point. `next = solo +1`: goes to b, the
other goes to b also. Read B POLE on the amputated stencils as registered
in Bubble then AFTER eliminating that pole project at 4. The possible
additional derivative on the solo line when SOLE extractor is derivative leg
(registers on the open A leg) is retained as the open stencil word. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.SchemeRG11.MSDetector
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm Flare Asymptotics
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace Classical
local notation "Tri" => Nodes 4

def load (μ R : ℝ) (U V L : Sl) (x:E4) := weigh fun i=> weigh fun j=> weigh fun k=> Bubble.earn μ (peak R i) (peak R j) (peak R k) U V L x

-- Action expanded as Σ_{a,b} ∂_a A_b A_a A_b ν, open A/slot b pinned by curl slots or terminal.
def tuner (a b:Axis): Eye→Axis:=![b,a,b]

-- oriented p moment flags at p40; p from b into V, then to sole. minus on A curvature at x. minus on V derivative iff t≠0

def lane (s : Eye)(μ R : ℝ)(i j m:Eye)(x:E4) := ∑ a:Axis, ∑ b:Axis,∑ u,∑ v,∑ w,
  let f:=tuner a b
  let t := s+1
  let q:=s+2
  let L := load μ R (tick t 0 a u) (tick q 0 a v) (tick s 0 a w) x
  ((fan true i u (f t) * fan true j v (f q) * fan false m w (f s):ℝ):ℂ) * (if s=0 then L else -L)

def corn (μ R : ℝ) (i j m : Eye) (x:E4) := ∑ s, lane s μ R i j m x

lemma choices (a u v : Axis) (s : Eye) : (tick (s+1) 0 a u).length+(tick (s+2) 0 a v).length≤3 := by
   fin_cases s <;> simp [tick,Eye]

variable {μ R : ℝ} (hμ : 0<μ)
include hμ
lemma loam (h : 1≤R) (U V L : Sl) {x:E4} (hx:x≠0) : ContinuousAt (load μ R U V L) x := by
 unfold load weigh; exact tendsto_finsetSum Finset.univ fun i _=> tendsto_const_nhds.smul (tendsto_finsetSum Finset.univ fun j _=> tendsto_const_nhds.smul (tendsto_finsetSum Finset.univ fun k _=>tendsto_const_nhds.smul (Bubble.earns hμ (peak_ge _ h) (peak_ge _ h) hx U V L)))
lemma crops (h : 1≤R)(i j m:Eye){x:E4}(hx:x≠0): ContinuousAt (corn μ R i j m) x:= by
  have hi s: ContinuousAt (lane s μ R i j m) x := by
    unfold lane; refine tendsto_finsetSum _ fun a _=>tendsto_finsetSum _ fun b _=> tendsto_finsetSum _ fun u _=> tendsto_finsetSum _ fun v _=> tendsto_finsetSum _ fun w _=>?_
    dsimp only
    by_cases hh : s=0
    · simp only [hh, ↓reduceIte]; exact tendsto_const_nhds.mul (loam hμ h _ _ _ hx)
    simp only [if_neg hh]; exact tendsto_const_nhds.mul (Tendsto.neg (loam hμ h _ _ _ hx))
  exact tendsto_finsetSum Finset.univ (fun i _=> hi i)

variable {ι : Type} {v : Filter ι} {f : ι→ℝ} (hf : Tendsto f v atTop) {x : ι→E4} {X : E4} (h : Tendsto x v (𝓝 X)) (hx:X≠0)
include hf h hx
lemma chute (U V L : Sl) : (fun w=> load μ (f w) U V L (x w)) =O[v] f := by
  obtain ⟨K,hK,he,hT⟩:= exists_compact_subset isOpen_compl_singleton (show X∈ ({0}ᶜ:Set _) from hx)
  obtain ⟨E,hE,h'⟩:= Bubble.health hμ U V L hK (fun h=> hT h rfl)
  have ht i j k:(fun w=> Bubble.earn μ (peak (f w) i) (peak (f w) j) (peak (f w) k) U V L (x w))=O[v] f:= by
    apply IsBigO.of_bound (E*(times i+times j)); filter_upwards [hf.eventually (eventually_ge_atTop 1),h.eventually (mem_interior_iff_mem_nhds.mp he : ∀ᶠ y in 𝓝 X,y∈K)] with w hw hP
    change 1≤f w at hw
    apply (h' _ (peak_ge _ hw) _ (peak_ge _ hw) _ _ hP).trans; rw [Real.norm_of_nonneg (by linarith : 0≤f w)]; unfold peak; exact le_of_eq (by ring)
  unfold load weigh; simp only [Complex.real_smul]; exact IsBigO.sum (fun i _=> IsBigO.const_mul_left (IsBigO.sum (fun j _=> IsBigO.const_mul_left (IsBigO.sum (fun k _=> IsBigO.const_mul_left (ht i j k) _)) _)) _)
lemma clutch (i j m : Eye): (fun w=> corn μ (f w) i j m (x w))=O[v] f:= by
  unfold corn lane; refine IsBigO.sum fun s _=> IsBigO.sum fun a _=> IsBigO.sum fun b _=> IsBigO.sum fun u _=> IsBigO.sum fun p _=> IsBigO.sum fun t _=> ?_; apply IsBigO.const_mul_left
  split
  · exact chute hμ hf h hx ..
  exact IsBigO.neg_left (chute hμ hf h hx ..)
end YM.SchemeRG11.MSDetector
