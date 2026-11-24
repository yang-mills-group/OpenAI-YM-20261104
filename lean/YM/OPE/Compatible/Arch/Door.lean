import YM.OPE.Compatible.Arch.Howl
import YM.PertExtension.OrbExpansion
/-!
# Mutual variable charts; measurable germ extraction
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics
variable {I J:Type}{G:Gauge}
abbrev Tile (G:Gauge)(I:Type):=I→G.El
abbrev Keys (G:Gauge)(I:Type):=I→G.Color
abbrev put (x: Keys G I):Tile G I:=Chart.expLinks G I x
@[simp] lemma put_zero: put (0:Keys G I) =1:= by funext i; simp [put,Chart.expLinks]
def unput (x:Tile G I) (i:I): G.Color:= G.plog (G.mat (x i))
@[simp] lemma unput_one : unput (1:Tile G I)=0:= by funext; simp [unput]
@[fun_prop] lemma putC : Continuous (put (G:=G) (I:=I)):= by apply continuous_pi;intro i; exact G.lieExp_cont.comp (continuous_apply i)
theorem newFold : Tendsto (unput (G:=G) (I:=I)) (𝓝 1) (𝓝 0):= tendsto_pi_nhds.mpr fun i=>
     G.plog_diff.continuousAt.tendsto.comp ((G.continuous_mat.comp (continuous_apply i)).continuousAt.tendsto (x:= (1:Tile G I))) |>.trans (show 𝓝 _ ≤𝓝 _ from by simp)
theorem unput_open (n:I): ∃ s∈𝓝 (1:Tile G I),ContinuousOn (fun x:Tile G I=> unput x n) s ∧ IsOpen s:=by
     obtain ⟨s,hs,hx⟩:= G.plog_diff.contDiffOn' (m:=0) (by simp) (by simp) -- tuple
     let f:= fun x:Tile G I=> G.mat (x n); have h : Continuous f:= G.continuous_mat.comp (continuous_apply _); obtain ⟨hx,hq⟩:=hx; simp only [insert_eq_of_mem (mem_univ _),univ_inter] at hq
     exact ⟨f ⁻¹' s, (hs.preimage h).mem_nhds (by unfold f; simpa using hx), hq.continuousOn.comp h.continuousOn (mapsTo_preimage ..), hs.preimage h⟩
variable [Fintype I]
lemma uppers : ∃ r: Tile G I→ Keys G I, Measurable r ∧ r =ᶠ[𝓝 1] unput:=by
     choose s hs hc h using (fun i:I=> unput_open (G:=G) i)
     let f(x:Tile G I)(i:I):= (s i).indicator (fun x:Tile G I=> unput x i) x
     refine ⟨f,measurable_pi_lambda _ fun i=> ?_,?_⟩
     · -- continuousOn -> measurable subtype -> evaluate indicator
       exact (hc i).measurable_piecewise continuous_const.continuousOn (h i).measurableSet -- name
     filter_upwards [show ∀ᶠ x in 𝓝 (1:Tile G I), x∈⋂ i,s i from iInter_mem.mpr hs] with x hx; exact funext fun i=>indicator_of_mem (mem_iInter.mp hx i) _
def intake (G:Gauge)(I:Type)[Fintype I]: Tile G I→ Keys G I:= Classical.choose uppers
lemma introM: Measurable (intake G I) := (Classical.choose_spec uppers).1
lemma introG: intake G I =ᶠ[𝓝 1] unput:=(Classical.choose_spec uppers).2
lemma local_zone : ∀ᶠ x in 𝓝 (0:Keys G I), unput (put x)=x:= by
     have hu(i:I):∀ᶠ x in 𝓝 (0:Keys G I), G.plog (G.mat (G.lieExp (x i)))=x i :=(show Tendsto (fun x: Keys G I=> x i) (𝓝 0) (𝓝 0) from (continuous_apply i).continuousAt).eventually (p:=fun x:G.Color=>G.plog (G.mat (G.lieExp x))=x) G.plog_left
     filter_upwards [eventually_all.mpr hu] with x hx using funext hx
lemma local_intro : ∀ᶠ x in 𝓝 (0:Keys G I), intake G I (put x) = x := by
     have hz:Tendsto (put (G:=G) (I:=I)) (𝓝 0) (𝓝 1):=by simpa only [put_zero] using putC.tendsto (0:Keys G I)
     filter_upwards [local_zone,Filter.EventuallyEq.comp_tendsto (introG (I:=I)) hz] with x hx ha; change intake _ _ (put x)=unput _ at ha
     rw [ha,hx]
-- station transformations
end YM.OPE.Libra
