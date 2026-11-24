import Mathlib.Topology.UrysohnsLemma
import YM.OPE.Compatible.Navy.Post
/-!
# Extending local motions. No claims on other exponential saddles. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J U K:Type}[Fintype I][Fintype J][Fintype U]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable (p: U ≃ I ⊕ J)
local notation "L" => prL p G
local notation "R" => prR p G
-- collar uses log real finite dimensional Hausdorff. Make extension prove via Urysohn. 
private lemma sailExt {X E:Type}[TopologicalSpace X][NormalSpace X][RegularSpace X][NormedAddCommGroup E][NormedSpace ℝ E]
   {f:X→E}{x:X}{s:Set X}(hf:ContinuousOn f s)(hh:s∈𝓝 x):∃ g:X→E,Continuous g ∧ g =ᶠ[𝓝 x] f:=by
      obtain ⟨y,hy,hℓ,h⟩:= exists_mem_nhds_isClosed_subset hh
      obtain ⟨t,ht,hX,hz⟩:= exists_mem_nhds_isClosed_subset (show interior y ∈𝓝 x from isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hy))
      obtain ⟨a,ha,hc,hq⟩:= exists_continuous_zero_one_of_isClosed isOpen_interior.isClosed_compl hX (show Disjoint (interior y)ᶜ t from Set.disjoint_left.mpr fun _ hx hv=> hx (hz hv))
      let g(i:X):= a i • f i; refine ⟨y.indicator g,?_,?_⟩
      · apply continuous_piecewise; rotate_left; · rw [hℓ.closure_eq]; exact a.continuous.continuousOn.smul (hf.mono h)
        · exact continuousOn_const
        intro i hi; unfold g; rw [show a i = 0 from ha (show i∈(interior y)ᶜ from hi.2), zero_smul]
      filter_upwards [ht] with i hi; rw [indicator_of_mem (interior_subset (hz hi)), show g i= _ from (show g i=f i from by unfold g; rw [show a i=1 from hc hi,one_smul])]
lemma buildExt (u: Tile G I→ Tile G J)(h:u 1=1)(hb:∀ j,ContDiffAt ℝ ω (fun x:Keys G I=> G.mat (u (put x) j)) 0):∃ t:Tile G I→Tile G J,Hark t∧ t =ᶠ[𝓝 1] u :=by
    let f(x:Keys G I):= unput (u (put x)); let F(x:Tile G I):=unput (u x)
    have hf:ContDiffAt ℝ ω f 0:=by
         refine contDiffAt_pi.mpr fun i=>?_ ; apply ContDiffAt.comp (f:=fun a: Keys G I=> G.mat (u (put a) i)) _ _ (hb i); rw [put_zero,h]; exact G.plog_diff
    obtain ⟨V,hV,hx,hq⟩:= hf.contDiffOn' (m:=0) (by simp) (by simp); simp only [insert_eq_of_mem (mem_univ _),univ_inter] at hq
    have he: f∘ unput=ᶠ[𝓝 1] F:= (Stand.sphere (D:=I) (G:=G)).mono fun x hx=>congr_arg F hx
    have hT : Tendsto (fun i=> u (put i)) (𝓝 0) (𝓝 1):=by
          let A:= fun i:Keys G I=> u (put i); have ht:A 0=1:=by simp [A,h]
          exact ht ▸ (show YM.Stationary.Army A 0 from hb).cont.tendsto
    have hu : Tendsto u (𝓝 1) (𝓝 1):=by
          refine (hT.comp (newFold (G:=G) (I:=I))).congr' ?_; exact (Stand.sphere (D:=I)).mono fun x hx=> congr_arg u hx
    choose s hs hxW hy using fun i:I=> unput_open (G:=G) i
    let S:= ⋂ i,s i; have hc:S∈𝓝 (1:Tile G I):= iInter_mem.mpr hs; have hh:ContinuousOn (unput (G:=G) (I:=I)) S:= continuousOn_pi.mpr (fun i=>(hxW i).mono (iInter_subset ..))
    obtain ⟨g,hg,H⟩:=sailExt (s:=S ∩ (unput ⁻¹' V)) (hq.continuousOn.comp (hh.mono inter_subset_left) (fun x hx=>hx.2)) (inter_mem hc ((show Tendsto unput (𝓝 (1:Tile G I)) (𝓝 0) from newFold).eventually (hV.mem_nhds hx)))
    let x:= put ∘ g; have hz:x=ᶠ[𝓝 1] u:=by filter_upwards [H.trans he,hu.eventually (p:=fun y:Tile G J=> put (unput y)=y) (Stand.sphere (G:=G))] with i hi hj; change put _= _; rw [hi]; exact hj
    refine ⟨x,⟨putC.comp hg,fun j=> (hb j).congr_of_eventuallyEq ?_,hz.eq_of_nhds.trans h⟩,hz⟩
    filter_upwards [(show Tendsto put (𝓝 (0:Keys G I)) (𝓝 1) from put_zero ▸ putC.continuousAt.tendsto).eventually hz] with i hi; rw [hi]
end YM.OPE.Cascade.Pilot
