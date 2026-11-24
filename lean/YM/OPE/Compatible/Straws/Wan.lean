import YM.OPE.Compatible.Straws.Saber
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass
variable {J:Type}[Fintype J]
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
attribute [local instance] Gauge.frobInner
lemma perch (f:Keys G D→ Tile G J)(h:∀ j,ContDiffAt ℝ ∞ (fun p=> G.mat (f p j)) 0):∃ τ:Tile G D→Tile G J,Continuous τ∧ ∀ᶠ x:U! in 𝓝 0,τ (put x)= f x:=by
      let K:=f 0; let v(x:U!):= f x*K⁻¹; have hp(j:J): ContDiffAt ℝ ∞ (fun x=> G.mat (v x j)) 0:= (h j).mul contDiffAt_const
      have hz:v 0=1:= mul_inv_cancel _; let F:=unput ∘ v; have hx: ContDiffAt ℝ ∞ F 0 := contDiffAt_pi.mpr (fun i=> ((show ContDiffAt ℝ ∞ G.plog (G.mat (v 0 i)) from by rw [hz]; exact G.plog_diff.of_le le_top)).comp (g:=G.plog) (f:=fun x=> G.mat (v x i)) 0 (hp i))
      have hh:Tendsto v (𝓝 0) (𝓝 1):=hz ▸ continuousAt_pi.mpr (fun i=> (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (hp i).continuousAt)
      obtain ⟨V,hV,hF,H⟩:=hx.contDiffOn' (m:=0) (by simp) (by simp); simp only [insert_eq_of_mem (mem_univ _),univ_inter] at H; choose s hs hxW hy using fun i:D=> unput_open (G:=G) i
      let S:= ⋂ i,s i; have hc:S∈𝓝 (1:Tile G D):= iInter_mem.mpr hs; have ht:ContinuousOn (unput (G:=G) (I:=D)) S := continuousOn_pi.mpr (fun i=> (hxW i).mono (iInter_subset ..)); obtain ⟨g,hg,hGH⟩:= sailExt (s:= S ∩ unput ⁻¹' V) (x:=1) (H.continuousOn.comp (ht.mono inter_subset_left) (fun i hi=>hi.2)) (inter_mem hc ((show Tendsto unput (𝓝 (1:Tile G D)) (𝓝 0) from newFold).eventually (hV.mem_nhds hF)))
      refine ⟨fun i=> put (g i)*K,(putC.comp hg).mul continuous_const,?_⟩
      filter_upwards [(show Tendsto (put (G:=G) (I:=D)) (𝓝 0) (𝓝 1) from put_zero ▸ putC.continuousAt.tendsto).eventually hGH, local_zone, hh.eventually Score.Stand.sphere] with i hi hj ht; rw [show g (put i)= F (unput (put i)) from hi,hj,show put (F i)= _ from ht]; unfold v; simp
omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace E] in lemma extStay {x: ℝ→Keys G J} {s:Keys G D→L[ℝ] ℝ}(h: ContDiffAt ℝ ∞ x 0)(hp:x 0=0): ∃ p: Path (Keys G J) G D,p.A=ᶠ[𝓝 0] x ∘ s:=by
      have hv: ContDiffAt ℝ ∞ (x∘s) 0:=(show ContDiffAt ℝ ∞ x (s 0) from s.map_zero.symm ▸ h).comp _ s.contDiff.contDiffAt
      obtain ⟨V,hV,H,hv'⟩:= hv.contDiffOn' (m:=0) (by simp) (by simp); simp only [insert_eq_of_mem (mem_univ _),univ_inter] at hv'; obtain ⟨t,ht,hx⟩:= sailExt (s:=V) (x:= (0:Keys G D)) hv'.continuousOn (hV.mem_nhds H)
      exact ⟨⟨t,hv.congr_of_eventuallyEq hx,ht.measurable,hx.eq_of_nhds.trans (by rw [Function.comp_apply,map_zero,hp])⟩,hx⟩
end Fiber
end YM.OPE.Libra
