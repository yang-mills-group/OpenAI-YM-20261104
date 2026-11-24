import YM.Comparison.RG02.Bare.Convergence
import YM.Comparison.RG02.Laplace.Choice
/-!
# Laplace test on full top-step measure, genuine complement cost

 Use Gap including Wilson energy on all actual sectors *and all assignments of predictor*.
 Fixed geometry, no growing radius estimates. Immediate cheaper inside-only expansion supplied by
 Facing API. Does not hold arbitrary step data without branch uniqueness. Does not discard off
 masks or old-e costs in later steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory Lattice Wilson Tree Pressure RG Integral Actual Precision Laplace
open PertExtension.Series PertExtension.Series.Tested
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio)
local notation "V"=>Config G c
local notation "U"=>Config G f
local notation "Y"=>F.Slice G
variable (v : Config G c) (y : F.Slice G) (t : S.Choices)

def pile : ℝ := Wilson.energy (F.drape y) + Precision.noiseTaylor S v (F.drape y) t
lemma nonnegative_pile (u : Config G f) : 0≤ Precision.noiseTaylor S v u t:= mul_nonneg (S.kernel.penalty_pos.le) (sum_nonneg fun _ _=> (G.price_range _).1)

variable (ht : S.patch.Branches S.kernel G)
include ht
lemma pile_positive (h : y≠1) : 0<pile F 1 y t:= by
   have hp:= energy_nonneg (F.drape y); have hq:=nonnegative_pile (1:V) t (F.drape y); unfold pile
   rcases hp.eq_or_lt with he|he; swap; exact add_pos_of_pos_of_nonneg he hq
   rw [← he,zero_add]; refine lt_of_le_of_ne hq ?_
   intro hh
   have hf:= flat_pin he.symm; apply h; apply unique_root S ht hf t _ F rfl
   funext i; obtain hu := ((Finset.sum_eq_zero_iff_of_nonneg (fun u (_:u∈Finset.univ)=> (G.price_range ((1:V) u * (S.prediction (F.drape y) t u)⁻¹)).1)).mp ((mul_eq_zero.mp hh.symm).resolve_left S.kernel.penalty_pos.ne')) i (Finset.mem_univ _)
   exact (mul_inv_eq_one.mp (ground_floor _ hu)).symm

private lemma pile_near (hy : y≠1): ∀ᶠ x : (ℝ × Config G c) × F.Slice G in 𝓝 ((0,1),y), x.1.1 < pile F x.1.2 x.2 t := by
   by_cases h: energy (F.drape y)=0
   · have hp :=foretells S (flat_pin h) ht t
     have hP : ContinuousAt (fun x : (ℝ×Config G c) × (F.Slice G)=> pile F x.1.2 x.2 t) ((0,1),y) := by
        unfold pile; apply ContinuousAt.add ((energy_cont.comp (F.continuous_drape.comp continuous_snd)).continuousAt); unfold Precision.noiseTaylor; apply ContinuousAt.const_mul

        let f := fun z : V×V => ∑ e, G.price (z.1 e*(z.2 e)⁻¹)
        have hg : ContinuousAt (fun x:(ℝ×V)×Y=> S.prediction (F.drape x.2) t) ((0,1),y):= hp.comp (x:=((0,1),y)) (f:=fun x:(ℝ×V)×Y=> F.drape x.2) (F.continuous_drape.comp continuous_snd).continuousAt
        change ContinuousAt (f ∘ fun x : (ℝ × V) × Y=> (x.1.2,S.prediction (F.drape x.2) t)) _
        exact ((show Continuous f from by unfold f; fun_prop).continuousAt).comp (((continuous_snd.comp continuous_fst).continuousAt).prodMk hg)
     exact ((continuous_fst.comp continuous_fst).continuousAt.eventually_lt hP (pile_positive F y t ht hy))
   have hv:= lt_of_le_of_ne (energy_nonneg _) (Ne.symm h)
   have he:ContinuousAt (fun x : (ℝ × V) × Y=> Wilson.energy (F.drape x.2)) ((0,1),y):=(energy_cont.comp (F.continuous_drape.comp continuous_snd)).continuousAt
   filter_upwards [(((continuous_fst.comp continuous_fst).continuousAt).eventually_lt he hv)] with x hx
   exact hx.trans_le (le_add_of_nonneg_right (nonnegative_pile x.1.2 t _))

lemma chamber (A : Set (F.Slice G)) (hv : A∈𝓝 1) (ha : IsOpen A):
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ z : Config G c in 𝓝 1, ∀ y, y∉A → δ≤pile F z y t := by
   let E := {x : (ℝ × Config G c) × F.Slice G | x.1.1 < pile F x.1.2 x.2 t}
   obtain ⟨B,Q,hB,hQ,hT,hU,H⟩:= generalized_tube_lemma (X:=ℝ×V) (s:={((0:ℝ),1)}) (n:=interior E) isCompact_singleton ha.isClosed_compl.isCompact isOpen_interior (by
      rintro ⟨x,y⟩ ⟨he,hb⟩; obtain rfl : x=(0,1):=Set.mem_singleton_iff.mp he
      rw [mem_interior_iff_mem_nhds]; exact pile_near F y t ht (fun e=> hb (e ▸ mem_of_mem_nhds hv)))
   obtain ⟨C,hC,D,hD,H'⟩:= mem_nhds_prod_iff.mp (hB.mem_nhds (hT (Set.mem_singleton (0,1))))
   obtain ⟨δ,Hδ,hδ⟩:= ((show ∀ᶠ x in along, x∈C from nhdsWithin_le_nhds hC).and Tested.eventually_pos).exists -- fix
   exact ⟨δ,hδ,(show ∀ᶠ z in 𝓝 (1:V), z∈D from hD).mono (fun z hz y hy=> ((show ((δ,z),y)∈E from interior_subset (H (a:=((δ,z),y)) ⟨H' ⟨Hδ,hz⟩,hU hy⟩) ) : δ < pile F z y t).le)⟩
end YM.Comparison.RG02.Bare
