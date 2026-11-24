import YM.OPE.Compatible.Munch.Vale
import YM.OPE.Compatible.Mason.Zeal
/-! # range Cut protocols for telescoping. Numeric. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m:ℕ}{ε v t c:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f)(w:Bid.Dir G L.c)
local notation "Xθ"=> Bid.Dir G L.c
noncomputable abbrev rangeG (L:Host K T)(x:Site L.f)(i:ℕ): Finset (Body 1 L.c):=univ.filter fun j:Body 1 L.c=> L.Z.ratio.embed j.1∈ neighbors (64*i) x
noncomputable abbrev Qspot (L:Host K T)(x:Site L.f)(n:ℕ): (Bid.Dir G L.c) →L[ℝ] (Bid.Dir G L.c):= ContinuousLinearMap.pi fun i=> if i∈rangeG L x n then ContinuousLinearMap.proj (φ:=fun _ : Body 1 L.c=> G.Color) (R:=ℝ) i else 0
-- warning L explicit macro. change
noncomputable abbrev κceil (i:ℕ):ℕ:= ballCost (64*i)*Fintype.card (TypeFace 1)
lemma Round (i:ℕ): (rangeG L x i).card ≤ κceil i:=by
       let f: Body 1 L.c↪ Body 1 L.f:= ⟨fun j=> (L.Z.ratio.embed j.1,j.2),fun j k h=>?_⟩; swap; · exact Prod.ext ((show L.Z.ratio.parent (L.Z.ratio.embed j.1)= _ from L.Z.ratio.embed_parent j.1).symm.trans ((congr_arg L.Z.ratio.parent (Prod.mk.inj h).1).trans (L.Z.ratio.embed_parent k.1))) (Prod.mk.inj h).2
       have hz: (rangeG L x i).map f ⊆neighbors (64*i) x ×ˢ (Finset.univ:Finset (TypeFace 1)):=by
            intro j hj; obtain ⟨k,hk,rfl⟩:=mem_map.mp hj; exact mem_product.mpr ⟨(mem_filter.mp hk).2,mem_univ _⟩
       have he:=Finset.card_le_card hz; rw [card_map,card_product,card_univ] at he; exact he.trans (Nat.mul_le_mul_right _ (neighbors_card ..))
lemma HopQ (he:i ≤ j) : rangeG L x i⊆ rangeG L x j := fun k hk=> mem_filter.mpr ⟨Finset.mem_univ _,(neighbors_mem ..).mpr (((neighbors_mem ..).mp (mem_filter.mp hk).2).trans (by omega))⟩
lemma Q_on {v:Body 1 L.c}(hv:v ∈rangeG L x i) : Qspot L x i w v=w v:=by unfold Qspot; simp only [ContinuousLinearMap.pi_apply]; rw [if_pos hv];rfl
lemma Q_off {v:Body 1 L.c}(hv:v∉rangeG L x i): Qspot L x i w v=0:=by unfold Qspot; simp only [ContinuousLinearMap.pi_apply]; rw [if_neg hv];rfl
lemma foothQ (he:i ≤ j): ‖Qspot L x i w‖≤ ‖Qspot L x j w‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p=>by
        by_cases h:p ∈rangeG L x i
        · rw[Q_on x w h]; exact (congr_arg norm (Q_on x w (HopQ x he h)).symm).trans_le (norm_le_pi_norm _ p)
        rw[Q_off x w h,norm_zero]; exact norm_nonneg _
lemma Mouth (j:Wings G L.c)(hv:j.1∈rangeG L x k): cash (JetB G L.c) (Qspot L x k w) j=cash (JetB G L.c) w j:=by unfold JetB; rw [Tip_ψ,Tip_ψ,Q_on x w hv]
lemma Ear_Q (j:Wings G L.c)(hv:j.1∉rangeG L x k): cash (JetB G L.c) (Qspot L x k w) j=0:=by unfold JetB; rw [Tip_ψ,Q_off x w hv]; simp
lemma Reap_Q (he:i ≤ j): ReserveQ L x (worldA L (Qspot L x i w)) (Qspot L x j w) (i:ℝ):=by
      refine ⟨fun v _=>mem_univ _,fun k hk=>?_⟩; have hx: k.1∈ rangeG L x i:=mem_filter.mpr ⟨mem_univ _,(neighbors_mem ..).mpr (by exact_mod_cast hk)⟩; exact (Mouth x w k hx).trans (Mouth x w k (HopQ x he hx)).symm
lemma SoarQ (L:Host K T)(x:Site L.f):∀ᶠ i:ℕ in atTop,Qspot L x i=ContinuousLinearMap.id ℝ (Bid.Dir G L.c):=by
       have ht(k:Body 1 L.c): ∀ᶠ i:ℕ in atTop,k∈rangeG L x i:=by filter_upwards [eventually_ge_atTop (separation x (L.Z.ratio.embed k.1))] with i hi; exact mem_filter.mpr ⟨mem_univ _,(neighbors_mem ..).mpr (by omega)⟩
       filter_upwards [eventually_all.mpr ht] with i hi; apply ContinuousLinearMap.ext; intro w; funext j; exact Q_on x w (hi j)
end
end YM.OPE.Borealis.Galea
