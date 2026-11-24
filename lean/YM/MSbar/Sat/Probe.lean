import YM.MSbar.Sat.Pitch
import YM.MSbar.Sat.Chord
import YM.MSbar.Sage.Sailing
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable (G:Gauge)
open Metric Next.Fluctuations
-- avoid measurable claims on unspecified global plog.Its restriction true.
structure Voice (G:Gauge) where
   δ : ℝ
   r : ℝ
   C : ℝ
   decode : G.El→ G.Color
structure Clear (X:Voice G):Prop where
   cost : 1≤X.C
   dist : 0<X.δ
   depth : 0<X.r
   reads : Measurable X.decode
   near (u:G.El) (h:G.chord u ≤ X.δ): X.decode u=G.plog (G.mat u) ∧ G.lieExp (X.decode u)=u ∧ ‖X.decode u‖ ≤ X.C*G.chord u
   small (a:G.Color) (h:‖a‖ ≤ X.r): X.decode (G.lieExp a)=a ∧ G.chord (G.lieExp a) ≤ X.C*‖a‖
   turns (u v:G.Color)(R:ℝ) (h:R ≤ X.r) (hv:‖u‖ ≤ R)(hx:‖v‖ ≤ R): ‖X.decode (G.lieExp u*G.lieExp v) -u-v‖ ≤ X.C*R*‖u‖
lemma vocals : ∃ X:Voice G,Clear G X:=by
    obtain ⟨c,r,hC,hr,hP⟩:=log_chart_cost G; obtain ⟨x,b,hx,hb,hF⟩:=chord_chart_cost G
    obtain ⟨t,hT,hK⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp G.plog_left
    obtain ⟨d,s,hd,hS,hs⟩:=spruce G
    let a(G':G.El):=G.plog (G.mat G')
    have h : ∀ᶠ u in 𝓝 (1:G.El), ContinuousAt a u:= by
       have hw:= (G.plog_diff.of_le (by simp : (1:WithTop ℕ∞)≤ω)).eventually (by simp)
       have ha:Tendsto G.mat (𝓝 1) (𝓝 1):= G.continuous_mat.tendsto _
       exact (ha.eventually hw).mono (fun i hk=> hk.continuousAt.comp (G.continuous_mat.continuousAt))
    obtain ⟨l,hL,h⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp h
    let p:= min r (l/G.colorScale); have hB:= G.colorScale_pos;have hp:0<p:=lt_min hr (by positivity)
    let k:= min t (min s (min b (p/(2*x)))); have hk:0 < k:=lt_min hT (lt_min hS (lt_min hb (by positivity)))
    let A:= {u:G.El | G.chord u ≤ p}; have hA: IsClosed A:=isClosed_le G.continuous_chord continuous_const
    have htA : ContinuousOn a A := fun u hu=> (h (show u∈closedBall (1:G.El) l from mem_closedBall.mpr (by
       change dist (G.mat u) 1 ≤ l; rw [dist_eq_norm,← chord_dist,mul_comm]; exact (le_div_iff₀ hB |>.mp ((show G.chord u ≤ p from hu).trans (min_le_right ..)))))).continuousWithinAt
    have hΩ z (he:‖z‖ ≤ k) : G.chord (G.lieExp z) ≤ p/2:=by
        apply (hF z (he.trans (le_trans (min_le_right ..) ((min_le_right ..).trans (min_le_left ..))))).trans; have ht : ‖z‖ ≤ p/(2*x):=he.trans (le_trans (min_le_right ..) ((min_le_right ..).trans (min_le_right ..))); have hg:2*x>0:=by positivity
        have hs := (le_div_iff₀ hg).mp ht; linarith only [hs]
    let M:= A.indicator a; refine ⟨⟨p,k,1+c+x+d,M⟩,⟨by change _≤ 1+c+x+d; linarith only [hC,hx,hd],hp,hk, htA.measurable_piecewise (continuous_const.continuousOn) hA.measurableSet,fun u hu=> ?_,fun z hz=> ?_,fun u v R hQ hy ht=>?_⟩⟩ -- syntax
    · let g:= G.chord u; have hk: G.chord u ≤ r:=hu.trans (min_le_left ..); obtain ⟨H,hk⟩:= hP u hk
      change M u=a u∧_
      have ha:M u=a u:= Set.indicator_of_mem (show u∈A from hu) _
      exact ⟨ha, (congr_arg _ ha).trans H,(congr_arg norm ha).trans_le (hk.trans (mul_le_mul_of_nonneg_right (show c≤ _ from (by change c ≤ 1+c+x+d; linarith only [hx,hd])) (G.chord_nonneg _)))⟩
    · have hu: G.lieExp z∈A:= (hΩ z hz).trans (half_le_self hp.le)
      have ht:‖z‖ ≤ k:= hz; refine ⟨(Set.indicator_of_mem hu a).trans (hK (mem_closedBall.mpr (show dist z 0 ≤ t from by rw [dist_zero_right]; exact ht.trans (min_le_left ..)))),?_⟩; exact (hF z (ht.trans (le_trans (min_le_right ..) ((min_le_right ..).trans (min_le_left ..))))).trans (mul_le_mul_of_nonneg_right (show x ≤ 1+c+x+d by linarith only [hC,hd]) (norm_nonneg _))
    have he:G.lieExp u*G.lieExp v∈A:= (G.chord_triangle _ _).trans (((add_le_add (hΩ _ (hy.trans hQ)) (hΩ _ (ht.trans hQ)))).trans_eq (by ring))
    change ‖A.indicator a _-u-v‖≤ _; rw [Set.indicator_of_mem he]; exact (hs R (hQ.trans (le_trans (min_le_right ..) (min_le_left ..))) u v hy ht).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show d ≤ 1+c+x+d by linarith only [hC,hx]) ((norm_nonneg _).trans ht)) (norm_nonneg _))
end YM.MSbar.Heath
