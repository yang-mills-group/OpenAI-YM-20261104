import YM.FVA2.Embr.Room
/-!
 # From interior Coercivity to whole positivity (on fixed finite Epoch history).
 Cost quotes carry all data of a single geometry.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Hearth.Clan RGComparison.Core16 Lumen Fk Forge
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {c f n:Side} {L:Fabric G n} (T:Cloth L)(w:L.Accounts→ℝ→ℝ)

-- exact reversed-tags still global gap although discontinuity outside. Uniform after all finite data.
private lemma bdd (S:StepData c f) : ∃ M:ℝ, ∀ s:S.Choices,∀ x:LinkFrame G f,∀ y:LinkFrame G c, penalty S s x y ≤M:= by obtain ⟨M,hm⟩:= (isCompact_range (show Continuous (BlockGauge.distance S (G:=G)) by unfold BlockGauge.distance; fun_prop)).bddAbove; exact ⟨ M,fun _ _ _=> hm ⟨_,rfl⟩ ⟩
private lemma linear_bound {n:Side}(L:Fabric G n)(w:L.Cost→ℝ→ℝ)(hc:∀ i,ContinuousAt (w i) 0)(h:∀ i,0<w i 0): ∃ M,∀ᶠ v:ℝ in 𝓝 0,∀ x, L.installment (fun i=> w i v) x≤ M:= by
 cases L with
 | endcap=> refine ⟨0, Filter.Eventually.of_forall fun v x=>(zero_tax ..).le⟩
 | layer S H t hf U=>
    obtain ⟨d,hD⟩:= bdd (G:=G) S; obtain ⟨M,hM⟩:= linear_bound U (w∘some) (fun _=> hc _) (fun _=> h _);
    let f:= w none
    have he:∀ᶠ v in 𝓝 (0:ℝ), 0≤ f v ∧ f v≤ f 0 +1:= (hc none).eventually ((eventually_ge_nhds (h none)).and (eventually_le_nhds (lt_add_one ..)))
    refine ⟨(f 0+1)*max d 0 +M,?_⟩; filter_upwards [hM,he] with v hv hh x; rw [tax_split]; exact add_le_add ((mul_le_mul_of_nonneg_left ((hD t _ _).trans (le_max_left ..)) hh.1).trans (mul_le_mul_of_nonneg_right hh.2 (le_max_right ..))) (hv _)
termination_by structural L
private lemma frame_bound (hc:∀ i,ContinuousAt (w i) 0)(h:∀ i,0<w i 0): ∃ M,∀ᶠ v:ℝ in 𝓝 0,∀ x, L.spend (fun i=>w i v) x≤M:= by
 obtain ⟨M,hM⟩:= (isCompact_range (show Continuous (fun u:L.LinksOn=> wilson (L.principal u)) from ((Wilson.energy_cont.comp ((Orb.lift_cont G).comp L.principal_cont)).div_const _) )).bddAbove
 obtain ⟨d,hD⟩:= linear_bound L (w∘some) (fun i=>hc _) (fun i=>h _)
 let f:= w none; have he:∀ᶠ v in 𝓝 (0:ℝ), 0≤f v∧ f v≤ f 0+1:= (hc none).eventually ((eventually_ge_nhds (h none)).and (eventually_le_nhds (lt_add_one ..)))
 refine ⟨(f 0+1)*max M 0 + d,?_⟩; filter_upwards [he,hD] with v ⟨hV,hv⟩ hd x; rw [budget_sum]; exact add_le_add ((mul_le_mul_of_nonneg_left ((hM ⟨x,rfl⟩).trans (le_max_left ..)) hV).trans (mul_le_mul_of_nonneg_right hv (le_max_right ..))) (hd _)

variable (y:Flats G (Bottom L))(t:Clan L)
local notation "X"=> (Warm T→G.El)
local notation "D"=> desk T w y
variable {Y₀ : L.Accounts→PowerSeries ℝ}{p:ℕ} (h:∀ i,0<term (Y₀ i) 0)(hp:∀i,Through p (amount (w i)) (Y₀ i))(H:∀i,ContDiffAt ℝ ω (w i) 0)
include h hp H
lemma starts : ∀ᶠ v:ℝ in 𝓝 0,∀ x,∀ t:Clan L,0≤ D v t x:= by
 filter_upwards [eventually_all.mpr (fun i=> (H i).continuousAt.eventually (eventually_gt_nhds (zeroWeight w Y₀ h p hp i))) ] with v hv x t; unfold desk; rw [actual]; apply Fabric.nonneg_cost; exact fun i=> hv _
local notation "R"=> install L T t
local notation "z"=> (w∘ Option.map (accounts L t))
lemma grant (K:Set X)(hk:IsOpen K)(hA:1∈K) : ∃ c>0,∀ᶠ v:ℝ in 𝓝 0,∀ x∉K,c≤ D v t x:= by
 let F:= (yarn T t); let y':=pointsAt L t y
 let T':= install L T t
 have hw(i:(changeTag L t).Accounts): ContinuousAt (z i) 0:=(H _).continuousAt; obtain ⟨c,hc,H⟩:= uniformFront T' y' z hw (fun i=> zeroWeight w Y₀ h p hp _) ((F.symm) ⁻¹' K) (hk.preimage F.symm.continuous) (show 1∈(F.symm) ⁻¹' K from by rw [show (1:_)=F 1 from (yarn_unit T t).symm]; simpa using hA)
 refine ⟨c,hc,?_⟩; filter_upwards [H] with v hv x hx; unfold desk; rw [actual]; exact hv _ (fun hk=>hx (by simpa only [Homeomorph.symm_apply_apply] using (show F.symm (F x)∈ K from hk)))
lemma reachable : ∃ c>0,∀ᶠ v:ℝ in 𝓝 0,∀ x:X,D v t x≤c:= by
 obtain ⟨m,hM⟩:= frame_bound (L:=changeTag L t) z (fun i=>(H _).continuousAt) (fun i=>zeroWeight w Y₀ h p hp _)
 refine ⟨max 1 m,lt_max_of_lt_left (by norm_num),hM.mono fun v hv x=>?_⟩; unfold desk; rw [actual]; exact (hv _).trans (le_max_right ..)

-- chosen width. interior lump contacts cover actual (nib) meters.
omit h hp H
lemma crisp_nbhd {P:G.El→Prop} (h:∀ᶠ v in 𝓝 1,P v):∃ d>0,∀ v:G.El,G.chord v<d→P v:= by
 obtain ⟨ε,hε,h⟩:= Metric.mem_nhds_iff.mp h; have hg:= G.colorScale_pos; refine ⟨ε/G.colorScale,by positivity,fun u hu=> h (Metric.mem_ball.mpr ?_)⟩
 change dist (G.mat u) (G.mat 1) < ε; rw [dist_eq_norm,G.mat_one]; exact (div_lt_div_iff_of_pos_right hg).1 hu
lemma ramp {ι:Type}[Fintype ι] (f: Set (ι→G.El))(h:f ∈ 𝓝 1): ∃ ε>0,∀ x:ι→G.El, Lumen.Planet.crisp ε univ x→ x ∈ f:= by
 obtain ⟨ε,hε,h⟩:= Metric.mem_nhds_iff.mp h; have hg:= G.colorScale_pos
 refine ⟨ε/G.colorScale,by positivity,fun u hu=> h (Metric.mem_ball.mpr ((dist_pi_lt_iff hε).mpr (fun i=> ?_)))⟩
 change dist (G.mat (u i)) (G.mat 1)< ε; rw [dist_eq_norm,G.mat_one]; exact (div_lt_div_iff_of_pos_right hg).mp (hu i (mem_univ _))
lemma shine {P:ℝ × X→ Prop} (h:∀ᶠ a in 𝓝 ((0:ℝ),(1:X)),P a) : ∃ ε>0,∀ᶠ t in 𝓝 (0:ℝ),∀ x:X, Lumen.Planet.crisp ε univ x→ P (t,x):= by
 rw [nhds_prod_eq] at h; obtain ⟨A,hA,B,hB,H⟩:= mem_prod_iff.mp h; let v:= ramp _ hB; obtain ⟨ε,hε,he⟩:= v; exact ⟨ε,hε, Filter.mem_of_superset hA (fun a ha x hx=> H ⟨ha,he x hx⟩)⟩

structure Adhere (t:Clan L)(A v:ℝ):Prop where
 tiny (x:X)(i:Warm T) : Forge.nib x i≤ A * (v^2+ D v t x)
 suite (x:X) : D v t x≤ A *(v^2 + ∑ i,nib x i)
omit h hp H in
lemma onward {r u v:ℝ}(hA:r≤u)(he:∀ x:X,0≤ D v t x)(H:Adhere T w y t r v): Adhere T w y t u v:=⟨fun x i=>(H.tiny x i).trans (mul_le_mul_of_nonneg_right hA (add_nonneg (sq_nonneg _) (he _))),fun x=>(H.suite x).trans (mul_le_mul_of_nonneg_right hA (add_nonneg (sq_nonneg _) (sum_nonneg (fun _ _=> sq_nonneg _))))⟩

include h hp H
lemma admissibleTag : ∃ A>0,∀ᶠ v:ℝ in 𝓝 0, Adhere T w y t A v:= by
 obtain ⟨a,ha,he⟩:= minimum_in T w y h hp H; obtain ⟨b,hb,hB⟩:= maximum_in T w y h hp H; obtain ⟨d,hd,F⟩:= shine T (he.and hB); let K:= {x:X| Lumen.Planet.crisp d univ x}; obtain ⟨c,hc,G0⟩:= grant T w y t h hp H K (Lumen.Planet.crisp_open ..) (fun i _=> G.chord_one.trans_lt hd); obtain ⟨M,hM,Q⟩:= reachable T w y t h hp H
 let A:= max (max a b) (max (4/c) (M/d^2))
 have ha0: a≤ A:= le_trans (le_max_left ..) (le_max_left ..)
 have hb0: b≤ A:= le_trans (le_max_right a b) (le_max_left ..)
 refine ⟨A,ha.trans_le ha0,?_⟩; filter_upwards [F,starts T w y h hp H,G0,Q] with v hf hu hc0 h0;
 constructor
 · intro x i; by_cases hx:x∈K
   · exact ((hf x hx).1 t i).trans (mul_le_mul_of_nonneg_right ha0 (add_nonneg (sq_nonneg _) (hu _ _)))
   calc
    _ ≤ 2^2 := pow_le_pow_left₀ (G.chord_nonneg _) (G.chord_le_two _) _
    _ ≤ (4/c)*(D v t x) := by have l:= mul_le_mul_of_nonneg_left (hc0 x hx) (div_nonneg (show (0:ℝ)≤4 by norm_num) hc.le); rw [div_mul_cancel₀ _ hc.ne'] at l; exact le_trans (by norm_num) l
    _ ≤ _ := mul_le_mul ((le_max_left ..).trans (le_max_right ..)) (le_add_of_nonneg_left (sq_nonneg _)) (hu _ _) (ha.le.trans ha0)
 intro x; let u:=v^2+∑ i,nib x i; have hw:0≤u:= add_nonneg (sq_nonneg _) (sum_nonneg fun i _=> sq_nonneg _)
 by_cases hx:x∈K; exact ((hf x hx).2 t).trans (mul_le_mul_of_nonneg_right hb0 hw)
 change ¬Lumen.Planet.crisp d univ x at hx; simp only [Lumen.Planet.crisp,not_forall] at hx; obtain ⟨i,_,hi⟩:= hx; replace hi:= not_lt.mp hi; have hy:d^2≤ u:= (pow_le_pow_left₀ hd.le hi 2).trans ((single_le_sum (f:=nib x) (fun i _=> sq_nonneg _) (mem_univ i)).trans (le_add_of_nonneg_left (sq_nonneg _)))
 exact (h0 x).trans (((div_mul_cancel₀ M (pow_pos hd 2).ne').symm.le).trans (mul_le_mul ((le_max_right ..).trans (le_max_right ..)) hy (sq_nonneg _) (ha.le.trans ha0)))

lemma admissible : ∃ A>0,∀ᶠ v:ℝ in 𝓝 0,∀ t,Adhere T w y t A v:= by
 choose f hf F using fun t=> admissibleTag T w y t h hp H
 have hx : ∀ t,f t≤ ∑ k,f k:=fun t=>single_le_sum (fun i _=> (hf i).le) (mem_univ t)
 let A:ℝ:= (∑ k, f k)+1; exact ⟨ A, by unfold A; linarith only [show 0≤∑ k,f k from sum_nonneg fun i _=> (hf i).le], ((eventually_all.mpr F).and (starts T w y h hp H)).mono fun v ⟨hv,hy⟩ t=> onward T w y t ((hx t).trans (le_add_of_nonneg_right zero_le_one)) (fun x=> hy x t) (hv t) ⟩
end YM.FVA2.Embr
