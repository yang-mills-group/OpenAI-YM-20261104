import YM.AveragedStep.Orders.Loads
/-! All-order physical (top only) Schwinger-Dyson error. Currency for L1
outputs against the exact vacuum and any tests on it. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{P:Patch}{K:KernelChoices}{S:StepData c f}
variable (F:Forest S.ratio)(Q:Cuff S.patch S.kernel A)
def fieldKey (e:F.Free)(i:G.ColorIndex): Ink G c f:= (Sum.inl e.val,i)
def vice (t:ℝ)(j:Ink G c f)(w:List (Ink G c f))(d:ℕ)(X:Hand G c f):ℝ:=
    peel j w X-mon w X * chorus S A t j.1 (fingers G j.2) d X
lemma vice_env (w:List (Ink G c f))(x:Site c)(j:Ink G c f)(d:ℕ)(τ:ℝ):Envelope fun z=> vice (S:=S) (A:=A) τ⁻¹ j w d (hands F Q x τ z):=by
 refine hands_env F Q x τ _ ?_
 unfold vice
 simp_rw [←peels j]
 exact (((mon_cont w).continuous_fderiv (by simp)).clm_apply continuous_const).sub ((mon_cont w).continuous.mul (smooth_chorus ..).continuous)

lemma live_range {S:StepData c f}(F:Forest S.ratio)(Q:Cuff S.patch S.kernel A)(x:Site c)(e:F.Free)(z:TopologyQ F G):|live F Q x e z|≤1∧ |outerGate F Q x e z|≤ 1:=by

 have ht(D:Finset (Rim c f)): |∏ i∈D,Cuff.ticket Q (aboard F x z i)| ≤1 :=by
   rw [Finset.abs_prod]; apply Finset.prod_le_one (fun _ _=>abs_nonneg _); intro i _; unfold Cuff.ticket; split
   · rw [abs_of_nonneg Q.trigger.nonneg]; exact Q.trigger.le_one
   simp
 exact ⟨ht _,ht _⟩
-- ensure failures of derivative mask are paid with same δ threshold
lemma wake (Q:Cuff P K A):∃ B D δ:ℝ,1≤B ∧ 0<δ ∧ 0≤D ∧
    (∀ u:G.El,‖Q.logC u‖≤ B*G.chord u) ∧
    (∀ u:G.El, G.chord u<δ → Q.ticket u=1 ∧∀ v:G.Color,Q.incline v u=0) ∧ ∀ i:G.ColorIndex,∀ u,|Q.incline (fingers _ i) u|≤ D:=by
 obtain ⟨E,d,hE,hd,H,J⟩:=Q.log_bought
 choose D hD using fun (i:G.ColorIndex) => Q.incline_bound (fingers G i)
 refine ⟨max E 1,∑ i,max (D i) 0,min d ((Q.width/8)/E), le_max_right .., lt_min hd (by have :=Q.active; positivity),Finset.sum_nonneg (fun i _=>le_max_right ..),fun u=> (J u).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (G.chord_nonneg _)),?_ ,?_⟩
 · intro u h
   obtain ⟨hv,hf⟩:= H u (h.trans_le (min_le_left ..)).le
   have hE': ‖Q.logC u‖< Q.trigger.rIn:= lt_of_le_of_lt (J u) (by rw [mul_comm]; exact lt_div_iff₀ hE |>.mp (h.trans_le (min_le_right ..)))
   have h0 : Q.logC u ∈ ball 0 Q.trigger.rIn:= mem_ball_zero_iff.mpr hE'
   have hz : (Q.trigger:G.Color→ℝ) =ᶠ[𝓝 (Q.logC u)] fun _=>1:=by
     filter_upwards [isOpen_ball.mem_nhds h0] with x hx; exact Q.trigger.one_of_mem_closedBall (ball_subset_closedBall hx)
   unfold Cuff.ticket Cuff.incline; rw [if_pos hv,hz.eq_of_nhds,hz.fderiv_eq]; simp [hv]
 intro i u; unfold Cuff.incline; split
 · change ‖fderiv ℝ (Q.trigger:G.Color→ℝ) (Q.logC u) (fingers G i)‖≤ _; exact (hD i _).trans ((le_max_left (D i) 0).trans (Finset.single_le_sum
      (f:=fun j=>max (D j) 0) (fun j _=>le_max_right ..) (Finset.mem_univ i)))
 rw [abs_zero]; exact Finset.sum_nonneg (fun i _=>le_max_right ..)

structure Cadence (Q:Cuff P K A)(B D δ:ℝ) : Prop where
 price:1≤B
 active:0<δ
 second:0≤D
 log : ∀ u:G.El,‖Q.logC u‖≤ B*G.chord u
 confirm : ∀ u:G.El,G.chord u<δ →Q.ticket u=1 ∧ ∀ v:G.Color,Q.incline v u=0
 rate : ∀ i:G.ColorIndex,∀ u:G.El,|Q.incline (fingers G i) u|≤D
lemma awake (Q:Cuff P K A):∃ B D δ:ℝ, Cadence Q B D δ:=by obtain ⟨B,D,δ,h1,h2,h3,h4,h5,h6⟩:=wake Q; exact ⟨B,D,δ,h1,h2,h3,h4,h5,h6⟩
-- Shape inventory for polynomial Z. Include all hits *and* their suppliers.
def aisle (e:Rim c f)(w:List (Ink G c f)) := home S e ∪ (w.map Prod.fst).toFinset
lemma aisle_self (e:Rim c f)(w:List (Ink G c f)) : e∈aisle (S:=S) e w := Finset.mem_union_left _ (home_self ..)
lemma aisle_slot {e:Rim c f}{w:List (Ink G c f)}{p:Ink G c f}(h:p∈w):p.1∈aisle (S:=S) e w:=Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,h,rfl⟩))
lemma aisle_home (e:Rim c f)(w:List (Ink G c f)):home S e ⊆ aisle (S:=S) e w := Finset.subset_union_left
end YM.AveragedStep
