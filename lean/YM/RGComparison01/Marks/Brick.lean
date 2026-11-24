import YM.RGComparison01.Marks.Flights
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Checks.Rooted
variable {p : BudgetPoint}{α : Type} {P : α→Support c}{V J: α → Config G c→ℝ}
variable (h:Rooted P V p a w)
include h
lemma nonnegative : 0 ≤ w :=by obtain ⟨b,hb,hs⟩:=h; exact budget_nonneg (hs (0:Site c))
lemma larger (hp:w ≤ v) : Rooted P V p a v:= credited p h hp
lemma decreasing (ha:t ≤ a): Rooted P V p t w:= by
   obtain ⟨b,hb,hB⟩:=h; refine ⟨b,hb,fun i => budget_mono (hB i) (fun j=> ?_) (fun j=> ?_)⟩
   · split; exact mul_nonneg (hb _|>.2.1) (Real.exp_nonneg _); rfl
   split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (hb _|>.2.1); rfl
lemma viable (i:α): p.Regular (P i) (V i):= by obtain ⟨b,h,_⟩:=h; exact (h i).1
lemma scales (t : α→ℝ) (ht:∀ i,|t i|≤ B)(hB:0 ≤ B): Rooted P (fun i=> t i • V i) p a (B*w):= by
   obtain ⟨b,he,hb⟩:=h; refine ⟨fun i=> B*b i,fun i=>⟨CouplingShape.reg_scale _ (he i).1,mul_nonneg hB (he i).2.1,fun X hx=> ?_⟩,fun i=>?_⟩
   · exact VerifiedReset.sup_le (CouplingShape.sup_scale _ ((he i).2.2 X hx)) (mul_le_mul_of_nonneg_right (ht i) (he i).2.1)
   convert budget_scale hB (hb i) using 1; ext j; split <;> simp [*, mul_assoc]
lemma fresh (hx:∀ i,J i=V i ∨ J i=0): Rooted P J p a w:=by
   let s (i:α):ℝ:= if J i=V i then 1 else 0
   have he : ∀ i,|s i| ≤ 1:= fun i=>by unfold s; split<;> norm_num
   have hP:= h.scales s he (by norm_num); rw [one_mul] at hP
   rw [show J=(fun i=> s i • V i) from funext (fun i=> ?_)]; exact hP
   unfold s; split; next ht=> rw [one_smul]; exact ht
   next hz=> rw [zero_smul]; exact (hx i).resolve_left hz
lemma sumBudgetR (hp : Rooted P J p a v) : Rooted P (V+J) p a (w+v) := by
   obtain ⟨b,h,hb⟩:=h; obtain ⟨c,hp,hc⟩:=hp
   refine ⟨b+c,fun i=>⟨?_,add_nonneg (h i).2.1 (hp i).2.1,fun j hj=> ?_⟩,fun i=>?_⟩
   · rw [Pi.add_apply,show V i+J i=V i-(-1:ℝ) • J i from (by simp)]; exact CouplingShape.reg_sub (h i).1 (CouplingShape.reg_scale _ (hp i).1)
   · rw [Pi.add_apply,show V i+J i=V i-(-1:ℝ) • J i from (by simp)]; have hx:=CouplingShape.sup_scale (-1) ((hp i).2.2 j hj); rw [abs_neg,abs_one,one_mul] at hx; exact CouplingShape.sup_sub (h i).1 (CouplingShape.reg_scale _ (hp i).1) ((h i).2.2 j hj) hx
   convert budget_plus (hb i) (hc i) using 2 with j; split <;> simp [*, add_mul]
lemma needle (i:α) (x: Site c) (hX:x∈P i) (hv:0 ≤ a): p.supBounds x (P i) (V i) w:= by
   obtain ⟨b,h,he⟩:=h; refine VerifiedReset.sup_le ((h i).2.2 x hX) ?_
   have ht := budget_single (he x) i; rw [if_pos hX] at ht; exact (le_mul_of_one_le_right (h i).2.1 (Real.one_le_exp (mul_nonneg hv (by positivity)))).trans ht
-- Root transfer
lemma tap (o:α→Site c)(hp:∀ i,o i∈ P i)(he:Quotes.preExponent p≤ a): Meadow.Budget p (fun i=> (⟨o i,P i,hp i⟩:RegularAddress c)) V w:=by
   obtain ⟨b,h,hB⟩:=h.decreasing he; refine ⟨b,fun i=> budget_mono (hB i) (fun j=>?_) (fun j=>?_),fun i=> ⟨(h i).1,(h i).2.2 (o i) (hp i)⟩⟩
   · split; exact mul_nonneg (h j|>.2.1) (Real.exp_nonneg _); rfl
   split; next hv=> rw [if_pos (show i∈P j from (show o j=i from hv) ▸ hp j)]
   next=> exact (hB i).1 _
lemma fadings (J:ℕ→ α → Prop) (hJ: ∀ i,V i≠0 → ∀ᶠ n in atTop,¬J n i) (hc:0< t):
    ∀ᶠ n in atTop, Rooted P (fun i=> if J n i then V i else 0) p a t:=by
  obtain ⟨b,h,hb⟩:=h
  let u n i:= if J n i ∧ V i≠0 then b i else 0; have h₀ n i:0 ≤ u n i:= by unfold u; split; exact (h i).2.1; exact le_rfl
  let g n x i:= if (x:Site c)∈P i then u n i *Real.exp (a*coverNumber p.B (P i)) else 0; have hg n x i:0≤ g n x i:= by unfold g; split; exact mul_nonneg (h₀ n i) (Real.exp_nonneg _); rfl
  let k x i:= if (x:Site c)∈P i then b i *Real.exp (a*coverNumber p.B (P i)) else 0
  have hs n x i:g n x i≤ k x i:= by unfold g k u; split_ifs; rfl; rw [zero_mul]; exact mul_nonneg (h _|>.2.1) (Real.exp_nonneg _); exact le_rfl
  have hz x: ∀ᶠ n in atTop, SumBudget (g n x) t := by
    have hh : Tendsto (fun n=> ∑' i,g n x i) atTop (𝓝 0):= by
      have hp i : Tendsto (fun n=> g n x i) atTop (𝓝 0):= by
        unfold g; split_ifs; swap; · exact tendsto_const_nhds
        by_cases h: V i=0; swap; · exact tendsto_const_nhds.congr' ((hJ i h).mono fun n hv=>by simp [u,hv])
        simp_rw [show ∀ n:ℕ,u n i=0 from fun _=>if_neg (fun hv=>hv.2 h),zero_mul]; exact tendsto_const_nhds
      have hf:= tendsto_tsum_of_dominated_convergence (show Summable (k x) from (hb x).2.1) hp (Eventually.of_forall fun i v=>by simpa only [Real.norm_of_nonneg (hg i x v)] using hs i x v)
      rwa [tsum_zero] at hf
    exact (hh.eventually_le_const hc).mono (fun n hn=>⟨hg n x,(hb x|>.2.1).of_nonneg_of_le (hg n x) (hs n x),hn⟩)
  filter_upwards [eventually_all.mpr hz] with n hn; refine ⟨u n,fun i=>?_,hn⟩
  have he (hF: (if J n i then V i else 0)=0) : p.Regular (P i) (if J n i then V i else 0) ∧ 0 ≤ u n i∧ ∀ j∈P i,p.supBounds j (P i) (if J n i then V i else 0) (u n i) := by
    rw [hF]; exact ⟨CouplingShape.reg_const _,h₀ _ _,fun j _=> sup_le (CouplingShape.sup_const 0) (by rw [abs_zero]; exact h₀ n i)⟩
  by_cases ht : J n i ∧ V i≠0
  · unfold u; dsimp only; rw [if_pos ht.1,if_pos ht]; exact h i -- order
  apply he; by_cases hs:J n i; rw [if_pos hs]; exact Classical.byContradiction (fun hh=> ht ⟨hs,hh⟩); exact if_neg hs
end Checks.Rooted
end YM.RGComparison01.Pledge
