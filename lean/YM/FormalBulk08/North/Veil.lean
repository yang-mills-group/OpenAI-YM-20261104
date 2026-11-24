import YM.FormalBulk08.Dove.Pulse

/-! End tile values. No claims (not even e linkage) at unadmitted levels. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I V:Type*}{η C:ℝ}{r:ℕ}{R: Reach V}
abbrev Ends {A:Type*}[TopologicalSpace A] (f:ℕ→A)(a:A):Prop:= Tendsto f atTop (𝓝 a)
def aura (f:ℕ→ℝ):ℝ:= limUnder atTop f
lemma aura_eq {f:ℕ→ℝ}{x:ℝ}(h: Ends f x):aura f=x:= limUnder_eq_iff ⟨x,h⟩ |>.mpr h
lemma aura_pays (f b:ℕ→ℝ)(h:Ends b 0)(ht:∀ᶠ n:ℕ in atTop,∀ m,n≤m →|f n - f m|≤ b n): Ends f (aura f) := by
    obtain ⟨N,H⟩:= eventually_atTop.mp ht
    have hv:Ends (fun n=>b (n+N)) 0:= (tendsto_add_atTop_iff_nat N).mpr h
    obtain ⟨X,hX⟩:= cauchySeq_tendsto_of_complete ((cauchySeq_shift (u:=f) N).1 (cauchySeq_of_le_tendsto_0' (s:=fun n=> f (n+N)) (fun n=>b (n+N)) (fun n m h=> by rw [Real.dist_eq];exact H _ (by omega) _ (by omega)) hv))
    rw [aura_eq hX];exact hX
lemma limit_arr {T:ℕ→Tile V r}{M:Tile V r}(hp:∀ᶠ n in atTop,Bail R η (T n) C)(h:∀ v,Ends (fun n=> T n v) (M v)): Bail R η M C:= by
    refine ⟨hp.exists.choose_spec.1,fun i a=>?_⟩
    rw [ENNReal.tsum_eq_iSup_sum,iSup_le_iff]; intro S
    have hy x : Ends (fun j=> glitter R η (T j) x) (glitter R η M x):= by
        let F (p:ℝ) := Gorge.shine η (wide R x)* ‖p‖ₑ; have hv : Continuous F:= by unfold F Gorge.shine; simp_rw [←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le];exact ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_norm)
        exact hv.continuousAt.tendsto.comp (h x)
    apply le_of_tendsto (tendsto_finsetSum _ (fun j _=> hy j.val)); filter_upwards [hp] with j hj; exact (ENNReal.sum_le_tsum _).trans (hj.2 _ _)
def terminalK (T:ℕ→Tile V r): Tile V r:=fun v=>aura fun n=> T n v
structure Boone (T:ℕ→Tile V r)(U:Tile V r):Prop where
    shares : ∀ v,Ends (fun n=> T n v) (U v)
lemma growthK (z:Fin r){T:ℕ→Tile V r}{b:ℕ→ℝ}(h:0≤η)(he:Ends b 0)(hp:∀ᶠ n:ℕ in atTop,∀ m,n≤m→Bail R η (T n-T m) (b n)): Boone T (terminalK T):= ⟨fun v=>aura_pays _ b he (hp.mono fun n h m ht=>(h m ht).value ‹0≤η› v z)⟩
lemma lossK {T:ℕ→Tile V r}{U:Tile V r}{n:ℕ}(hp:Boone T U)(H:∀ m,n≤m→Bail R η (T n-T m) C): Bail R η (T n-U) C:= limit_arr ((eventually_ge_atTop n).mono fun m h=>H m h) (fun v=> tendsto_const_nhds.sub (hp.shares v))
lemma repeat_foot (S:Schedule)(i:ℕ)(ξ:ℝ)(h:0<ξ): Ends (fun n=>ratioR S n i ξ) 0 := by
    unfold ratioR; have hx:= (S.shrinks.div_const (S.a i)); have he:= hx.rpow (tendsto_const_nhds (x:=ξ)) (Or.inr h); simpa [Real.zero_rpow h.ne'] using he
-- row width and pace
lemma linger {f:ℕ→Cover→ℝ}{g:Cover→ℝ}(h:∀ i, Ends (fun n=> f n i) (g i))(hp:∀ᶠ n in atTop,Width η C (f n)) : Width η C g:= by
    let w (i:Cover):= Real.exp (η*size i); let d (i:Cover):ℝ:= w i*‖g i‖; have hd i:0≤d i:= mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    have ht (S:Finset Cover): ∑ i∈S,d i≤ C := by
       apply le_of_tendsto (tendsto_finsetSum _ (fun i _=> (h i).norm.const_mul (w i))); filter_upwards [hp] with n hn; exact ((hn.2.1).sum_le_tsum _ (fun i _=>hn.1 i)).trans hn.2.2
    have he: Summable d := summable_of_sum_le hd ht
    exact ⟨hd,he,he.tsum_le_of_sum_le ht⟩
variable {I J:Type}{f:ℕ→Row I J}{b:ℕ→ℝ}
def terminalR (f:ℕ→Row I J): Row I J:=fun i j v=> aura fun n=> f n i j v
lemma Winbound {f:Cover→ℝ}(hp:Width η C f)(h:0≤η)(v:Cover) : |f v|≤ C:= ((hp.unweighted h).2.1.le_tsum v fun _ _=>norm_nonneg _).trans (hp.unweighted h).2.2
lemma row_aura (h:0≤η)(he:Ends b 0)(hp:∀ᶠ n in atTop,∀ m,n≤m→(minusRows (f n) (f m)).strip η (b n)) : ∀ i j v, Ends (fun n=> f n i j v) (terminalR f i j v):=fun i j v=> aura_pays _ b he (hp.mono fun _ e m q=> Winbound (e m q i j) h v)
lemma row_shiver {U:Row I J}(he:∀ i j v,Ends (fun n=>f n i j v) (U i j v)){n:ℕ}(hp:∀ m,n≤m → (minusRows (f n) (f m)).strip η C) : (minusRows (f n) U).strip η C:=fun i j=> linger (f:=fun m v=> f n i j v-f m i j v) (fun v=> tendsto_const_nhds.sub (he i j v)) ((eventually_ge_atTop n).mono fun m h=>hp m h i j)
end YM.FormalBulk08.North
