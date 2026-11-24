import YM.FormalBulk08.North.Veil

/-! Uniform holograms. Reader sees quantitative endpoint not just two-cut. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I:Type}{G:Gauge}{K:KernelChoices}{E e r:ℕ}
variable {W:Lab G K I}{ρ:ChartRatio G}

def fare_n (u:Leaf W.scrolls) (i:ℕ):= ratioR (W.V u.a).S i u.b targetPower
lemma fare_fin (u:Leaf W.scrolls): Ends (fare_n u) 0:= repeat_foot _ _ _ targetPower_pos
lemma fare_fin_lt (u:Leaf W.scrolls)(a:ℝ): Ends (fun n=> a*fare_n u n) 0:= by simpa using (fare_fin u).const_mul a
-- genuine head_0 no admitted extras used to define. index independent

def heir (a:hue G)(ρ:ChartRatio G)(W:Lab G K I)(x:I)(i:ℕ):Pot G:=fun e r=> terminalK fun N=> saga ρ a W x N i e r
variable (a:hue G)(hp:Use W ρ E)(h:LocalRatio ρ)(hs:G.Simple)
include hp h hs
lemma tenuous (he:e≤E)(r:ℕ):∃ B:Leaf W.scrolls→ℝ, Soft (chron _) B ∧ (∀ i,0≤B i) ∧ ∀ x:Leaf W.scrolls, ∀ N M,x.b≤N→N≤M → Bail (fame _) (W.windowD x) (saga ρ a W x.a N x.b e r) (B x) ∧ Bail (fame _) (W.windowD x) (saga ρ a W x.a N x.b e r-saga ρ a W x.a M x.b e r) (B x*fare_n x N) := by
    obtain ⟨⟨C,⟨A,p,u,X⟩,P⟩,hB,D,⟨K1,n,hu,Y⟩,b,Q⟩:= weigh_all hp h hs a he r
    let τ:=chron W.scrolls; refine ⟨fun i=> A*τ.day i^p + K1*τ.day i^n, ((soft_coin τ A).times ((soft_day τ).pows p)).plus ((soft_coin τ K1).times ((soft_day τ).pows n)),fun i=> add_nonneg (mul_nonneg u (pow_nonneg (τ.good _) _)) (mul_nonneg hu (pow_nonneg (τ.good _) _)),fun x N M h t=>?_⟩
    let y: meshPoint W:=⟨x,N,M,h,t⟩; exact ⟨(P y).mono (((le_abs_self _).trans (X y)).trans (le_add_of_nonneg_right (mul_nonneg hu (pow_nonneg (τ.good _) _)))), (Q y).mono (mul_le_mul_of_nonneg_right (((le_abs_self (D y)).trans (Y y)).trans (le_add_of_nonneg_left (mul_nonneg u (pow_nonneg (τ.good _) _)))) (ratioR_pos ..).le)⟩ -- parse
lemma crown (he:e≤E)(r)(x:Leaf W.scrolls): Boone (fun N=> saga ρ a W x.a N x.b e r) (heir a ρ W x.a x.b e r):= by
    cases r with
    | zero=>
       refine ⟨fun i=> aura_pays _ (fun _=>0) tendsto_const_nhds ?_⟩; filter_upwards [eventually_ge_atTop x.b] with n hn m hm
       have he N (hN:x.b≤N): saga ρ a W x.a N x.b e 0=0:= by
            by_contra U; have he:= ((genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) _ a h hs hN).valence _ _ U).1; omega
       simp only [he n hn,he m (hn.trans hm), Pi.zero_apply,sub_self, abs_zero,le_refl]
    | succ r=>
       obtain ⟨B,P,T,H⟩:= tenuous a hp h hs he (r+1); apply growthK (η:=W.windowD x) 0 _ _ ((eventually_ge_atTop x.b).mono (show ∀ m,x.b ≤ m → ∀ n,m ≤ n → Bail _ (W.windowD x) (saga ρ a W x.a m x.b e (r+1)-saga ρ a W x.a n x.b e (r+1)) (B x*fare_n x m) from fun i hi j hj=> (H x i j hi hj).2)); exacts [(hp.zero x).le, fare_fin_lt x (B x)]
lemma diadem (he:e≤ E)(r): ∃ B:Leaf W.scrolls→ℝ, Soft (chron _) B ∧ (∀ i,0≤B i) ∧ ∀ x:Leaf W.scrolls,Bail (fame _) (W.windowD x) (heir a ρ W x.a x.b e r) (B x) ∧ ∀ N,x.b≤N→ Bail (fame _) (W.windowD x) (saga ρ a W x.a N x.b e r-heir a ρ W x.a x.b e r) (B x*fare_n x N) := by
    obtain ⟨B,p,H,hK⟩:= tenuous a hp h hs he r
    have hx x:=North.crown a hp h hs he r x
    exact ⟨B,p,H,fun x=> ⟨limit_arr (R:=fame _) (T:=fun N=>saga ρ a W x.a N x.b e r) ((eventually_ge_atTop x.b).mono fun i hi=> (hK x i i hi le_rfl).1) (hx x).shares, fun N he=> lossK (T:=fun N=>saga ρ a W x.a N x.b e r) (U:=heir a ρ W x.a x.b e r) (R:=fame _) (n:=N) (hx x) (fun i hi=> (hK x N i he hi).2)⟩⟩ -- Σ
end YM.FormalBulk08.North
