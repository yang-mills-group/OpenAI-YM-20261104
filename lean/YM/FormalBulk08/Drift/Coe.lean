import YM.FormalBulk08.Elm.Forest
import YM.FormalBulk08.North.Nest

/-! Limit charts at every level. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Drift
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {X I : Type*}{G:Gauge}{η C :ℝ}{V:Reach X}{K:KernelChoices}{E e r m n d D R:ℕ}
lemma penny_limit {T:ℕ→Tile X r}{o:X}{S:Tile X r}(h:∀ᶠ i in atTop, Knoxville V η o (T i) C)(he:Boone T S): Knoxville V η o S C := by
    refine ⟨h.exists.choose_spec.1,?_⟩;rw [ENNReal.tsum_eq_iSup_sum,iSup_le_iff]; intro P
    have hv x : Ends (fun i=>penon V o η (T i) x) (penon V o η S x):= by
       let f(z:ℝ):= Gorge.shine η (wide V (Fin.cons o x:chain X (r+1)))*‖z‖ₑ; have hc:Continuous f:= by unfold f Gorge.shine; simp_rw [←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_norm)
       exact hc.continuousAt.tendsto.comp (he.shares x)
    apply le_of_tendsto (tendsto_finsetSum _ (fun i _=>hv i)); filter_upwards [h] with x hx; exact (ENNReal.sum_le_tsum _).trans hx.2
lemma cool {Y: Tile X r}{o:X}(h: Knoxville V η o Y C)(he:0≤η)(w):‖Y w‖≤ C:= (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (show 0≤η*herb V o w from mul_nonneg he (Nat.cast_nonneg _)))).trans (penn_chill _ h)
variable {X:Type}{W: Lab G K X}{ρ:ChartRatio G}{B:Frame G d}{H:Hol G}{T: SectionData B} {o:Loc G 1} {Z: Leaf W.scrolls}

def issue (W:Lab G K X)(ρ:ChartRatio G)(a:hue G)(F:Frame G d)(T:SectionData F)(h:d+1≤D)(i:X)(m:ℕ) : Roof.Plaza F D := fun x p e r=> terminalK (fun n=> Elm.bornY ρ W a F T h i n m x p e r)
variable (q:Quota B H W o D E R)(u:Use W ρ E)(h: LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)(he:e≤ E)(i : Letter B)
include h u q a hs ht hb hr he
lemma canoe (r:ℕ): ∃ C:Leaf W.scrolls→ℝ, Soft (chron W.scrolls) C ∧ (∀ i,0≤C i) ∧ ∀ x:Leaf W.scrolls,∀ N M,x.b≤N→ N≤M→ ∀ p:Studio D, Knoxville (fame _) (W.windowD x) (0,o) (bornY ρ W a B T q.horizon x.a N x.b i p e r) (C x*‖p‖) ∧ Knoxville (fame _) (W.windowD x) (0,o) (bornY ρ W a B T q.horizon x.a N x.b i p e r-bornY ρ W a B T q.horizon x.a M x.b i p e r) (C x*fare_n x N*‖p‖):= by
    obtain ⟨⟨C,⟨A,m,u',X⟩,b,H⟩,hb',D,⟨B',n,p,Y⟩,hv,P⟩:= expend q u h hs ht hb a hr he r i
    let τ:=chron W.scrolls; let U(x:Leaf W.scrolls):=A*τ.day x^m; let V(x:Leaf W.scrolls):=B'*τ.day x^n; have hu x:0≤U x:= mul_nonneg u' (pow_nonneg (τ.good _) _); have ht x:0≤V x:=mul_nonneg p (pow_nonneg (τ.good _) _)
    let T' x := U x+V x; refine ⟨T', ((soft_coin τ A).times ((soft_day τ).pows m)).plus ((soft_coin τ B').times ((soft_day τ).pows n)),fun x=> add_nonneg (hu x) (ht x),fun x N M hN hM p=>?_⟩
    let z:meshPoint W:=⟨x,N,M,hN,hM⟩; have H1:C z ≤ U x:= (le_abs_self _).trans (X z); have H2:D z≤ V x:= (le_abs_self _).trans (Y z)
    refine ⟨(H z p).mono ?_, (P z p).mono ?_⟩
    · simp only [one_mul];exact mul_le_mul_of_nonneg_right (H1.trans (le_add_of_nonneg_right (ht _))) (norm_nonneg _)
    simp only [one_mul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (H2.trans (le_add_of_nonneg_left (hu _))) (ratioR_pos ..).le) (norm_nonneg _)
lemma harbor (r:ℕ)(x:Leaf W.scrolls)(p:Studio D) : Boone (fun N=> bornY ρ W a B T q.horizon x.a N x.b i p e r) (issue W ρ a B T q.horizon x.a x.b i p e r):= by
    obtain ⟨C,c,k,P⟩:= canoe q u h a hs ht hb hr he i r; refine ⟨fun v=> aura_pays _ (fun n=>C x*fare_n x n*‖p‖) (by simpa using (fare_fin_lt x (C x)).mul_const ‖p‖) ((eventually_ge_atTop x.b).mono fun n hn m hm=>?_)⟩; exact cool (P x n m hn hm p).2 (u.zero x).le v
lemma skiff (r:ℕ):∃ C:Leaf W.scrolls→ℝ, Soft (chron W.scrolls) C ∧ (∀ i,0≤C i) ∧ ∀ x:Leaf W.scrolls,∀ p:Studio D, Knoxville (fame _) (W.windowD x) (0,o) (issue W ρ a B T q.horizon x.a x.b i p e r) (C x*‖p‖) ∧ ∀ N,x.b≤N→ Knoxville (fame _) (W.windowD x) (0,o) (bornY ρ W a B T q.horizon x.a N x.b i p e r-issue W ρ a B T q.horizon x.a x.b i p e r) (C x*fare_n x N*‖p‖):= by
    obtain ⟨C,c,k,P⟩:= canoe q u h a hs ht hb hr he i r; refine ⟨_,c,k,fun x p=> ?_⟩; have hp:= Drift.harbor q u h a hs ht hb hr he i r x p; refine ⟨penny_limit ((eventually_ge_atTop x.b).mono (fun j hj=> (P x j j hj le_rfl p).1)) hp, fun m hm=> penny_limit ((eventually_ge_atTop m).mono (fun j hj=> (P x m j hm hj p).2)) ⟨fun z=> tendsto_const_nhds.sub (hp.shares z)⟩⟩
lemma pantry_prices (r:ℕ)(x:Leaf W.scrolls):
    Brass staticT o (fun _=>W.windowD x) (fun i=>fare_n x (i+x.b)) (fun _=>1) (fun n p=> bornY ρ W a B T q.horizon x.a (n+x.b) x.b i p e r) (fun _ p=>issue W ρ a B T q.horizon x.a x.b i p e r):= by
    obtain ⟨C,c,k,P⟩:= canoe q u h a hs ht hb hr he i r; obtain ⟨V,v,b,U⟩:= skiff q u h a hs ht hb hr he i r
    refine ⟨⟨_,soft_coin _ (C x),fun _=> k x,fun i y=>?_⟩,⟨_,soft_coin _ (V x),fun _=> b x,fun i y=>?_⟩,_,soft_coin _ (V x),fun _=> b x,fun i y=>?_⟩
    · simp only [one_mul]; exact (P x (i+x.b) (i+x.b) (by omega) le_rfl y).1
    · simp only [one_mul];exact (U x y).1
    simp only [one_mul,←mul_assoc]; exact (U x y).2 _ (by omega)
end YM.FormalBulk08.Drift
