import YM.FormalBulk08.Drift.Coe
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Drift
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff
variable {I J:Type*}{G:Gauge}{η C:ℝ}{σ:ℕ→ℝ}{X:Type}{K:KernelChoices}{W: Lab G K X}{E e r d D n:ℕ}{ρ:ChartRatio G}{o:Loc G 1}
lemma sarking {T: ℕ → Studio D→Tile (edgeL G) r}{V:Studio D→Tile (edgeL G) r}(h:Brass staticT o (fun _=>η) σ (fun _=>1) T (fun _=>V))(z:Studio D)(hs:0≤η)(hp:Ends σ 0)(he:∀ i,0≤σ i): Boone (fun n=>T n z) (V z):= by
    obtain ⟨C,c,k,U⟩:=brass_crisp h; refine ⟨fun v=>?_⟩; have hh:Faint staticT σ (fun n=>T n z v-V z v):= by
       refine ⟨_,c.times (soft_coin _ ‖z‖),fun i=>mul_nonneg (k i) (norm_nonneg _),fun i=>?_⟩; refine (cool (U i z) hs v).trans_eq ?_; ring
    have hz:= quietude hp he hh; convert hz.add_const (V z v) using 1
    · ext;exact (sub_add_cancel ..).symm
    rw [zero_add]
lemma mark_money {a: Loc G 1}{T S:ℕ→ Studio D→Tile (edgeL G) r}(F:Frame G d)(h:Brass staticT a (fun _=>η) σ (fun _=>1) T S)(i:Letter F)(hs:0<η)(p:Studio D): Pact staticT σ (fun x=> pearlJ F (T x p) (mint F i)) (fun x=> pearlJ F (S x p) (mint F i)):= by
    obtain ⟨A,hA,H⟩:= pearl_cost F a i r hs
    obtain ⟨C,c,k,W⟩:=Matched.left h; obtain ⟨B,b,u,Y⟩:=Matched.right h; obtain ⟨Z,z,v,X⟩:=brass_crisp h
    have hp {T:ℕ →Tile (edgeL G) r}{C:ℕ→ℝ}(h:Soft staticT C)(hp:∀ i, Knoxville (fame _) η (0,a) (T i) (C i*(1*‖p‖))): Soft staticT (fun x=>pearlJ F (T x) (mint F i)):= ((soft_coin staticT A).times (h.times (soft_coin staticT (1*‖p‖)))).below fun i=> (H _ _ (hp i)).trans (le_abs_self _)
    refine ⟨hp c (fun i=>W i p),hp b (fun i=>Y i p),_,(soft_coin staticT A).times (z.times (soft_coin staticT ‖p‖)),fun i=>mul_nonneg hA (mul_nonneg (v i) (norm_nonneg _)),fun x=>?_⟩
    have hx: pearlJ F (T x p-S x p) (mint F i)= pearlJ F (T x p) (mint F i)-pearlJ F (S x p) (mint F i):= by
       apply eq_sub_of_add_eq; rw [← chalk F _ _ (X x p) (Y x p) hs hs,sub_add_cancel]
    rw [Pi.sub_apply, ←hx];exact (H _ _ (X x p)).trans_eq (by ring)

lemma mana {T:ℕ→ Anthem D G}{V: Anthem D G}(F:Frame G d)(hp:∀ e≤ E,∀ r,Brass staticT o (fun _=>η) σ (fun _=>1) (fun i p=> T i p e r) (fun _ p=> V p e r))(hs:0<η)(j:Letter F): Priced staticT σ (fun i=> echo F (T i) j) (fun _=> echo F V j) E:= by
    intro e he; simp_rw [echoline]; apply pact_sums _; intro t _; by_cases ht:slots F j -t≤e
    · simp_rw [if_pos ht]; exact mark_money F (hp _ (by omega) _) j hs _
    simp_rw [if_neg ht];apply Pact.coin

lemma moors [Fintype I] (p: Side→Pap I)(q: Pap I)(a: I→Pap J)(N:ℕ→ℕ)
    (he : ∀ j≤ E,∀ᶠ n in atTop, ∀ l,N j<l→ rancho (p n) j l=0)
    (h : ∀ j≤ E,∀ r v,Tendsto (fun n=>rancho (p n) j r v) atTop (𝓝 (rancho q j r v))) (m)(hm:m≤E)(v:J→₀ℕ):
    Tendsto (fun n=>MvPolynomial.coeff v (coeff m (roam ℝ a (p n)))) atTop (𝓝 (MvPolynomial.coeff v (coeff m (roam ℝ a q)))) := by
    have hT (j) (hj:j≤ E)(l) (hl : N j<l): marble l (coeff j q)=0:= funext fun v=> tendsto_nhds_unique (h j hj l v) (tendsto_const_nhds.congr' ((he j hj).mono (fun _ hh=>congr_fun (hh l hl).symm v)))
    have hh (T:Pap I): MvPolynomial.coeff v (coeff m (roam ℝ a T))=∑ j∈Finset.range (m+1), MvPolynomial.coeff v (coeff m (insertAt ℝ a (coeff j T)*X^j)):=by unfold roam; rw [(Series.liquid _ _ m).apex,map_sum,MvPolynomial.coeff_sum]
    simp_rw [hh]; apply tendsto_finsetSum _; intro j hj; have hp:j≤E:=by rw [Finset.mem_range] at hj;omega
    exact trinket m j a v p q (N j) (he j hp) (hT j hp) (h j hp)
end YM.FormalBulk08.Drift
