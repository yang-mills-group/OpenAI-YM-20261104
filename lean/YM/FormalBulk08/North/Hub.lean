import YM.FormalBulk08.North.Carat

/-! Local Cash limit proofs via rate packets. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I J:Type}{G:Gauge}{K:KernelChoices}{E e r:ℕ}{W:Lab G K I}
-- constant day

def staticT : Time ℕ:=⟨fun _=>1,fun _=>le_rfl⟩
lemma static_p {f:ℕ→ℝ}(h:Soft staticT f): ∃ C:ℝ,∀ i, |f i| ≤ C:= by obtain ⟨C,n,u,H⟩:=h;use C;simpa only [staticT,one_pow,mul_one] using H
lemma sequenceF (f b:ℕ→ℝ)(he:Ends b 0)(hb:∀ i,|f i| ≤ b i) : Ends f 0:= squeeze_zero_norm (fun i=>hb i) he
lemma quietude {δ f:ℕ→ℝ}(he:Ends δ 0)(hp:∀ i,0≤δ i)(h:Faint staticT δ f):Ends f 0:= by
    obtain ⟨C,c,h,W⟩:=h; obtain ⟨B,u⟩:= static_p c; exact sequenceF f (fun i=> B*δ i) (by simpa using he.const_mul B) (fun i=>(W i).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (u _)) (hp i)))
lemma quietP {δ f:ℕ→ℝ}{C:ℝ}(he:Ends δ 0)(hp:∀ i,0≤δ i)(h:Pact staticT δ f (fun _=>C)): Ends f C:= by
    have hu:= quietude he hp h.blur; convert hu.add_const C using 1; · ext i; simp
    rw [zero_add]
lemma stillK {δ:ℕ→ℝ}{S:Reach I}{σ:ℝ}{T:ℕ→Tile I r}{V:Tile I r}(z:Fin r)(h0:0≤σ)(he:Ends δ 0)(hp:∀ i,0≤δ i)(h:Totem staticT (fun _=> S) (fun _=>σ) δ T (fun _=> V)):Boone T V:= by
    obtain ⟨C,c,p,H⟩:=h.nebula
    refine ⟨fun v=>?_⟩; have hh:Faint staticT δ (fun i=>T i v-V v):= ⟨_,c,p,fun i=> (H i).value h0 v z⟩; convert (quietude he hp hh).add_const (V v) using 1; · ext i; simp
    rw [zero_add]
lemma replace_peak {p q : ℕ → Tile I r}{T:Tile I r}(h:Boone p T)(he:∀ᶠ i in atTop,p i=q i): Boone q T:=⟨fun v=>(h.shares v).congr' (he.mono fun _ h=>congr_fun h _)⟩
lemma static_serene {p:ℕ→Tile I r}{T:Tile I r} (m:ℕ)(h:Boone (fun n=>p (n+m)) T) : Boone p T:=⟨fun v=>(tendsto_add_atTop_iff_nat m).mp (h.shares v)⟩
lemma boundP {p:ℕ→ Pot G}{U:Pot G}(h:∀ᶠ i in atTop,Vivid (p i))(hv:∀ e≤E,∀ r, Boone (fun i=>p i e r) (U e r)): Vivid (stopper U E) := by
    refine ⟨fun e r=>?_,fun e r=>?_,fun e r he=>?_⟩
    · unfold stopper;by_cases he:e≤E
      · rw [if_pos he]; intro x v; exact tendsto_nhds_unique (hv e he r|>.shares _) (((hv e he r).shares v).congr' (h.mono (fun i hi=> (hi.civil ..).symm)))
      rw [if_neg he];apply up_zero
    · unfold stopper;by_cases he:e≤E
      · rw [if_pos he];intro x s; exact tendsto_nhds_unique (hv e he r|>.shares _) (((hv e he r).shares x).congr' (h.mono (fun i hi=> (hi.agate ..).symm)))
      rw [if_neg he];apply agate_zero
    unfold stopper at he; split at he
    · rename_i hx; by_contra h'; apply he; ext v; apply tendsto_nhds_unique ((hv e hx r).shares v); refine tendsto_const_nhds.congr' ?_; filter_upwards [h] with i hi; have hZ: p i e r=0:= by by_contra hm; exact h' (hi.valence _ _ hm)
      rw [hZ]
    exact (he rfl).elim
lemma stopper_presents {T:Pot G}{n:Side}{j:ℕ}(h:j≤E):(PowerSeries.coeff j) (stone (stopper T E) n) =PowerSeries.coeff j (stone T n):= by -- change
    simp_rw [sow_coeff,sow,stopper,if_pos h]
lemma totem_hold {ρ:ChartRatio G}(a:hue G)(hp:Use W ρ E)(h:LocalRatio ρ)(hs:G.Simple)(x:Leaf W.scrolls)(hx:e≤ E) : Totem staticT (fun _=> fame _) (fun _=> W.windowD x) (fun n=> fare_n x (n+x.b)) (fun n=> saga ρ a W x.a (n+x.b) x.b e r) (fun _=>heir a ρ W x.a x.b e r):= by
   obtain ⟨C,c,P,U⟩:= tenuous a hp h hs hx r; obtain ⟨D,d,Q,V⟩:= diadem a hp h hs hx r; exact ⟨⟨_,soft_coin _ (C x),fun n=>(U x (n+x.b) _ (by omega) le_rfl).1⟩,⟨_,soft_coin _ _,fun _=>(V x).1⟩,_,soft_coin _ (D x),fun _=>Q x,fun n=>(V x).2 (n+x.b) (by omega)⟩
end YM.FormalBulk08.North
