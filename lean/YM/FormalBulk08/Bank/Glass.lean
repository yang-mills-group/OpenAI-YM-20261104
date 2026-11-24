import YM.FormalBulk08.Bank.Fall

/-! Through each FINITE order, admitting separate widths. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {V I : Type*} {J : Type*}
lemma bonded_match {q:V→V→ℝ} {p t s u : Waves V} {e r n E} (h : e ≤ E) (H : ∀ i≤n,∀ b≤E,p i b=t i b) (S : ∀ i≤n,∀ b≤E,s i b=u i b) : brawl q p s n e r=brawl q t u n e r := by
   unfold brawl; refine Finset.sum_congr rfl fun a ha=> Finset.sum_congr rfl fun b hb=> ?_; simp_rw [Finset.mem_antidiagonal] at hb ha; rw [H _ (by omega) _ (by omega),S _ (by omega) _ (by omega)]
lemma through_swim (q : V→V→ℝ) (p t : OrbitV V) (n E) (ht : ∀ b≤E,p b=t b) : ∀ b≤E, swim q p n b=swim q t n b := by
   induction n using Nat.strong_induction_on with
   | _ n ih=>
       intro b hb; cases n with
       | zero=> rw [swim_first,swim_first]; exact ht b hb
       | succ n=>funext r; rw [swim_succ,swim_succ,ih _ (by omega) b hb,bonded_match hb (fun i hi=>ih i (by omega)) (fun i hi=> ih i (by omega))]
-- variants
lemma kith_minus {η} {r : ℕ} {T : Tile (Biglot I) r} {U : Tile (Biglot I) r} {M P : (n:Side) → Tile (Tor n I) r} (h : Kith η T M) (ht : Kith η U P) : Kith η (T-U) (fun n=> M n-P n):= by
   obtain ⟨h,B,H⟩:=h; obtain ⟨ht,A,hh⟩:=ht; exact ⟨fun v=>(h v).sub (ht v), B+A,(H.and hh).mono fun _ h=> h.1.sub h.2⟩

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (T : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G) (h : P.patch.Branches K G) (k : (n:Side)→(primary P.patch K n).Choices)
lemma kith_start (hp : Vivid W) (hr : LocalRatio ρ) {η s C B : ℝ} (hs : 0<s) (hs':s≤P.L.val*η) (hC : 0≤C) (he : (Flight.duo K.penalty P).A0.strip s C)
   (e r : ℕ) (i : Fin r) (H : Bail (fame _) η (W e r) B) : Kith s (cola W ρ P T K e r) (fun n=>rancho (coffer W ρ P T h n (k n)) e r) := by
   unfold cola; simp_rw [posted W ρ P T h _ _ e r hs hC he]; by_cases hE:e=0
   · simp only [hE,↓reduceIte]; exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
   simp only [hE,↓reduceIte];
   have hz n:= filtered (primary P.patch K n) W ρ h hp hr T (k n) e r i;simp_rw [hz];clear hz; unfold primary;
   let X:= locating G K P T; obtain ⟨A,hA,ht⟩:= Lodge.bothPay G K T _ hs; have hX : X.strip s (A*C):=(ht _ _ hC he).1
   apply water_pearl (zealandPay K P T hX) _ i hs (le_trans zero_le_one (le_max_left ..)); unfold ouzo altitude atlas
   obtain ⟨B,hB⟩:= TO_bail G e r s P.patch K; obtain ⟨R,hR⟩:= WO_bail G e r s T ρ
   have hh:= water_pearl (M:= winging (Rim G P.patch) (Loc G 1)) (wing_strip _) (stable hs.le (packed_up (hp.civil e r) _) (packet_bill P.L hs' hs.le H) i) i hs zero_le_one
   exact (water_pearl (pane_pay T s) (kith_minus hh (stable hs.le (TO_up G P.patch K e r) hB i)) i hs zero_le_one).add (stable hs.le (WO_up G T ρ e r) hR i)
lemma demanded_finite (hp : Story W (pink K.penalty P.wing)) (E : ℕ): ∃ η : ℝ,0<η ∧ ∀ e≤E,∀ r,∃ C, Bail (fame _) η (W e r) C := by
   let S:= Fin (E+1) × Fin (E+3)
   choose s C hs H using fun i:S=>hp.fare i.1.val i.2.val
   obtain ⟨v,-,hv⟩:= Finset.exists_min_image Finset.univ s ⟨(0,0),Finset.mem_univ _⟩; refine ⟨s v,hs v,fun e he r=>?_⟩
   by_cases hx:r < E+3
   · let i:S := (⟨e,by omega⟩,⟨r,hx⟩); exact ⟨C i,(H i).shrink (hv i (Finset.mem_univ _))⟩
   have he' : W e r=0:=by by_contra ht;obtain ⟨h,h',-⟩:=hp.valence _ _ ht; omega
   rw [he'];exact ⟨_,bail_void ..⟩

def stopper (T:OrbitV V) (E : ℕ):OrbitV V:=fun e=> if e≤E then T e else 0
lemma redskin {η s C B : ℝ} (hs : 0<s) (hC : 0≤C) (hs':s≤P.L.val*η) (he : (Flight.duo K.penalty P).A0.strip s C) (hB : 0≤B) (hz : (gamma G K P T h).strip s B)
   (hp : Vivid W) (hr : LocalRatio ρ) (n e r : ℕ) (i : Fin r) (H : ∀ l≤e,∀ r, ∃ C, Bail (fame _) η (W l r) C) : Kith s (magma P T W ρ h n e r) (fun b=> whirl P T W ρ h b (k b) n e r) := by
    let Z b:=rancho (coffer W ρ P T h b (k b)); let Y:= cola W ρ P T K
    have hv m l (hp' : 0<l) : Kith s (stopper Y e m l) (fun b=> stopper (Z b) e m l) := by
       unfold stopper; by_cases h':m≤e
       · obtain ⟨C',hc⟩:= H m h' l; simpa only [h', ↓reduceIte] using kith_start P T W ρ h k hp hr hs hs' hC he m l (⟨0,hp'⟩ : Fin l) hc
       simp_rw [if_neg h']; exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void ..⟩
    let q:= rayshot P T h; have ht:= kith_swim (landing_row q (Row.rights _ _ (rayStrip P T h hB hz) hs.le)) _ hs (.of_forall (ray_grated P T h hs.le hB hz)) (ray_flip P T h) hv n e r (Nat.pos_of_ne_zero (by intro h; have :=i.isLt;omega))
    rw [through_swim (lands q) (stopper Y e) Y n e (fun j hj=> if_pos hj) e le_rfl] at ht
    have hh b : swim (q.acts b) (stopper (Z b) e) n e=whirl P T W ρ h b (k b) n e := through_swim _ _ _ _ e (fun j hj=> show stopper (Z b) e j=Z b j from if_pos hj) e le_rfl
    simp_rw [hh] at ht; exact ht
end YM.FormalBulk08.Bank
