import YM.FormalBulk08.Quire.Tons
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t D:ℕ}{X:Type} {ρ:ChartRatio G}

-- further strict savings. use prebuilt Priced
def yetmore (a:hue G)(P:Flight j t)(V:Lodge P.patch)(K:KernelChoices)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(Y:Anthem D G)(hL:2≤P.L.val)(d u e r:ℕ)(p:Studio D) : Tile (edgeL G) r:= icons P ρ V W h Y hL d u e r p + ∑ j∈Finset.range e,Wine.bill (bookH (epoch a P V K W ρ h)) (bookU (epoch a P V K W ρ h)) e j r • quick P V W Y ρ h hL d u p j r
lemma dawn_path (a:hue G)(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(Y:Anthem D G)(hL:2≤P.L.val)(d u e r:ℕ)(p:Studio D): migrates a P V K W ρ h hL d u Y p e r= blade P K V Y d e r hL p+ yetmore a P V K W ρ h Y hL d u e r p:= by
   let f:= epoch a P V K W ρ h; have he: Wine.bill (bookH f) (bookU f) e e r=1:= by unfold Wine.bill; rw [Nat.sub_self]; exact Fresh.mul ((book_fresh f).pow _) ((book_guard f).pow _)
   unfold migrates stir stamp; rw [Finset.sum_range_succ,he,one_smul,quickse,add_comm,add_assoc];rfl
-- Tender BMI
section
variable {J U:X→ℕ}{F:∀ i:X,Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{Z L:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g:X→ℝ}
variable {o:Loc G 1}{T S:X→ Anthem D G}{W Y:X→ Pot G}
-- gather prerequisites
structure Wells (τ: Time X)(F:∀ i:X,Flight (J i) (U i))(V:∀ i:X,Lodge (F i).patch)(H:∀ i,(F i).patch.Branches K G)(ρ:ChartRatio G)(a: hue G) (σ η δ : X→ℝ)(Z L:∀ i:X,Train (J i))(W Y:X→Pot G)(E:ℕ) : Prop where
   pay:Aster.Freight F V ρ K τ σ η E
   carts : Canvas F V H τ Z L η δ
   dpos: ∀ i,0≤δ i
   air : Soft τ (fun i=> ((F i).L.val:ℝ))
   pharmacy : LocalRatio ρ
   aV: ∀ i, Story (W i) (pink K.penalty (Z i))
   bV: ∀ i, Story (Y i) (pink K.penalty (L i))
   paid : ∀ e≤ E,∀ m, Totem τ (fun _=>fame _) σ δ (fun i=> W i e m) (fun i=> Y i e m)
   church : ∀ i:X,4 ≤ U i
   weight : Priced τ δ (fun i=> epoch a (graded F Z i) (V i) K (W i) ρ (H i)) (fun i=> epoch a (graded F L i) (V i) K (Y i) ρ (H i)) E
variable {a:hue G}
-- issue ρ in weight
lemma bottle (w:Wells τ F V H ρ a σ η δ Z L W Y E) (h:∀ x,0≤g x)(hL:∀ i:X,2≤(F i).L.val)(d u e r:ℕ)(he:e≤E)(hp:∀ j m, precede e r j m→ Brass τ o σ δ g (fun i p=>T i p j m) (fun i p=> S i p j m)): Brass τ o η δ g (fun i p=> yetmore a (graded F Z i) (V i) K (W i) ρ (H i) (T i) (hL i) d u e r p) (fun i p=> yetmore a (graded F L i) (V i) K (Y i) ρ (H i) (S i) (hL i) d u e r p) := by
    have ht i := (w.aV i).toVivid; have hz i:= (w.bV i).toVivid; have hd:= w.pay
    have hf i : Fresh (epoch a (graded F Z i) (V i) K (W i) ρ (H i)) := (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1
    have hv i: Fresh (epoch a (graded F L i) (V i) K (Y i) ρ (H i)) := (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.bV i) K.penalty_pos (w.church i)).1
    obtain ⟨HA,Hb⟩:=w.weight.goods hf hv
    have hh j m (hj:j ≤ E) (hp:∀ i k, precede j m i k → Brass τ o σ δ g (fun x p=>T x p i k) (fun x p=>S x p i k)) := icon_rush hd w.carts w.pharmacy w.dpos h hL w.air ht hz w.paid u j m d hj hp
    unfold Brass yetmore; apply Matched.plus (hh e r he hp); apply matched_sums _;intro j hj; rw [Finset.mem_range] at hj
    apply Matched.amp _ (HA.income Hb _ _ r (by omega)); simp_rw [quickse]; have hk:=hp j r (Or.inl hj); exact Matched.plus (blade_pays w.pay w.carts w.dpos h hL w.air j r d hk) (hh j r (hj.le.trans he) (fun i k hi=> hp i k (by unfold precede at *;omega)))
-- mock indexing
lemma Wells.left (w:Wells τ F V H ρ a σ η δ Z L W Y E): Wells τ F V H ρ a σ η δ Z Z W W E:= ⟨w.pay,w.carts.left.mock,w.dpos,w.air,w.pharmacy,w.aV,w.aV,fun e he m=> Totem.constant (w.paid e he m).left,w.church,fun i hi=>Pact.constant (w.weight i hi).left⟩
lemma Wells.right (w:Wells τ F V H ρ a σ η δ Z L W Y E): Wells τ F V H ρ a σ η δ L L Y Y E:= ⟨w.pay,w.carts.right.mock,w.dpos,w.air,w.pharmacy,w.bV,w.bV,fun e he m=> Totem.constant (w.paid e he m).right,w.church,fun i hi=>Pact.constant (w.weight i hi).right⟩
lemma wells_income (w:Wells τ F V H ρ a σ η δ Z Z W W E)(h:∀ x,0≤g x)(hL:∀ i:X,2≤(F i).L.val)(d u e r:ℕ)(he:e≤E)(hp:∀ j m,precede e r j m→ Tender τ o σ g (fun i p=>T i p j m)): Tender τ o η g (fun i p=> yetmore a (graded F Z i) (V i) K (W i) ρ (H i) (T i) (hL i) d u e r p):= Matched.left (bottle w h hL d u e r he (fun j m hz=> Matched.constant (T:=_) (hp j m hz)))
lemma full_income (w:Wells τ F V H ρ a σ η δ Z L W Y E)(h:∀ x,0≤g x)(hL:∀ i:X,2≤(F i).L.val)(d u e r:ℕ)(he:e≤E)(hp:∀ j m,precede e r j m→ Brass τ o σ δ g (fun i p=>T i p j m) (fun i p=> S i p j m))(hr: Brass τ o σ δ g (fun i p=> T i p e r) (fun i p=> S i p e r)) : Brass τ o η δ g (fun i p=> migrates a (graded F Z i) (V i) K (W i) ρ (H i) (hL i) d u (T i) p e r) (fun i p=> migrates a (graded F L i) (V i) K (Y i) ρ (H i) (hL i) d u (S i) p e r) := by
    simp_rw [dawn_path]; exact Matched.plus (blade_pays w.pay w.carts w.dpos h hL w.air e r d hr) (bottle w h hL d u e r he hp)
end
end YM.FormalBulk08.Quire
