import YM.FormalBulk08.Basin.Floe
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Firth
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
-- key on shift of the *coarse* root. Before reexpression.
variable {G:Gauge}{p q:Side}(x: Site p)
open Wilson Jets
open scoped Matrix.Norms.Frobenius
lemma routeStem (Z:Pap (wire G p))(h:Rite Z Z 1 0):Rite (resite x Z) Z 1 x:= by
   intro I y a b k ha hb hP hT hA hG hx; rw [label_w x a ha hP Z];
   apply h I (fun z=> a z ∘ Lotus.tint x) b k (by rw [ha];rfl) hb (contDiffAt_pi.mpr fun j=>contDiffAt_pi.mp hP (Lotus.tint x j)) hT hA hG; filter_upwards [hx] with z hz;rw [pull_id,zooms,hz]
lemma wageStem (Z Y:Pap (wire G p))(h:Rite Z Y 1 x): Z=resite x Y:= by
    let T:=fun a:Jets.Rays (wire G p)=> a ∘ Lotus.tint x
    have hx: ContDiffAt ℝ ω T 0:=contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    obtain H:= h (wire G p) (fun y=> y ∘ (id : wire G p→_)) T 1 rfl rfl (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) hx (fun _=>contDiffAt_const) ⟨1,rfl⟩ (.of_forall fun z=>by funext u; simp [T,zooms,Lattice.gauge]); rw [fit_translate, show T=(fun a: Jets.Rays (wire G p)=> a∘ Lotus.tint x) from rfl,fit_translate] at H; convert H using 1; ext1 n;simp
    rfl
lemma voyageW {T:Tile (Biglot V) r}{S:(p:Side)→Tile (Tor p V) r}(h:Light T S)(x:Cover): Light (carries x T) (fun p=>carries (wrap p x) (S p)):= by
    intro v; let V:= (Lotus.tint (-x)) ∘ v; apply (h V).congr'; refine .of_forall fun p=>?_ ; change S p _= S p _; congr 1; ext1 i; simp [V,←map_neg,drip_tint]
lemma resite_grade (T:Pap (wire G p))(x:Site p)(e r:ℕ): rancho (resite x T) e r=carries x (rancho T e r):= by
    have he: (Lotus.tint x (I:=Loc G 1)).symm= Lotus.tint (-x):= by ext i <;> simp [Lotus.tint]
    change rancho (joust (Lotus.tint x) T) e r=_; rw [joust_level,he]; rfl
variable {K:KernelChoices}{P:Flight j t}{L:Lodge P.patch}{h:P.patch.Branches K G}{W T:Pot G}
variable (a:hue G){ρ:ChartRatio G}(hs:LocalRatio ρ)(hp:Story W (pink K.penalty P.wing))(ht:4≤t)(hx:Ritual T m)
include hs hp ht hx a
lemma nibs (y:Cover): braise P L W (Kemp.work (P.patch.L.val • y) T) ρ h m= Kemp.work y (braise P L W T ρ h m):= by
    let Y:= Kemp.work (P.patch.L.val • y) T;let f(n:Side):= primary P.patch K n; let u(n):= Classical.choice (chooseable n _ (f n)); let S n:= tossed P ρ h L n (u n) (Mesa.stone W _)
    obtain ⟨s,C,hc,c,H,-⟩:= colors G K.penalty K.penalty_pos P.legal; have hC:∀ n:Side,Civic (Mesa.stone W n) := hp.civic
    let B p:=Kemp.banner m T p
    have hh(p): S p (Kemp.banner m Y _)= resite (wrap p y) (S p (B _)):= by
       apply wageStem; unfold Y;rw [seated _ _ _ _ hx.young hx.committees, show P.patch.L.val • y=(f p).ratio.count.val • y from rfl, ←(f p).ratio.embed_wrap]
       apply tossed_ward P ρ h L p (u p) (Mesa.stone W _) (stoned_main hc.le c.le (H P.wing).1 hp.toVivid hp.ink _) hs ht (hC _) 1 (wrap p y); exact routeStem _ _ (hx.esteem _)
    funext i r; let o:edgeL G:=(0,Exterior.coord 0,a); have hv := ((testified o P L W ρ h hp hs ht hx u i r).choose_spec.2).1; obtain ⟨z,-,Uw,-⟩:= testified o P L W _ h hp hs ht (from_R _ _ hx (P.L.val • y)) u i r; have hU n:S n (Kemp.banner m (Kemp.work (P.L.val • y) T) _)=resite (wrap n y) (S n (B _)):= hh n
    ext1 w; refine tendsto_nhds_unique (Uw w) (((voyageW hv y) w).congr' (.of_forall fun n=> ?_));dsimp only; rw [show tossed _ _ _ _ _ _ _ _= _ from hU n, resite_grade]
lemma winding (y:Cover): enterStep P L W a ρ h m (Kemp.work (P.patch.L.val • y) T) = Kemp.work y (enterStep P L W a ρ h m T):= by
   unfold enterStep; rw [nibs a hs hp ht hx]; ext i j v;simp [stamp, Kemp.work,Kemp.carries,jetty,Finset.sum_apply]
end YM.FormalBulk08.Firth
