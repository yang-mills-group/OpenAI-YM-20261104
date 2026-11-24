import YM.FormalBulk08.Elm.Twig
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Elm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E e R d D m n l r:ℕ}{o:Loc G 1}{ρ:ChartRatio G}
variable {W:Lab G K X}{F:Frame G d}{H: Hol G}{T:SectionData F} (hp:Quota F H W o D E R)(u:W.Use ρ E)(C C':Pin W.scrolls) (p:∀ x,C.N x≤C'.N x) (h: LocalRatio ρ) (hs:G.Simple) (ht:T.Sound H)(hb:Bid.pop T)(a:hue G)

variable (T)
-- fields on P cuts. implicit pin
abbrev tribal {C: Pin W.scrolls}(M:X→ℕ)(i:Deck C): Roof.Plaza F D := bornY ρ W a F T hp.horizon i.a (M i.a) i.b -- ρ implicit
variable {T}
lemma again (x:Turn C)(M:X→ℕ)(he:C.N x.a ≤ M x.a): tribal (ρ:=ρ) T hp a M x.bed= avenue F ρ a (graded W.liftF (W.trail M) x) (W.liftU x) (W.liftH x) (growL _ _) (Lab.instory ρ a W M x.ups) (tribal (ρ:=ρ) T hp a M x.ups):= born_walk a hp _ _ _ (x.head.trans_le he)
include u
lemma canopy_budget (x:Letter F)(i m :ℕ): Tender ((sage C).reach (peak C)) o (fun j=> W.eagle (peak C j)) (fun _=>1) (fun j p=> tribal (ρ:=ρ) T hp a C.N (peak C j) x p i m):= by
    obtain ⟨B,b,H⟩:= sectionQual F T hp.horizon x o i 1 i le_rfl m; refine ⟨_, soft_coin _ B,fun _=>b,fun j p=>?_⟩; change Knoxville (fame _) (W.width j (C.N j)) (0,o) (bornY _ W a F _ _ j (C.N j) (C.N j) x p i m) (B*(1*‖p‖))
    rw [went_top a hp,one_mul]; exact penn_shrink (H p) ((u.cost (peak C j).toLeaf).trans (window_le ..))
omit u
lemma young_floor {τ:Time X}{g η:X→ℝ} {T:X→ Plaza F D}(hx:∀ i,Court o F (T i))(x:Letter F)(p e:ℕ)(hp:e+Pose.slots F x<p): Tender τ o η g (fun i t=>T i x t e p):= by simp_rw [show ∀ i (t:Studio D), T i x t e p=0 from fun i t=> by by_contra hh; exact (not_lt_of_ge ((hx i|>.officers x).fare.1 t e p hh)) (by omega)]; exact bear_void ..
lemma scooped (x:Turn C):2≤(W.liftF x).L.val:= growL _ _
include u h hs ht hb
lemma escaped (hr:d≤R) : ∀ i:Letter F,∀ j k:ℕ,j≤E→ k≤ j+slots F i→Tender (sage C) o W.eagle (fun _=>1) (fun x p=> tribal (ρ:=ρ) T hp a C.N x i p j k):= by
    let Y:= tribal (ρ:=ρ) T hp a C.N (C:=C)
    have hv(z: Deck C):Court o F (Y z):= birth _ h hp hs ht hb _ _ _ z.zone z.cap
    apply avenues; intro x j k hj hk ih
    have hh (i:Letter F)(m n:ℕ)(hx:itinerary F x j k i m n): Tender (sage C) o W.eagle (fun _=>1) (fun z p=>Y z i p m n):=by
        by_cases h:n≤ m+slots F i
        · exact ih i m n hx h
        exact young_floor hv i n m (lt_of_not_ge h)
    have hU:=up_age C u.liable
    refine Elm.stip u.liable (θ:=1/2) (by positivity) ?_ (canopy_budget (T:=T) hp u C a x j k)
    exact realize_volume x H hj hr hp.horizon (fun i:Turn C=>quota_fits hp i.toLeaf) (grasp u C C (fun _=>le_rfl) h hs a) (payroll_from C hp u C.N) (scooped C) (fun i=>hv i.ups) (fun i=> qualitative hp u C h hs a i.ups x) (fun i=> again (T:=T) hp C a i C.N le_rfl) hk (fun j m h=> tenderLift (p:=Turn.ups) hU (hh x j m (offhand x h))) (fun i j k hi=>tenderLift (p:=Turn.bed) (down_age C) (hh i j k hi))
lemma rooted_quote (hr:d≤R)(i:Letter F)(he:e≤ E)(m:ℕ): Tender (sage C) o W.eagle (fun _=>1) (fun x p=>tribal (ρ:=ρ) T hp a C.N x i p e m):= by
   by_cases ht:m≤ e+slots F i
   · exact escaped hp u C h hs ‹T.Sound H› hb _ hr i e m he ht
   exact young_floor (fun i:Deck C=> birth a h hp hs ‹T.Sound H› hb _ _ _ i.zone i.cap) i m e (lt_of_not_ge ht)
end YM.FormalBulk08.Elm
