import YM.FormalBulk08.Elm.Trunk
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Elm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X I:Type}{E e R d D m n l r:ℕ}{θ:ℝ}{o:Loc G 1}{ρ:ChartRatio G}
lemma brass_fold {τ:Time X}{s:Time I}{T S:X→ Studio D→Tile (edgeL G) r}{σ δ:X→ℝ}{g:I→ℝ}(p:I→ X)(hp:Soft s (fun i=>τ.day (p i)))(h:Brass τ o σ δ (fun _=>1) T S)(ht:∀ i,δ (p i) ≤ g i): Brass s o (σ ∘p) g (fun _=>1) (fun i=> T (p i)) (fun i=> S (p i)):= by
   have hh:=tenderLift (p:=p) hp (brass_cr T S h); refine ⟨tenderLift hp (show Tender _ _ _ (fun _=>1) _ from h.1), tenderLift hp (show Tender _ _ _ (fun _=>1) _ from h.2),?_⟩ -- implicit F? change
   apply Bear.below hh; intro i v; rw [one_mul];exact mul_le_mul_of_nonneg_right (ht i) (norm_nonneg _)
lemma deg_out (P: Page X)(C:Pin P)(h:0≤θ)(i:Turn C): Degree θ i.bed ≤ Dove.bump θ i:= by
   change ratioR (P.mesh i.a) (C.N i.a) i.b θ ≤ ratioR (P.mesh i.a) (C.N i.a) (i.b+1) θ; unfold ratioR; gcongr
   all_goals first|exact h| exact (Schedule.a_pos ..).le|exact div_nonneg (Schedule.a_pos ..).le (Schedule.a_pos ..).le| exact Schedule.a_pos ..| exact StrictAnti.antitone ((P.mesh i.a).strictAnti) (Nat.le_succ _)

variable {W:Lab G K X}{F:Frame G d}{H: Hol G}{T:SectionData F} (hp:Quota F H W o D E R)(u:W.Use ρ E)(C C':Pin W.scrolls) (p:∀ x,C.N x≤C'.N x) (h: LocalRatio ρ) (hs:G.Simple) (ht:T.Sound H)(hb:Bid.pop T)(a:hue G)
include p u hp h hs ht hb
lemma last_quote (hr:d≤ R)(i:Letter F)(he:e≤ E)(m:ℕ): Tender (sage C) o W.eagle (fun _=>1) (fun x t=> tribal (ρ:=ρ) T hp a C'.N x i t e m):= tenderLift (p:=Lab.raiseD C C' p) (show Soft (sage C) _ from soft_day (sage C)) (rooted_quote hp u C' h hs ht hb a hr i he m)
lemma shoots (hr:d≤ R):∀ i:Letter F,∀ e r,e≤ E → r≤e+slots F i→Brass (sage C) o W.eagle (Degree targetPower) (fun _=>1) (fun x t=>tribal (ρ:=ρ) T hp a C.N x i t e r) (fun x t=> tribal (ρ:=ρ) T hp a C'.N x i t e r) := by
   let Z(x: Deck C):=tribal (ρ:=ρ) T hp a C.N x; let S(x:Deck C):=tribal (ρ:=ρ) T hp a C'.N x
   have hv(x:Deck C):Court o F (Z x):= birth a h hp hs ht hb _ _ _ x.zone x.cap
   have hx(x:Deck C):Court o F (S x):= birth a h hp hs ht hb _ _ _ x.zone (x.cap.trans (p _))
   refine avenues F E _ ?H; intro i j k he hk ih;
   have hA:=rooted_quote hp u C h hs ht hb a hr i he k;have hB:=last_quote hp u C C' p h hs ht hb a hr i he k
   refine ⟨hA,hB,?_⟩
   have hh z m n (hz:itinerary F i j k z m n): Brass (sage C) o W.eagle (Degree targetPower) (fun _=>1) (fun x t=> Z x z t m n) (fun x t=> S x z t m n) := by
       by_cases hy:n ≤ m+slots F z
       · exact ih z m n hz hy
       simp_rw [show ∀ x (t:Studio D), Z x z t m n=0 from fun x t=>by by_contra h; have he:=(hv x|>.officers z).fare.1 t m n h; unfold Yield at *; omega,show ∀ x (t:Studio D), S x z t m n=0 from fun x t=>by by_contra h; have he:=(hx x|>.officers z).fare.1 t m n h; unfold Yield at *;omega];apply mates_void
   let α:=targetPower
   have he' : α<1/2:= by norm_num [α,targetPower]
   have hX:=soft_day ((sage C).reach (peak C)); let M(x):= fun t=>Z x i t j k-S x i t j k
   have hu:= up_age C u.liable
   have hw:Tender (sage C) o W.eagle (Degree α) M:= by
       apply targe (P:=C) u.liable he' (by linarith) _ (tenderLift (p:=peak C) hX (show Tender (sage C) o W.eagle (fun _=>1) _ from Bear.minus hA hB))
       exact elliptic i H he hr hp.horizon (fun i:Turn C=> quota_fits hp i.toLeaf) hk (grasp u C C' p h hs a) (payroll_from C hp u C.N) (payroll_from C hp u C'.N) (scooped C) (fun i=>hv i.ups) (fun i=> hx i.ups) (fun i=>again hp C a i C.N le_rfl) (fun i=>again hp C a i C'.N (p _)) (fun i=> qualitative hp u C h hs a i.ups _) (fun i=>qualitative hp u C' h hs a (Lab.raiseD C C' p i.ups) _) (tenderLift (p:=Turn.ups) hu hB) (fun j m h=>brass_fold Turn.ups hu (hh i j m (offhand _ h)) (fun _=>le_rfl)) (fun x j m h=>brass_fold Turn.bed (down_age C) (hh x j m h) (deg_out _ C targetPower_pos.le))
   unfold Tender at hw; simp only [one_mul]; exact hw
lemma truss (hr:d≤ R) (i:Letter F)(he:e≤ E)(r): Brass (sage C) o W.eagle (Degree targetPower) (fun _=>1) (fun x t=>tribal (ρ:=ρ) T hp a C.N x i t e r) (fun x t=>tribal (ρ:=ρ) T hp a C'.N x i t e r) := by
   by_cases h':r ≤ e+slots F i;exact shoots hp u C C' p h hs ht hb a hr i e r he h'
   have hh(c: Deck C)(M:X→ℕ)(he:C.N c.a≤ M c.a)(v): tribal (ρ:=ρ) T hp a M c i v e r=0:= by by_contra hz; have he:= (birth a h hp hs ht hb _ _ _ c.zone (c.cap.trans he)).officers i|>.fare.1 v e r hz;unfold Yield at *;omega
   simp_rw [show ∀ x t,tribal (ρ:=ρ) T hp a C.N (x:Deck C) i t e r=0 from fun x v=> hh x C.N le_rfl v,show ∀ x t,tribal (ρ:=ρ) T hp a C'.N (x:Deck C) i t e r=0 from fun x t=>hh x C'.N (p _) t];exact mates_void ..
lemma bought (hr:d≤R)(i j: Letter F): Priced (Dove.tide C) (Dove.bump targetPower) (fun x=>bornM (T:=T) (W:=W) (ρ:=ρ) a hp.horizon x.a (C.N x.a) x.b i j) (fun x=>bornM (T:=T) (W:=W) (ρ:=ρ) a hp.horizon x.a (C'.N x.a) x.b i j) E:= by
    intro e he
    apply Clover.transfer (T:=fun z:Turn C=>tribal (ρ:=ρ) T hp a C.N z.ups) (S:=fun z:Turn C=>tribal (ρ:=ρ) T hp a C'.N z.ups) he j e i (Or.inr ⟨rfl,Nat.zero_le _⟩) hr (Nat.zero_le _) (grasp u C C' p h hs a) (payroll_from C hp u C.N) (payroll_from C hp u C'.N) (scooped C) (fun x=>birth a h hp hs ht hb _ _ _ x.ups.zone x.head) (fun x=> birth a h hp hs ht hb _ _ _ x.ups.zone (x.head.trans_le (p _))) (fun i=> qualitative hp u C h hs a i.ups j) (fun i=>qualitative hp u C' h hs a (Lab.raiseD C C' p i.ups) j) (tenderLift (p:=Turn.ups) (up_age C u.liable) (last_quote hp u C C' p h hs ht hb _ hr j he 0)) (fun i k hh=> brass_fold Turn.ups (up_age C u.liable) (Elm.truss hp u C C' p h hs ht hb a hr j (show i≤E by unfold precede at hh;omega) k) (fun _=>le_rfl))
end YM.FormalBulk08.Elm
