import YM.FormalBulk08.Tundra.Firm

/-! Cutoff GDP for D and first step emissions. Captured stock may be subject to
just these polynomial bounds. Require model-phase as defined on same horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Dove Castor North Spruce Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I:Type}{E m l e r u D R d:ℕ}{o:Loc G 1}{W:Lab G K X}{F:Frame G d}{T:SectionData F}{H:Hol G}{ρ:ChartRatio G}
variable {g δ:X→ℝ}{τ:Time X}{Y Z:X→Anthem D G}{θ:ℝ}
lemma muscle (hw:∀ e≤E,∀ r, Blizzard u τ o δ g (fun x p=>Y x p e r) (fun x p=>Z x p e r))(h:d*d≤u)(i:Letter F)(j:ℕ)(hv:j≤E): Calm τ δ g (fun x=>coeff j (echo F (Y x) i)) (fun x=>coeff j (echo F (Z x) i)):= by
    refine ⟨tier_c (T:=Y) (fun i he r=>(hw i he r).1) h i hv,tier_c (T:=Z) (fun i he r=>(hw i he r).2) h i hv,?_⟩; refine (tier_c (T:=fun i=>Y i-Z i) (fun i he r=> remains (hw i he r)) h i hv).lower fun x=> le_of_eq ?_ ;apply congr_arg abs; simp_rw [echoline,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k hk;let r':= (j-(Pose.slots F i-k))
    by_cases hh: slots F i-k ≤ j; swap; · simp [hh]
    obtain ⟨A,a,V,H⟩:=(hw r' (le_trans (Nat.sub_le ..) hv) k).1; obtain ⟨B,b,P,W⟩:=(hw r' (le_trans (Nat.sub_le ..) hv) k).2; let v:= inside F i D; let S:=Y x v r' k;let T:= Z x v r' k; simp only [hh,↓reduceIte]; have hw':=runners_chalk F o (S-T) T (penn_sub (H x v) (W x v)) (W x v) (mint F i) ((Nat.mul_le_mul_left d (slotsFits F i)).trans h);change pearlJ F S _-pearlJ F T _= pearlJ F (S-T) _; rw [sub_add_cancel] at hw'; rw [hw',add_sub_cancel_right]
variable (q:Quota F H W o D E R)(p:Nesting F D E R u W o)(v:Lab.Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)
   (C P Q:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hz:∀ i,P.N i≤Q.N i)(hl:l≤R)(hR:d≤R)
   (hg:∀ i,0≤g i)(hy:∀ i,Clef o (Y i) l)(hx:∀ i,Clef o (Z i) l)
   (hw:∀ e≤ E,∀ r,Blizzard u ((sage C).reach (peak C)) o (hill C P hp) g (fun x p=>Y x p e r) (fun x p=> Z x p e r))
   (he:θ<1/2)
include q p v h a hs ht hb C P Q hp hz hR
lemma bookings (y:Letter F)(hn:e≤E) (r:ℕ) : Blizzard u (sage C) o (fun i=>hill C P hp i.a) (fun _=>1) (fun i z=>tribal (ρ:=ρ) T q a P.N i y z e r) (fun i z=> tribal (ρ:=ρ) T q a Q.N i y z e r):= stains (p.width.reach (fun i:Deck C=> i.toLeaf)) (fun _=>v.zero _) (fun _=>le_rfl) _ (show Brass _ _ _ _ _ _ _ from brass_fold (Lab.raiseD C P hp) (soft_day (sage C)) (Elm.truss q v P Q hz h hs ht hb a hR y hn r) (fun i=>bend_up C P hp i targetPower_pos.le))
include hl hg hy hx hw he
lemma dayshore :∀ e≤E,∀ r, Blizzard u (sage C) o (fun i=>hill C P hp i.a) (fun i=>g i.a * Degree θ i) (fun i z=>wave (T:=T) l ρ q a C P i Y z e r) (fun i z=>wave (T:=T) l ρ q a C Q i Z z e r) := by
   let X'(i:Deck C):= wave (T:=T) l ρ q a C P i Y;let P'(i:Deck C):=wave (T:=T) l ρ q a C Q i Z;let T' x:= tribal (T:=T) (ρ:=ρ) q a P.N (x:Deck C);let Y' x:= tribal (T:=T) (ρ:=ρ) q a Q.N (x:Deck C)
   let Z1:=hill C P hp;let b(x:X):=Z1 x*g x; have hb' x:0≤b x:=mul_nonneg (limb_pos ..) (hg x)
   have hl' i:=(hp i).trans (hz i)
   have H1 i j (hj:j≤ E) (r:ℕ): Blizzard u (sage C) o (fun i=>Z1 i.a) (fun _=>1) (fun x z=> T' x i z j r) (fun x z=>Y' x i z j r):= bookings q p v h a hs ht hb C P Q hp hz hR _ hj r
   have hT x:Court o F (T' x):= birth a h q hs ht hb _ _ _ x.zone (x.cap.trans (hp _)); have hZ x:Court o F (Y' x):=birth a h q hs ht hb _ _ _ x.zone (x.cap.trans (hl' _))
   have Ho e j r:=(hw e j r).1;have Hq e j r:=(hw e j r).2; have H0:θ≤1:= by linarith
   obtain HA:= yearly q v h a hs ht hb C P hp p hl hR hg hy Ho he H0; obtain HB:=yearly q v h a hs ht hb C Q hl' p hl hR hg hx Hq he H0
   have Hu:=classifier q v h a hs ht hb C P hp hy; have hz':=classifier q v h a hs ht hb C Q hl' hx
   let t (i:Deck C):= g i.a* Degree θ i
   let A e r:= Blizzard u (sage C) o (fun i=>Z1 i.a) t (fun i z=> X' i z e r) (fun i z=> P' i z e r)
   have hv i r (hi:l+i<r): A i r:= by unfold A;simp_rw [show ∀ x p,X' x p i r=0 from fun x p=>Classical.byContradiction fun h=> (not_lt_of_ge ((Hu x).1.fare.1 p i r h)) hi,show ∀ x p,P' x p i r=0 from fun x p=>Classical.byContradiction fun h=>(not_lt_of_ge ((hz' x).1.fare.1 p i r h)) hi];exact mates_void ..
   suffices ∀ i j,i≤E → j≤l+i → A i j from fun i hi r=>by by_cases hx:r≤l+i;exact this i r hi hx; exact hv i r (lt_of_not_ge hx)
   apply goyal; intro e r hE hr' ih; have hA j m (hp:precede e r j m) : A j m:= by by_cases hh:m≤l+j; exact ih j m hp hh; exact hv j m (lt_of_not_ge hh)
   let T1 (i:Deck C) (p):= X' i p e r-P' i p e r; have hk:Sigh u (sage C) o (fun i=> b i.a*Degree θ i) T1:= by
       apply veranda v.liable he H0 hb'
       · have ht:= (slide (T:=fun i=>X' (Turn.ups i)) (S:=fun i=>P' (Turn.ups i)) (budge C P Q hp hz v h a hs) (ticky C p P.N) (p.width.reach (fun i:Turn C=> i.toLeaf)) (fun i=>show 0≤ t i.ups from mul_nonneg (hg _) (ratioR_pos ..).le) (fun i=> hT i.bed) (fun i=>hZ i.bed) (fun i=>(Hu i.ups).1) (fun i=>(hz' i.ups).1) (fun i=>(Hu i.ups).2) (fun i=>(hz' i.ups).2) (show r≤R+E by omega) hE hl (scooped C) (fun j m hx=>ley Turn.ups (up_age C v.liable) (g:=t) (hA j m hx)) (lynx Turn.ups (up_age C v.liable) (HB _ hE r)) (fun y j hx=>ley Turn.bed (down_age C) (H1 y j (hx.trans hE) r))).1
         change Sugar _ _ _ _ (fun i=> Z1 i.a*g i.a*Dove.bump θ i) _ (fun i=>T1 i.ups) (fun i w=> X' i.bed w e r-P' i.bed w e r); simp_rw [show ∀ i:Turn C,X' i.bed=_ from fun i=>waved _ ρ q a C P i, show ∀ i:Turn C,P' i.bed=_ from fun i=>waved _ ρ q a C Q i,mul_assoc]; exact ht
       unfold T1; simp_rw [show ∀ x,X' (peak C x)=_ from fun x=>wave_last (T:=T) l ρ q a C P x,show ∀ x,P' (peak C x)=_ from fun x=>wave_last (T:=T) l ρ q a C Q x]
       have he(i:X)(p:Studio D): canopy F (T' (peak C i)) (Y i) p e r-canopy F (Y' (peak C i)) (Z i) p e r=Y i p e r-Z i p e r-(crease F (T' (peak C i)) (Y i) p e r- crease F (Y' (peak C i)) (Z i) p e r):= by unfold canopy;simp only [Pi.sub_apply];abel
       change Sigh _ _ _ _ (fun i z=> canopy F (T' _) _ _ _ _-canopy F (Y' _) (Z i) z e r);simp_rw [he]; refine Bear.minus (remains (hw e hE r)) (match_c e r (fun i=>hT (peak C i)) (fun i=>hZ (peak C i)) (fun i j hj=> ley (peak C) (soft_day _) (H1 i j (hj.trans hE) r)) (fun j k hj=>?_)); obtain Hc:=muscle hw p.plus k j (by omega); exact ⟨Hc.aF,Hc.diff⟩
   refine b_join (T:=fun i p=> X' i p e r) (S:=fun i p=>P' i p e r) (HA _ hE r) (HB _ hE r) ?_; convert hk using 1; ext x; exact (mul_assoc ..).symm
lemma fullTime : ∀ e≤E,∀ r,Blizzard u (Dove.tide C) o (fun i=> hill C P hp i.a) (fun i=>g i.a*Dove.bump θ i) (fun i z=> turf (T:=T) l ρ q a C P i Y z e r) (fun i z=> turf (T:=T) l ρ q a C Q i Z z e r):= by
   have Ht:= dayshore q p v h a hs ht hb C P Q hp hz hl hR hg hy hx hw he; have H(i:Turn C):0 ≤ g i.a*Dove.bump θ i:= mul_nonneg (hg _) (ratioR_pos ..).le;have Hv e (h:e≤E) r:= ley Turn.ups (up_age C v.liable) (Ht e h r)
   intro e He r
   exact whole (F:=W.liftF) (P:=W.liftU) (H:=W.liftH) (T:=fun i=>wave (T:=T) l ρ q a C P i.ups Y) (S:=fun i=>wave (T:=T) l ρ q a C Q i.ups Z) (budge C P Q hp hz v h a hs) (p.width.reach (fun i:Turn C=> i.toLeaf)) (scooped C) H He (fun j m hx=>Hv j (by unfold precede at *;omega) m) (Hv e He r) d l
lemma wages (i:Letter F)(n:ℕ)(hn:n≤E): Calm (Dove.tide C) (fun i=> hill C P hp i.a) (fun i=>g i.a*Dove.bump θ i) (fun j=>coeff n (feed (T:=T) l ρ q a C P j Y i ())) (fun j=>coeff n (feed (T:=T) l ρ q a C Q j Z i ())):= muscle (Y:=fun x=>turf (T:=T) l ρ q a C P x Y) (Z:=fun x=>turf (T:=T) l ρ q a C Q x Z) (fullTime q p v h a hs ht hb C P Q hp hz hl hR hg hy hx hw he) p.plus i n hn
end YM.FormalBulk08.Tundra
