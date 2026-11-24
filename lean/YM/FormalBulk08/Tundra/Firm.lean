import YM.FormalBulk08.Tundra.Amble

/-! Solved rec, same Spruce models. A stronger initial moment demand may be chosen
by authorities for readout; no power of width lost on this trajectory. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Dove Castor North Spruce Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I:Type}{E m l e r u D R d:ℕ}{o:Loc G 1}{W:Lab G K X}{Z:Frame G d}
variable {τ:Time X}{g:X→ℝ}{S T:X→ Anthem D G}{P:SectionData Z}{H:Hol G}{ρ: ChartRatio G}
lemma tier_c (ht:∀ e ≤ E,∀ r, Wayfarer T e r u τ o g)(hp:d*d≤u)(i:Letter Z)(h:e ≤ E): Faint τ g (fun x=>coeff e (echo Z (T x) i)):= loser i hp (fun j hj k=>ht j (hj.le.trans h) k) (tilted (T:=fun x p=>T x p e (Pose.slots Z i)) i (ht e h (Pose.slots Z i)) hp)
variable (q:Quota Z H W o D E R)(v:Lab.Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple) (hz:P.Sound H)(hb: Bid.pop P)(C M:Pin W.scrolls)(hp:∀ i,C.N i≤M.N i)
    (p:Nesting Z D E R u W o) {θ:ℝ}
include v q h hs hz hb hp a
lemma classifier (hy:∀ i,Clef o (T i) l)(i:Deck C): Clef o (wave (T:=P) l ρ q a C M i T) l ∧ echo Z (wave (T:=P) l ρ q a C M i T)=0:= by
   let Y(x:Deck C):= tribal P q a (ρ:=ρ) M.N x; have hk(x): Court o Z (Y x):= birth a h q hs hz hb x.a x.b (M.N x.a) x.zone (x.cap.trans (hp _))
   let U x:=wave (T:=P) l ρ q a C M x T
   have H1(x:X)(m)(hx:W.neck x≤m)(hr:m≤C.N x):let z:Deck C:=⟨⟨x,m,hx⟩,hr⟩; Clef o (U z) l ∧ echo Z (U z)=0 := by
      induction hr using Nat.decreasingInduction with
      | self=>intro z; have ht:= canopy_nav (hk (peak C x)) (hy x); change Clef o (wave _ _ _ _ C _ (peak C x) T) _ ∧ echo _ (wave _ _ _ _ C _ (peak C x) T)=_;rw [wave_last]; exact ht
      | of_succ i hi IH=>
         intro z; let k: Turn C:=⟨⟨x,i,hx⟩,hi⟩; have he:= IH (hx.trans (Nat.le_succ _)); have hU:U z=canopy Z (Y z) (turf (T:=P) l ρ q a C M k T):= waved l ρ q a C M k; obtain ht:= budge C M M hp (fun _=>le_rfl) v h a hs;let R:=graded W.liftF (W.trail M.N) k
         rw [hU]; exact canopy_nav (hk z) (migrate_w (P:=R) a (W.liftH k) (scooped C k) d (show Clef o (U k.ups) l from he.1) (ht.aV k) (ht.church k) h le_rfl)
   exact H1 i.a i.b i.zone i.cap
include p
lemma yearly (hl:l≤R)(hr:d≤R)(hv:∀ i,0≤g i)(hy:∀ i,Clef o (S i) l)(hw:∀ e≤ E,∀ r, Wayfarer S e r u ((sage C).reach (peak C)) o g)(he:θ<1/2)(hh:θ ≤ 1):∀ e≤E,∀ r, Sigh u (sage C) o (fun i=>g i.a*Degree θ i) (fun i z=> wave (T:=P) l ρ q a C M i S z e r) := by
    let t x:= wave (T:=P) l ρ q a C M x S;let B x:= tribal (ρ:=ρ) P q a M.N (x:Deck C)
    have ht_ x: Court o Z (B x):= birth a h q hs hz hb _ _ _ x.zone (x.cap.trans (hp _)); obtain H:=budge C M M hp (fun _=>le_rfl) v h a hs
    have hK(x): Clef o (t x) l∧echo Z (t x)=0:=classifier q v h a hs hz hb C M hp hy x
    have ht:=p.width.reach (fun i:Turn C=> i.toLeaf); have hm(i:Letter Z)(j)(hx:j≤E)(r:ℕ): Sigh u (sage C) o (fun _=>1) (fun x z=>B x i z j r):= stain (p.width.reach (fun i:Deck C=> i.toLeaf)) (fun i=> v.zero _) (fun _=>le_rfl) u (last_quote q v C M hp h hs hz hb a hr i hx r)
    let U(k n:ℕ):Prop:= Wayfarer t k n u (sage C) o (fun i=>g i.a*Degree θ i); have hz' (k n:ℕ)(hp:l+k<n): U k n:= by
       unfold U
       unfold Wayfarer; simp_rw [show ∀ i p,t i p k n=0 from fun i p=>Classical.byContradiction fun h=> (not_lt_of_ge ((hK i).1.fare.1 p k n h)) hp]; exact bear_void ..
    suffices ∀ i j, i≤E → j≤ l+i→ U i j from fun i hi r=> by by_cases he:r≤ l+i;exact this _ _ hi he; exact hz' _ _ (lt_of_not_ge he)
    apply goyal; intro e r h' hp' ih; have hU (j m:ℕ)(h: precede e r j m):U j m:= by by_cases hh:m≤ l+j; exact ih j m h hh; exact hz' _ _ (lt_of_not_ge hh)
    apply veranda (T:=fun i w=>t i w e r) v.liable he hh hv
    · have hz(i:Turn C):0≤g i.a*Dove.bump θ i:=mul_nonneg (hv _) (ratioR_pos ..).le
      have H0:= (rail H (ticky C p M.N) ht hz (fun i=>(hK i.ups).1) (fun i=>(hK i.ups).2) h' (show r≤R+E by omega) hl (scooped C) (fun j m hh=> lynx Turn.ups (up_age C v.liable) (T:=fun i w=> t i w j m) (g:=fun i=>g i.a*Degree θ i) (hU j m hh)) (fun i=>ht_ i.bed) (fun k j hx=> lynx Turn.bed (down_age C) (hm k j (hx.trans h') r)) l).1
      simp_rw [show ∀ i:Turn C,t i.bed=_ from fun i=> waved (T:=P) (Y:=S) l ρ q a C M i]; exact H0
    simp_rw [show ∀ x,t (peak C x)=_ from fun x=> wave_last (T:=P) (Y:=S) l ρ q a C M x]; exact Bear.minus (hw e h' r) (aching_at _ _ (fun i=>ht_ (peak C i)) (fun k n hn=> lynx (peak C) (soft_day _) (hm k _ (hn.trans h') r)) (fun j k ht=> tier_c hw p.plus k (by omega)))
end YM.FormalBulk08.Tundra
