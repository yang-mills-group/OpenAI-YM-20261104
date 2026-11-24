import YM.FormalBulk08.Spruce.Fir
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H: Hol G}
variable {ρ:ChartRatio G}{o: Loc G 1}{Y: X→ Anthem D G}{g:X→ℝ}
variable (q:Quota F H W o D E R) (u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hl:l≤R)
-- R≤cap. full tower of projection-null packets; define WITH removal top so starts from general


def ledge (D :ℕ)(ρ:ChartRatio G)(W:Lab G K X)(x:X)(N i d l:ℕ)(a:hue G) := migrates (D:=D) a (destination (W.V x) N i) (W.wood x i) K (Lab.saga ρ a W x N (i+1)) ρ (W.toEmpire.bill x i) (growL _ _) d l
variable (l)
-- top step Y maybe input varying height p; q gates do not use exact paths.
def resumeS (x:X)(Y: Anthem D G) : ℕ → ℕ → Anthem D G
   | 0, i=> canopy F (bornY ρ W a F T q.horizon x (P.N x) i) Y
   | n+1,i=> canopy F (bornY ρ W a F T q.horizon x (P.N x) i) (ledge D ρ W x (P.N x) i d l a (resumeS x Y n (i+1)))
variable (ρ)
def wave (x:Deck C)(Y:X→Anthem D G) := resumeS (T:=T) (ρ:=ρ) l q a P x.a (Y x.a) (C.N x.a-x.b) x.b
lemma wave_last (x:X) : wave (T:=T) l ρ q a C P (peak C x) Y = canopy F (tribal T q a (ρ:=ρ) P.N (peak C x)) (Y x):= by rw [wave,show C.N (peak C x).a-(peak C x).b=0 from Nat.sub_self _, resumeS]
lemma waved (x:Turn C): wave (T:=T) l ρ q a C P x.bed Y= canopy F (tribal T q a (ρ:=ρ) P.N x.bed) (ledge D ρ W x.a (P.N x.a) x.b d l a (wave (T:=T) l ρ q a C P x.ups Y)) := by
   unfold wave at *;rw [show C.N x.bed.a-x.bed.b=C.N x.ups.a-x.ups.b+1 from ?_,resumeS]; rfl
   change C.N x.a-x.b=C.N x.a-(x.b+1)+1;have :=x.head;omega
-- cost requirements independently top. Qual and Clef
variable {ρ l}
include u hp h hs ht hb
lemma confidential (hy:∀ i,Clef o (Y i) l)(hw:∀ i,Qual (Y i) o E (W.eagle (peak C i))) (i:Deck C):
   let T':= wave (T:=T) l ρ q a C P i Y; Clef o T' l ∧ Qual T' o E (W.eagle i) ∧ echo F T'=0:= by
   let Z(x: Deck C):= tribal T q a (ρ:=ρ) P.N x; have hz(x): Court o F (Z x) := birth a h q hs ht hb x.a x.b (P.N x.a) x.zone (x.cap.trans (hp _)); have he x k:Qual (Z x k) o E (W.eagle x):= qualitative q u P h hs a (Lab.raiseD C P hp x) k
   let U x:= wave (T:=T) l ρ q a C P x Y
   have H1(x:X)(m)(hx:W.neck x≤ m)(hr:m≤ C.N x): let z: Deck C:=⟨⟨x,m,hx⟩,hr⟩; Clef o (U z) l ∧ Qual (U z) o E (W.width x m) ∧ echo F (U z)=0 := by
       induction hr using Nat.decreasingInduction with
       | self=> intro z; have ht:= canopy_nav (B:=F) (hz (peak C x)) (hy x); change Clef o (wave _ _ _ _ C _ (peak C x) Y) _ ∧ Qual (wave _ _ _ _ C _ (peak C x) Y) _ _ _ ∧ echo _ (wave _ _ _ _ C _ (peak C x) Y)=_; rw [wave_last];exact ⟨ht.1,qualCan (Z (peak C x)) _ _ (he _ ) (hw _), ht.2⟩
       | of_succ i hi IH=>
          intro z; let k: Turn C:=⟨⟨x,i,hx⟩,hi⟩; obtain ⟨hV,hQ,hU⟩:= IH (hx.trans (Nat.le_succ _));
          let M := ledge D ρ W x (P.N x) i d l a (U k.ups)
          have h': U z=canopy F (Z z) M := waved l ρ q a C P k
          obtain Ht:= budge C P P hp (fun _=>le_rfl) u h a hs;let R:= graded W.liftF (W.trail P.N) k
          have hQ':= migrate_w (P:=R) (V:=W.liftU k) a (W.liftH k) (scooped C k) d (show Clef o (U k.ups) l from hV) (Ht.aV k) (Ht.church k) h le_rfl; obtain ⟨hu,V⟩:= canopy_nav (hz z) hQ'; rw [h']; refine ⟨hu,qualCan _ _ _ (he _) ?_,V⟩
          obtain ⟨C,c,u,P⟩:= Ht.carts.left.swirl; obtain ⟨A,v,e,X⟩:= Ht.carts.left.rays; exact migrate_qual R _ _ _ _ _ h (Ht.church k) (Ht.pay.input k) (Ht.pay.output k) (Ht.pay.coverage k) _ (Ht.aV k) E (fun i he r=> by obtain ⟨C,c,h⟩:= (Ht.paid i he r).left; exact ⟨_,h k⟩) (P k) (X k) (u k) (e k) _ _ _ hQ
   exact H1 i.a i.b i.zone i.cap
end YM.FormalBulk08.Spruce
