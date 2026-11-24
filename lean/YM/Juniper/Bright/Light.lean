import YM.Juniper.Bright.Run
/-!
 # Instantiate Warm lamp on high-order pure bouquets (any R)

 all V orientations carried. χ manifest but tread. Centers on old supports. Nobody
      assumes divided carrier for unstamped (Seed claim retains travel).
 Usage: need E unsplit slot exposure when not in Π via Destiny.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona
open Further.PhysicalPeriodLimitF933 Macrame Shelf Stellar
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f c' f' L : Side} {P:Teller G}
      {W μ x C C' s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n w:ℕ}
local notation "U"=> radiusB x
section exact
variable {S:StepData c f} {T:Tube G S} {R : Rep G f}
    (I: Cash W x μ L Q o C T R)

def firstPrice (n:ℕ): Finset (Mint.Music c f):= (Meadow.tuck n).filter fun i=> Mint.verse R.path i ≤ radiusB x -- doesn't include I
-- helper
lemma resource_preimage (b:Finset (Mint.Music c f)) (t:Molecule S) (he:t⊆Mint.hatch S b):∃ q⊆b,Mint.hatch S q=t:=by
   let q:= b.filter fun j=> Mint.disc S j∈ t
   refine ⟨q,filter_subset ..,?_⟩; ext i; constructor; · intro hi; obtain ⟨k,hk,rfl⟩:= mem_map.mp hi; exact (mem_filter.mp hk).2
   intro hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp (he hi); exact mem_map_of_mem _ (mem_filter.mpr ⟨hj,hi⟩)

def beam (S: StepData c f): Head S→ Site c := extend (Mint.disc S) (Mint.pace S) 0
lemma beam_pin (p : Mint.Music c f): beam S (Mint.disc S p) = Mint.pace S p:= (Mint.disc S).injective.extend_apply ..
def flora (n:ℕ): Shelf I (Mint.width Q.halo U U):= by
   let v:Finset (Mint.Music c f):= firstPrice (R:=R) (x:=x) n
   refine ⟨Mint.hatch S v,?_,beam S,?_,?_⟩
   · intro p hp; obtain ⟨q,-,hq⟩:= resource_preimage v p hp; rw [← hq, Mint.unrostered]
   all_goals
      intro p hp; obtain ⟨q,hq,rfl⟩:=mem_map.mp hp; rw [beam_pin]
      have h:= Mint.centered Q.halo U U (lt_of_lt_of_le (by norm_num) I.laws.data.room.sight.1) q S T R (show _ from (mem_filter.mp hq).2)
      first|exact h.1|exact h.2
lemma unfolded (a:Site c) (t:Mint.Music c f) (n k:ℕ) : Mint.disc S t∈(flora I n).Window k a ↔ t∈firstPrice (R:=R) (x:=x) n ∧ separation a (Mint.pace S t) ≤ terrace (Mint.width Q.halo U U) k:=by
   rw [Shelf.Window,mem_filter]; change _ ∈ (Mint.hatch _ _) ∧ beam S (Mint.disc S t) ∈ _ ↔ _; rw [Mint.hatch,Finset.mem_map',beam_pin, neighbors_mem]
lemma drafted (n:ℕ) (t:Mint.Music c f) : Mint.disc S t∈(flora I n).binders ↔ t∈ firstPrice (x:=x) (R:=R) n:= by change _ ∈ (firstPrice n).map _↔ _; exact Finset.mem_map' _
end exact
section lift
variable {g:Patch}{K:KernelChoices} {M:ℕ}{c f C₀ F:Side} {hs : f.val=c.val*g.L.val} {hh : F.val=C₀.val*g.L.val}
local notation "S"=> stepped K hs
local notation "Y"=> stepped K hh
variable {T:Tube G (stepped K hs)} {T': Tube G (stepped K hh)} {R: Rep G f} {R': Rep G F}
variable (hC:C₀.val=c.val*M) (he:2≤c.val)
local notation "V"=> Lace.project (h:=hs) (H:=hh) hC he
local notation "π"=> (V).low.cut
-- extend on HEAD enumerations
local notation "v'=>" => verse_down (V)
def trail : Head (stepped K hh)→ Head (stepped K hs) := Function.extend (Mint.disc Y) (Mint.disc S ∘ v'=> ) (fun _=> Classical.arbitrary _)
lemma trail_at (x:Mint.Music C₀ F): trail (K:=K) (hs:=hs) (hh:=hh) hC he (Mint.disc Y x)= Mint.disc S (v'=> x):= (Mint.disc Y).injective.extend_apply ..
variable (I':Cash W x μ L Q o C' T' R') (I:Cash W x μ L Q o C T R) (hp:R'.path=R.path) (a:Site C₀) (n k:ℕ)
local notation "B"=> Mint.width Q.halo (radiusB x) U
local notation "ζ"=> terrace B k
include hC he hp I I'
lemma chosen (x':Mint.Music C₀ F) : x' ∈ firstPrice (R:=R') (x:=x) n ↔ v'=> x' ∈ firstPrice (R:=R) (x:=x) n:=by
    rw [firstPrice, firstPrice]; simp only [mem_filter, Meadow.pocket]
    rw [Meadow.contempt hC he hp (I:=I) (I':=I') x'|>.1]; cases x' with
    |inl x=> rfl
    |inr x=> rcases x with x|x|x<;> rfl

def light (hc: 2*(ζ+B)<c.val): Lamp k (flora I' n) (flora I n) a (V).low.cut := by
   have hm:= Stellar.nest_mint (Q:=K) (h:=hs) (H:=hh) (hC:=hC) (he:=he)
   let Ω:=(flora I' n).Window k a; let F:=(flora I n).Window k (π a)
   let t : Head (stepped K hh)→Head (stepped K hs):= trail hC he
   have hy q (hq:q∈ Ω) : ∃ i,Mint.disc Y i=q:= by obtain ⟨i,h,rfl⟩:= mem_map.mp ((mem_filter.mp hq).1); exact ⟨i,rfl⟩
   have ht i:t (Mint.disc _ i)= Mint.disc S (v'=> i):= trail_at ..
   refine ⟨t,?_,?_, Meadow.garden hC a hc,?_⟩
   · refine le_antisymm ?_ ?_; swap
     · intro i hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp (mem_filter.mp hi).1; obtain ⟨q,h,hQ⟩:= hm.esc a j
       obtain ⟨hz,hp'⟩:= unfolded I (π a) j n k|>.1 hi
       have ht': Mint.disc Y q∈ Ω:= (unfolded ..).2 ⟨(chosen hC he I' I hp n q).2 (h.symm ▸ hz), hQ.trans_le hp'⟩; refine mem_image.mpr ⟨_,ht',?_⟩; rw [ht,h]
     intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; obtain ⟨j,rfl⟩:= hy _ hj
     rw [ht]; refine (unfolded ..).2 ?_; obtain ⟨hz,hQ⟩:= unfolded I' a j n k|>.1 hj
     refine ⟨(chosen hC he I' I hp n j).1 hz, ?_⟩; rw [← hm.footing]; exact (Deck.less ..).trans hQ
   · intro i hi j hj hij; obtain ⟨i,rfl⟩:= hy _ hi; obtain ⟨j,rfl⟩:=hy _ hj; rw [ht,ht] at hij; exact congr_arg _ (hm.point (k:=ζ) (by omega) a i j ((unfolded I' a i n k).1 hi).2 ((unfolded ..).1 hj).2 ((Mint.disc S).injective hij))
   intro i hi; obtain ⟨i,rfl⟩:=hy _ hi; rw [ht]; exact (Meadow.contempt hC he hp (I:=I) (I':=I') i).2.symm



variable (h: T'= Deck.re T)(ha:R'.p=R.p)(hx:R'.beta=R.beta)
   {C₁ C₂ d d' z z' t t' A A' u u' r r' v v' q q':ℝ}{b ℓ i j:ℕ}
   (N : Captain I b C₁ d z t A u r v q ℓ χ) (N' : Captain I' j C₂ d' z' t' A' u' r' v' q' i χ)
   (f₀: Config G c)(hy:flags (Pressure.temp x) f₀ = ∅) (hc : 2*(2*(terrace (Mint.width Q.halo (radiusB x) (radiusB x)) k + Mint.width Q.halo (radiusB x) (radiusB x))) < c.val)
include hc N N' hy h ha hx
lemma recognized (s:I'.ThinP) (hs₀ : (flora I' n).theme s.val k) (hV : s.val ⊆ (flora I' n).Window k a) (t:I.ThinP)
    (ht:t.val=s.val.image (trail (K:=K) hC he)) : leaflet I' χ ((V).low.links f₀) s=leaflet I χ f₀ t := by
   obtain ⟨p,hX,hz⟩:= resource_preimage _ s.val hs₀.2.2
   let J₀:= light hC he I' I hp a n k (by omega)
   let v:= (V).low.links f₀
   have hq : t.val=s.val.image J₀.π:=ht; have hv : t.val = Mint.hatch S (wrappers (V) p):=by
     rw [ht,←hz,hatch,hatch,Finset.map_eq_image, Finset.map_eq_image, wrappers]; rw [Finset.image_image,Finset.image_image]; congr 1; exact funext fun i=>Bright.trail_at hC he i -- edit
   have hL : flags (Pressure.temp x) v=∅:= by
     have hproof: 0 < 1 + U := Nat.add_pos_left Nat.zero_lt_one _
     have hc₀ : 4<c.val:= lt_of_lt_of_le (b:=100) (by decide) ((Nat.le_mul_of_pos_right 100 hproof).trans I.laws.data.room.buys)
     ext i; rw [show i∈RG.flags (Pressure.temp x) v ↔ _ from Deck.flagged hC f₀ i hc₀ (Pressure.temp x),hy]; simp
   have hh(t':I'.ThinP):I'.spawn χ v t'.val = leaflet I' χ v t':=(N'.collective t' v).1.trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hL]; simp))
   rw [← hh s, ← show I.spawn χ f₀ t.val= leaflet I χ f₀ t from (N.collective t f₀).1.trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hy]; simp)),hv,← hz]
   exact Mint.meetups hC he I' I h hp ha hx a (ζ+B) hc (fun u hu v h' h=> Mint.disc Y |>.injective (J₀.sits (hV (hz ▸ mem_map_of_mem _ hu)) (hV (hz ▸ mem_map_of_mem _ h')) (by
     change trail _ _ _ = trail _ _ _; rw [Bright.trail_at,Bright.trail_at,show verse_down _ u= verse_down _ v from h]))) (hz.symm ▸ Shelf.patio _ _ _ hV)
     (fun i h=> (mem_filter.mp (hX h)).2) f₀ χ hy (hz.symm ▸ hs₀.1) (hv ▸ hq.symm ▸ ((J₀.seating hV).1 hs₀).1)
lemma vogue : Bright.Ledger k (flora I' n) χ a ((V).low.links f₀)= Bright.Ledger k (flora I n) χ (π a) f₀:= by
   exact Lamp.compare (light hC he I' I hp a n k (by omega)) ((V).low.links f₀) f₀ (recognized hC he I' I hp a n k h ha hx N N' f₀ hy hc)
end lift
end YM.Juniper.Bright
