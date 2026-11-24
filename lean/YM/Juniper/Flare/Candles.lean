import YM.Juniper.Flare.Book
/-! # Selected mixed Shelf windows. Consume cover comparisons, no
 orientation loss at label aggregation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Mint Stellar Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Bright Shelf
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {R:RG.Rep G f} {R':RG.Rep G F}
variable {a b s w : ℝ} {J : ConnectedActivityE6.Target G K}
    {o : ConnectedActivityE6.Target.Order G w} {L₀ : Side}
    (I : Cash w p a L₀ J o b T R) (I' : Cash w p a L₀ J o s T' R')
variable {B' m l : ℕ} {U : Tape (decreed h) R (radiusB p) J.halo}
    {U' : Tape (decreed H) R' (radiusB p) J.halo}
    (V : Volume (Lace.project (h:=h) (H:=H) hC he) U' U m) (hp : R'.path=R.path)
local notation "B" => radiusB p
local notation "μ" => Mint.width J.halo (radiusB p) (radiusB p)
local notation "π" => V.π
local notation "F₀" => lampset («S»:=S) U m
local notation "F₁" => lampset («S»:=Y) U' m

variable (k:ℕ) (z:Site C)
local notation "τ" => Shelf.terrace μ k

def axle : Head (stepped Q H)→Head (stepped Q h):= Function.extend (sites Y) (sites S ∘ Flare.track (L) (V.π)) (fun _=> Classical.arbitrary _)
lemma axle_here (i:TypeLetter C F): axle (Q:=Q) V (sites Y i)= sites S (track (L) (V.π) i):= (sites Y).injective.extend_apply ..
local notation "y"=> portal I' U' m
local notation "x"=> portal I U m
local notation "ϖ"=> axle (Q:=Q) V
local notation "P₀"=> (L).low.cut
local notation "Δ"=> track (L) (V.π)

include I I' hp
/-- All projections used on the same unmasked geometry. The coverage radius
 covers their designated roots and farLog vertex AND projected costs.
 `π` extends arbitrarily outside selected alphabet, never invokes geometry there. -/
def sky (hn:2*(τ+μ)< c.val): Lamp k y x z P₀:= by
   let W:=(y).Window k z; let W':=(x).Window k ((L).low.cut z)
   have hh:=Volume.trail I I' V hp; let Ω:= Volume.depart I I' V hp
   have he i (hi:i∈W):∃ g∈F₁, sites Y g=i:= by obtain ⟨j,hj,rfl⟩:= mem_map.mp ((mem_filter.mp hi).1); exact ⟨_,hj,rfl⟩
   -- he shadows ge; use assumption
   refine ⟨ϖ,le_antisymm ?_ ?_,?_,Meadow.garden hC z hn,?_⟩
   · intro j hj; obtain ⟨i,hi,rfl⟩:= mem_image.mp hj; obtain ⟨i,h,rfl⟩:= he _ hi
     rw [axle_here]; refine (Flare.lightWindow ..).2 ⟨(Volume.moved I I' V hp i h).1,?_⟩
     have hF:= (Volume.major V i h).symm; rw [← Volume.major V i h]; exact (Deck.less ..).trans ((Flare.lightWindow I' U' ..).1 hi).2
   · intro i hi; obtain ⟨i,hu,rfl⟩:= mem_map.mp (mem_filter.mp hi).1; obtain ⟨ht,hT⟩:= Flare.lightWindow I U («x»:=(L).low.cut z) i m k|>.1 hi -- x binder name conflict
     obtain ⟨⟨j,hj⟩,hj',hz⟩:= hh.esc z ⟨i,ht⟩; have heq:Δ j = i:= congr_arg Subtype.val hj'
     refine mem_image.mpr ⟨sites Y j, (Flare.lightWindow ..).2 ⟨hj,hz.trans_le hT⟩,?_⟩; rw [axle_here]; exact congr_arg (sites S) heq
   · intro i hi j hj hk; obtain ⟨i,hf,rfl⟩:= he _ hi; obtain ⟨j,hv,rfl⟩:= he _ hj; rw [axle_here,axle_here] at hk
     exact congr_arg _ (show i=j from congr_arg Subtype.val (hh.point (k:=τ) (by omega) z ⟨i,hf⟩ ⟨j,hv⟩ ((Flare.lightWindow ..).1 hi).2 ((Flare.lightWindow ..).1 hj).2 (Subtype.ext ((sites S).injective hk))))
   intro i hi; obtain ⟨i,h,rfl⟩:= he _ hi; rw [axle_here]; have ht:= I.laws.data.room.buys; have hg : c.val ≤ f.val:= ‹f.val=c.val*P.L.val› ▸ Nat.le_mul_of_pos_right _ P.L.pos
   exact (matched (T:=T) (T':=T') (l:=J.halo) (s:=radiusB p) (V.π) i hp (by omega) ((Volume.moved I I' V hp i h).2)).symm

open Blaze Silica March Captain
variable {C₁ C₂ d d' θ θ' u u' t t' A A' r r' v v' q q' p' p'' : ℝ} {χ:Chi} {j j' n n':ℕ}
variable (N: Captain I j C₁ d θ t A u r v q n χ) (N': Captain I' j' C₂ d' θ' t' A' u' r' v' q' n' χ)
variable (hn: 2 * (2*(Shelf.terrace (Mint.width J.halo (radiusB p) (radiusB p)) k + Mint.width J.halo (radiusB p) (radiusB p))) < c.val)
variable (hT:T'=Deck.re T) (he' : R'.p=R.p)(hβ : R'.beta=R.beta)
    (V₀: Config G c) (h₀: flags (Pressure.temp p) V₀=∅)
include N N' hn hT he' hβ h₀
lemma shine (u:I'.ThinP) (ht:(y).theme u.val k) (hV:u.val⊆(y).Window k z)
    (v:I.ThinP)(hX:v.val=u.val.image ϖ) : leaflet I' χ ((L).low.links V₀) u= leaflet I χ V₀ v:= by
   let Ω:= sky I I' V hp k z (by omega); let P:= (F₁).filter fun i=> sites Y i ∈ u.val
   have h₁: members Y P=u.val:= by
      ext i; constructor
      · intro hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp hi; exact (mem_filter.mp hj).2
      intro hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp (ht.2.2 hi); exact mem_map_of_mem _ (mem_filter.mpr ⟨hj,hi⟩)
   have hΩ : v.val = u.val.image Ω.π:= hX
   have h₂:v.val= members S (wallet (L) (V.π) P):= by
      rw [hX,← h₁]; unfold members wallet; rw [Finset.map_eq_image,Finset.map_eq_image,image_image,image_image];
      apply image_congr; intro i _; exact Flare.axle_here (Q:=Q) V i
   let f:=(L).low.links V₀; have hC : flags (Pressure.temp p) f=∅:= by
      have hc : 4 < c.val:= by have ht:= I.laws.data.room.buys; omega
      ext i; rw [show i∈flags (Pressure.temp p) f ↔ _ from Deck.flagged hC V₀ i hc _,h₀]; simp
   have hh:I'.spawn χ f u.val=leaflet I' χ f u:=(N'.collective ..).1.trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hC]; simp))
   rw [← hh, ← show I.spawn χ V₀ v.val=leaflet I χ V₀ v from (N.collective ..).1.trans (masked_eq _ _ _ _ (by unfold Healthy; rw [h₀]; simp)),h₂,← h₁]
   refine Flare.meetups ‹C.val=_› he V.π I' I hT hp he' hβ z (τ+μ) hn (fun i hi j hj h=> ?_)
      (by rw [h₁]; exact Shelf.patio _ _ _ hV) (fun i hi=> (Volume.moved I I' V hp i (mem_filter.mp hi).1).2)
      V₀ χ h₀ (by rw [h₁]; exact ht.1) (by rw [← h₂,hΩ]; exact ((Ω.seating hV).1 ht).1)
   apply (sites Y).injective (Ω.sits (hV ((mem_filter.mp hi).2)) (hV ((mem_filter.mp hj).2)) ?_); rw [show Ω.π=ϖ from rfl]; exact (axle_here V _).trans ((congr_arg _ h).trans (axle_here V _).symm)

include V
lemma illuminated : Bright.Ledger k y χ z ((L).low.links V₀)= Bright.Ledger k x χ ((L).low.cut z) V₀:=
   Lamp.compare (sky I I' V hp k z (by omega)) ((L).low.links V₀) V₀ (shine I I' V hp k z N N' hn hT he' hβ V₀ h₀)
end YM.Juniper.Flare
