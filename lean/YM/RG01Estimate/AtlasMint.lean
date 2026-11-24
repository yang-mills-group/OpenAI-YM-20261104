import YM.RG01Estimate.DeckShift
/-! # Universal transfer of Ω under the genuine Tags & seed convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Greenbelt Deck.Stellar Poll Pond MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
variable {Γ : Type}
variable {a v W K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta)
    {V:Lex Γ f}{V':Lex Γ F}(A:Charts (h:=h) (H:=H) hC he R R' V V') {U: Finset (Header Γ C F)} {m : ℕ}
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (warps (Γ:=Γ) (Lace.project (h:=h) (H:=H) hC he)) U)
    (hS:C'.unionP (songs («S»:=stepped Q H) V' U)⊆neighbors n Z)
    (hw:∀ i∈ U,fit R'.path i ≤ radiusB p)
    (hU: ∀ i, regularFoot (decreed H) 0 (radiusB p) R' (V' i)⊆neighbors m ((decreed H).parent i.1))
    (hC': 2*(m+3)<c.val)
section shelter
end shelter
section tag
variable {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    (hq:T'=Deck.re T) (cV: Config G c) (χ:Chi)
    (hv: RG.flags (Pressure.temp p) cV=∅)
include hC he ht hx hb C' c' hZ hd hS hw hU hC' hq A hv
lemma commute (hf : (L).Fitted E E') :
    let q:=songs («S»:=stepped Q H) V' U; let r:=songs («S»:=stepped Q h) V (U.image (warps (L))); let Y':=(L).low.links cV
    amountP R' (prism T' p χ o.K Y' E') W o.a J.halo J.table q=amountP R (prism T p χ o.K cV E) W o.a J.halo J.table r := by
  intro q r Y'
  let X:= planted (prism T p χ o.K cV E) r; let X':= planted (prism T' p χ o.K Y' E') q
  have hk := c'.laws.data.room; have hM:= C'.laws.data.room
  have hh: X.manifest:=planted_valid ..; have he':X'.manifest:=planted_valid ..
  have hB:bleached X:= by
    change { (roster r) with flags:= RG.flags (Pressure.temp p) cV}= _; unfold r; rw [white,hv]
  have hQx : RG.flags (Pressure.temp p) Y'=∅ := by
    ext i; rw [show i∈RG.flags (Pressure.temp p) Y' ↔ _ from flagged hC cV i (show _ from (by have h:= hk.buys; omega)) (Pressure.temp p),hv]; simp
  have hB': bleached X':= by
    change { (roster q) with flags:= RG.flags (Pressure.temp p) Y'}= _; unfold q; rw [white,hQx]
  let p' := Mint.weftK (h:=h) (Q:=Q) (H:=H) hC Z
  let f' k:=(X'.taggedL k).attains R' J.table W o.a (own q) J.halo q; let f k:=(X.taggedL k).attains R J.table W o.a (own r) J.halo r
  have heq k : f' ((L).pullTag Q k)=f k:= by
    let K':= X.taggedL k; let Y'':=X'.taggedL ((L).pullTag Q k); have hr:Stellar hC he K p K' Y'':= ⟨hB,hB',rfl,rfl,rfl,rfl,rfl,hf,rfl,hk,hM,hq,by have hp:=hk.buys; omega⟩
    exact correspondence C' c' ht hx hb A Z n hZ hd hS hw hU hC' hr he' hh rfl ..
  have hg k : f' k=f (p' k):= by
    rw [← heq]
    let w:= X'.taggedL ((L).pullTag Q (p' k)); have ht i (hi:i∈C'.unionP q):Deck.reverts hC Z ((L).low.cut i)=i:= same_site hC Z _ (by omega) hS i hi
    apply C'.vista q (X'.taggedL k) w rfl rfl he' he' _ (fun _ _=>Iff.rfl); refine ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun i hi=>?_,fun i hi=> ?_,fun _ _ _=> rfl⟩
    · exact (congr_arg k.1 (ht _ hi)).symm
    exact (congr_arg k.2 (show (Deck.reverts hC Z ((L).low.cut i.1),i.2)=i from Prod.ext (ht i.1 hi) rfl)).symm
  change likely f'=likely f; rw [funext hg]; exact (Mint.makeup (hC:=hC) Z).cashout f

lemma spawn_read (hp:Ac.Spark C'.supportP (songs («S»:=stepped Q H) V' U))
    (hP: Ac.Spark c'.supportP (songs («S»:=stepped Q h) V (U.image (warps (L))))) :
    let q:=songs («S»:=stepped Q H) V' U; let r:=songs («S»:=stepped Q h) V (U.image (warps (L)))
    C'.spawn χ ((L).low.links cV) q=c'.spawn χ cV r := by
  intro q p'; letI:Nonempty (Forest (Y).ratio):= Tree.select (decreed H) P.odd_side; letI:Nonempty (Forest (S).ratio):= Tree.select (decreed h) P.odd_side
  let W':= (L).low.links cV; have hx' : RG.flags (Pressure.temp p) W'=∅:= by
    ext i; rw [show i∈ RG.flags (Pressure.temp p) W' ↔ _ from flagged hC cV i (by have h:= c'.laws.data.room.buys; omega) (Pressure.temp p),hv]; simp
  have hh E (F:Forest (Y).ratio) (hE:(L).Fitted E F) : proceedsA R' (prism T' p χ o.K W' F) W o.a J.halo J.table q = proceedsA R (prism T p χ o.K cV E) W o.a J.halo J.table p':= by
    have ha : standsIn (prism T' p χ o.K W' F) R' J.halo q:=⟨hp,cannery ..,by change RG.flags (Pressure.temp p) W' ∩ _ = _; rw [hx',show roster q=_ from white ..,Finset.empty_inter]⟩
    have hw':standsIn (prism T p χ o.K cV E) R J.halo p':=⟨hP,cannery ..,by change RG.flags (Pressure.temp p) cV ∩ _ = _; rw [hv,show roster p'=_ from white ..,Finset.empty_inter]⟩
    unfold proceedsA; rw [if_pos ha,if_pos hw']; exact commute C' c' ht hx hb A Z n hZ hd hS hw hU hC' hq cV χ hv hE
  let p₁:=(L).low.cut; let w:= Deck.reverts hC Z
  let f' (i:Reserve Y):= proceedsA R' (prism T' p χ o.K W' (Greenbelt.allot i)) W o.a J.halo J.table q
  let f (i:Reserve (S)):= proceedsA R (prism T p χ o.K cV (Greenbelt.allot i)) W o.a J.halo J.table p'
  let P (i:Reserve Y) (j:Site c):= Deck.dismount (h:=h) hC he Z (i (w j))
  change likely f' = likely f
  have heq k:f' k=f (P k):= by
    let F':= Greenbelt.allot («S»:=(S)) (P k); let E':=(L).repeater F'
    rw [show f (P k)= _ from (hh F' E' ⟨fun i=>rfl⟩).symm]; refine Horticulture.Travels.sails _ _ _ rfl rfl rfl rfl rfl rfl C' ?_; intro i hi
    have hc := (hS (show _∈ C'.unionP q from hi)); let x:= (Y).ratio.parent i; have hx':x∈ Set.range w:= ⟨p₁ x,(same_site hC Z _ (by omega) hS x hi)⟩
    change (k x).up i = F'.up ((L).high.cut i); unfold F' Greenbelt.allot P; dsimp only; unfold dismount; dsimp only
    rw [show (S).ratio.parent _= _ from Lace.position (L) i,show w ((L).low.cut ((L).R.parent i))=x from same_site hC Z _ (by omega) hS x hi, Deck.hereagain (h:=h) (H:=H) hC he Z hx' i rfl]
  rw [funext heq]; have hk : Matchup (P: Reserve Y→ Reserve (S)):= ((Deck.countingF (Q:=Q) (h:=h) (H:=H) hC he Z).expands w (irrevocable ..)); exact hk.cashout f
end tag
end YM.RG01Estimate.Evoc
