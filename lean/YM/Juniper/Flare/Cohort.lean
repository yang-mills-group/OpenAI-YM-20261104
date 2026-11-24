import YM.Juniper.Flare.Letters
/-!
 # Mixed lift: exact shared-tag & Gaussian stencil cumulants.
 The E book extension requires the entire genealogy proof (not termwise
 multiplying a claim about separate one-operator expectations).
 Adapts Deck/{Purloin,Detrain,Quips}.lean proofs; see also Letters.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Mint Stellar Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
variable (π : ℕ → ℕ)
abbrev wallet (L': Lace h H M) (π : ℕ → ℕ) (U : Finset (TypeLetter C F)):= U.image (track L' π)

section mixed
variable {U : Finset (TypeLetter C F)}

variable {a v W K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (hf : X'.manifest) (hm:X.manifest) (hK:X.width=o.K)
    (k k':Finset ℕ)
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (track (Lace.project (h:=h) (H:=H) hC he) π) U)
    (hS:C'.unionP (U.map (sites (stepped Q H)))⊆neighbors n Z) (hw:∀ i∈U,Pertinent (Lace.project (h:=h) (H:=H) hC he) π (radiusB p) R' R i)
include C' c' A ht hx hb hf hm hK hZ hd hS hw
lemma blankets : let q:= U.map (sites (Y)); let u:=(wallet (L) π U).map (sites (S))
    X'.attains R' J.table W o.a k J.halo q=X.attains R J.table W o.a k' J.halo u := by
  intro q u
  let I:= podium (Y) G (C'.unionP q) X'.B; let g:= X'.body R' J.table W o.a k J.halo q; let f:= X.body R J.table W o.a k' J.halo u
  let l:=L; let x' := radiusB p
  have hz : X'.width=o.K:= A.wit.symm.trans hK
  have hi i (hi:i∈I):separation Z (along (Y) i) ≤ n:= (neighbors_mem ..).1 (hS <| (mem_filter.mp hi).2 (along (Y) i) (by rw [separation_self]; omega))
  have hj:= tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he
  let y:= seed (G:=G) l; let e:↥I ↪ Tubular _ G:= ⟨fun i=> y i.val, fun i k h=> Subtype.ext (hj.point (k:=n) (by omega) Z _ _ (hi _ i.2) (hi _ k.2) h)⟩
  have hE : circuit I X'.relating=X.relating.submatrix e e:= by ext i j; apply A.allocates hZ; refine (separation_triangle _ Z _).trans ?_; rw [separation_comm _ Z]; have hz:=hi _ i.2; have hk:=hi _ j.2; dsimp only; omega
  let a:= arch I X'.relating; have hI:MeasurePreserving (swim I) X'.dice a:= orbit (C'.laws.data.localP E' X' A.reached hz hf).sails.fullC.posSemidef I; have hl:MeasurePreserving (mount e) X.dice a:= by unfold a arch; rw [hE]; exact loss e _ (c'.laws.data.localP E X A.equal hK hm).sails.fullC.posSemidef
  have hx (Y₁:E.Slice G) (Y₂:E'.Slice G): (∫ z,g (Y₂,z) ∂X'.dice) = ∫ z,f (Y₁,z) ∂X.dice:= by
    let a z:=g (Y₂,spill I z); let b z:=g (Y₂,z)
    have ha : Measurable b:= ((X'.body_b J.table_exists (A.reached.symm ▸ C'.laws.intake) (by rw [A.reached,hz]; exact C'.laws.data.access) ..)).comp (measurable_const.prodMk measurable_id)
    have hp : Measurable a:= ha.comp (spill_m I)
    have he (u v) (h : swim I u=swim I v): b u=b v:= C'.concord q (X'.wrapY Y₂) (X'.wrapY Y₂) ⟨Village.refl _ _,(observe _).1 h,fun _ _=> Iff.rfl⟩ A.reached (Finset.Subset.refl _)
    have hy z:f (Y₁,z)=a (mount e z):= by
      rw [show a (mount e z)=b (blow l z) from he _ _ (Pond.settled _ _)]; change _=(X'.wrapY Y₂).term _ _ _ _ _ _ _ _
      unfold f Coat.body; dsimp only; unfold q u Coat.term; rw [prod_map,prod_map]; unfold wallet; rw [prod_image hd]
      exact Finset.prod_congr rfl (fun i hi=> (pay (A.draws Y₁ Y₂) π i ht hx hb (hw i hi) Z (fun j hj=> hS (mem_biUnion.mpr ⟨_,mem_map_of_mem (sites Y) hi,hj⟩)) (by have hx:= A.news; have hv:= A.old.buys; omega) z J.table W o.a ..).symm)
    rw [Pond.gathered (spill I) (spill_m I) hI (Pond.settled I) he ha]; change (∫ z,a z ∂_) =_
    rw [← hl.map_eq,MeasureTheory.integral_map (by exact hl.measurable.aemeasurable) hp.aestronglyMeasurable]; exact integral_congr_ae (Eventually.of_forall fun i=> (hy i).symm)
  unfold attains; rw [integral_prod _ (C'.integrated X' A.reached hz hf k q),integral_prod _ (c'.integrated X A.equal hK hm k' u)]
  let D := (∫ y,g (X'.Y,y) ∂X'.dice)
  have ht (z:E'.Slice G): (∫ y,g (z,y) ∂X'.dice)= D:= (hx X.Y z).trans (hx X.Y X'.Y).symm
  have hk (z:E.Slice G): (∫ y,f (z,y) ∂X.dice)=D:= (hx z _).symm
  change (∫ z:E'.Slice G, (∫ y,g (z,y) ∂X'.dice) ∂E'.order G)=(∫ z:E.Slice G, (∫ y,f (z,y) ∂X.dice) ∂E.order G)
  simp_rw [ht,hk]; simp

end mixed
variable (hC he)
variable {U : Finset (TypeLetter C F)} {a v W q K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta)
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (track (Lace.project (h:=h) (H:=H) hC he) π) U)
    (hS:C'.unionP (members (stepped Q H) U)⊆neighbors n Z) (hw:∀ i∈U,Pertinent (Lace.project (h:=h) (H:=H) hC he) π (radiusB p) R' R i)
    (V:Config G c) (χ:Chi) (hv : RG.flags (Pressure.temp p) V=∅)
include he C' c' hq ht hx hb hv hZ hd hS hw
lemma trimmed (hf : (L).Fitted E E') :
    let q:=members (Y) U; let r:=(wallet (L) π U).map (sites (stepped Q h)); let Y':=(L).low.links V
    amountP R' (prism T' p χ o.K Y' E') W o.a J.halo J.table q=amountP R (prism T p χ o.K V E) W o.a J.halo J.table r := by
  intro q r Y'
  let X:= planted (prism T p χ o.K V E) r; let X':= planted (prism T' p χ o.K Y' E') q
  have hk := c'.laws.data.room; have hM:= C'.laws.data.room
  have he: X.manifest:=planted_valid ..; have he':X'.manifest:=planted_valid ..
  have hB:bleached X:= by
    change { (roster (members (stepped Q h) _)) with flags:= RG.flags (Pressure.temp p) V}= _; rw [Flare.no_roster,hv]
  have hQx : RG.flags (Pressure.temp p) Y'=∅ := by
    ext i; rw [show i∈RG.flags (Pressure.temp p) Y' ↔ _ from flagged hC V i (show _ from (by have h:= hk.buys; omega)) (Pressure.temp p),hv]; simp
  have hB': bleached X':= by
    change { (roster (members (stepped Q H) _)) with flags:= RG.flags (Pressure.temp p) Y'}= _; rw [Flare.no_roster,hQx]
  let p' := Mint.weftK (h:=h) (Q:=Q) (H:=H) hC Z -- shadowed h
  let f' k:=(X'.taggedL k).attains R' J.table W o.a (own q) J.halo q; let f k:=(X.taggedL k).attains R J.table W o.a (own r) J.halo r
  have hh k : f' ((L).pullTag Q k)=f k:= by
    let Z:= X.taggedL k; let Y'':=X'.taggedL ((L).pullTag Q k); have hr:Stellar hC (by assumption) K p Z Y'':= ⟨hB,hB',rfl,rfl,rfl,rfl,rfl,hf,rfl,hk,hM,hq,by have hp:=hk.buys; omega⟩
    exact blankets hr π C' c' ht (by assumption) hb he' he rfl (own q) (own r) _ _ hZ hd hS hw
  have hg k : f' k=f (p' k):= by
    rw [← hh]
    let w:= X'.taggedL ((L).pullTag Q (p' k)); have ht i (hi:i∈C'.unionP q):Deck.reverts hC Z ((L).low.cut i)=i:= same_site hC Z _ (by omega) hS i hi
    apply C'.vista q (X'.taggedL k) w rfl rfl he' he' _ (fun _ _=>Iff.rfl); refine ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun i hi=>?_,fun i hi=> ?_,fun _ _ _=> rfl⟩
    · exact (congr_arg k.1 (ht _ hi)).symm
    exact (congr_arg k.2 (show (Deck.reverts hC Z ((L).low.cut i.1),i.2)=i from Prod.ext (ht i.1 hi) rfl)).symm
  change likely f'=likely f; rw [funext hg]; exact (makeup (hC:=hC) Z).cashout f

lemma meetups (hp:Ac.Spark C'.supportP (members Y U)) (hP: Ac.Spark c'.supportP (members (stepped Q h) (wallet (L) π U))):
    C'.spawn χ ((L).low.links V) (members Y U)= c'.spawn χ V (members (stepped Q h) (wallet (L) π U)):= by
  letI:Nonempty (Forest (Y).ratio):= Tree.select (decreed H) P.odd_side; letI:Nonempty (Forest ((stepped Q h)).ratio):= Tree.select (decreed h) P.odd_side
  let V':= (L).low.links V; let q:= members Y U; let p':= members (stepped Q h) (wallet (L) π U)
  have hx' : RG.flags (Pressure.temp p) V'=∅:= by
    ext i; rw [show i∈ RG.flags (Pressure.temp p) V' ↔ _ from flagged hC V i (by have h:= c'.laws.data.room.buys; omega) (Pressure.temp p),hv]; simp
  have hh E (F:Forest (Y).ratio) (he:(L).Fitted E F) : proceedsA R' (prism T' p χ o.K V' F) W o.a J.halo J.table q = proceedsA R (prism T p χ o.K V E) W o.a J.halo J.table p':= by
    have ha : standsIn (prism T' p χ o.K V' F) R' J.halo q:=⟨hp,troupers ..,by change RG.flags (Pressure.temp p) V' ∩ _ = _; rw [hx',show roster q=_ from no_roster ..,Finset.empty_inter]⟩
    have hw':standsIn (prism T p χ o.K V E) R J.halo p':=⟨hP,troupers ..,by change RG.flags (Pressure.temp p) V ∩ _ = _; rw [hv,show roster p'=_ from no_roster ..,Finset.empty_inter]⟩
    unfold proceedsA; rw [if_pos ha,if_pos hw']; exact trimmed hC _ π C' c' hq ht hx hb Z n hZ hd hS hw V χ hv he
  let p₁:=(L).low.cut; let w:= Deck.reverts hC Z
  let f' (i:Reserve Y):= proceedsA R' (prism T' p χ o.K V' (Greenbelt.allot i)) W o.a J.halo J.table q
  let f (i:Reserve (stepped Q h)):= proceedsA R (prism T p χ o.K V (Greenbelt.allot i)) W o.a J.halo J.table p'
  let P (i:Reserve Y) (j:Site c):= Deck.dismount (h:=h) hC he Z (i (w j))
  change likely f' = likely f
  have heq k:f' k=f (P k):= by
    let F':= Greenbelt.allot («S»:=((stepped Q h))) (P k); let E':=(L).repeater F'
    rw [show f (P k)= _ from (hh F' E' ⟨fun i=>rfl⟩).symm]; refine Horticulture.Travels.sails _ _ _ rfl rfl rfl rfl rfl rfl C' ?_; intro i hi
    have hc := (hS (show _∈ C'.unionP (members Y U) from hi)); let x:= (Y).ratio.parent i; have hx':x∈ Set.range w:= ⟨p₁ x,(same_site hC Z _ (by omega) hS x hi)⟩
    change (k x).up i = F'.up ((L).high.cut i); unfold F' Greenbelt.allot P; dsimp only; unfold dismount; dsimp only
    rw [show ((stepped Q h)).ratio.parent _= _ from Lace.position (L) i,show w ((L).low.cut ((L).R.parent i))=x from same_site hC Z _ (by omega) hS x hi, Deck.hereagain (h:=h) (H:=H) hC he Z hx' i rfl]
  rw [funext heq]; have hk : Matchup (P: Reserve Y→ Reserve (stepped Q h)):= ((Deck.countingF (Q:=Q) (h:=h) (H:=H) hC he Z).expands w (irrevocable ..)); exact hk.cashout f
end YM.Juniper.Flare
