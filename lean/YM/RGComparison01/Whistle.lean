import YM.RGComparison01.Orbit

/-!
# Use a Relay to actually push with ALL catalog heads

 Uses Deck marginals at every ROOT/Cash. We emphasize because all-arity Hessian
 cancellations cannot be charged if changing stencils just by equality of
 bulk unanchored evaluations. Here render on an auxiliary where the true
 path is held; later recover anchor costs. This keeps both F and V predicates
 in their direct Roles. Follows `Deck.*` proofs, using their priced support/
 transport & physical block interfaces; extends Optic to attached E materials
 & membership. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Relay
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {c f C F L₀: Side} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC:C.val=c.val*M} {he : 2≤ c.val}
variable {T:Tube G (stepped Q h)} {T':Tube G (stepped Q H)} {R : RG.Rep G f} {R':RG.Rep G F}
  {I : Cash W s a L₀ X o U T R} {I' : Cash W s a L₀ X o u T' R'}
  {D : Cabinet ι I b} {A : Cabinet χ I' b} {Z : χ → ι}
    (L':Relay (A:=A) (D:=D) hC he Z)
local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {E : Tree.Forest (stepped Q h).ratio} {E' : Tree.Forest (stepped Q H).ratio}
variable (x : Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (p : Cabinet.Folder χ)
    (hS:A.garden p⊆neighbors n x)
local notation "q" => (A.shell p)
local notation "U₁" => (D.shell (send Z p))

include L' hZ hS
lemma audit {Θ : Coat T E} {Θ' : Coat T' E'} (J : Stellar hC he K s Θ Θ') (hf : Θ'.manifest) (hm:Θ.manifest) (hK:Θ.width=o.K) (k k':Finset ℕ) :
    Θ'.attains R' X.table W o.a k X.halo q=Θ.attains R X.table W o.a k' X.halo U₁ := by
  let V:= podium (Y) G (A.garden p) Θ'.B; let g:= Θ'.body R' X.table W o.a k X.halo q; let f':= Θ.body R X.table W o.a k' X.halo U₁
  have hz : Θ'.width=o.K := J.wit.symm.trans hK
  have hi i (hi:i∈V):separation x (along (Y) i) ≤ n := (neighbors_mem ..).1 (hS ((mem_filter.mp hi).2 (along (Y) i) (by rw [separation_self]; omega)))
  have hj:= tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he
  let y:= seed (G:=G) (L); let e:↥V ↪ Tubular _ G:= ⟨fun i=> y i.val, fun i k h=> Subtype.ext (hj.point (k:=n) (by omega) x _ _ (hi _ i.2) (hi _ k.2) h)⟩
  have hE : circuit V Θ'.relating=Θ.relating.submatrix e e:= by ext i j; apply J.allocates hZ; refine (separation_triangle _ x _).trans ?_; rw [separation_comm _ x]; have hz:=hi _ i.2; have hk:=hi _ j.2; dsimp only; omega
  let μ:= arch V Θ'.relating; have hI:MeasurePreserving (swim V) Θ'.dice μ:= orbit (I'.laws.data.localP E' Θ' J.reached hz hf).sails.fullC.posSemidef V
  have hl:MeasurePreserving (mount e) Θ.dice μ:= by unfold μ arch; rw [hE]; exact loss e _ (I.laws.data.localP E Θ J.equal hK hm).sails.fullC.posSemidef
  have hx (Y₁:E.Slice G) (Y₂:E'.Slice G): (∫ z,g (Y₂,z) ∂Θ'.dice) = ∫ z,f' (Y₁,z) ∂Θ.dice:= by
    let t z:=g (Y₂,spill V z); let b z:=g (Y₂,z)
    have ha : Measurable b:= ((Θ'.body_b X.table_exists (J.reached.symm ▸ I'.laws.intake) (by rw [J.reached,hz]; exact I'.laws.data.access) ..)).comp (measurable_const.prodMk measurable_id)
    have hp : Measurable t:= ha.comp (spill_m V); have he (u v) (h : swim V u=swim V v): b u=b v:= I'.concord q (Θ'.wrapY Y₂) (Θ'.wrapY Y₂) ⟨Village.refl _ _,(observe _).1 h,fun _ _=> Iff.rfl⟩ J.reached (Finset.Subset.refl _)
    have hy z:f' (Y₁,z)=t (mount e z):= by
      rw [show t (mount e z)=b (blow (L) z) from he _ _ (Pond.settled _ _)]
      change (Θ.wrapY Y₁).term _ _ _ _ _ _ _ _= (Θ'.wrapY Y₂).term _ _ _ _ _ _ _ _
      unfold Coat.term Cabinet.shell; rw [prod_map,prod_map]; unfold send; rw [prod_image (L'.injected x _ (by omega) _ hS)]
      exact Finset.prod_congr rfl (fun i hi=> (L'.grant (J.draws Y₁ Y₂) k k' z i).symm)
    rw [Pond.gathered (spill V) (spill_m V) hI (Pond.settled V) he ha]; change (∫ z,t z ∂_) =_
    rw [← hl.map_eq,MeasureTheory.integral_map hl.measurable.aemeasurable hp.aestronglyMeasurable]; exact integral_congr_ae (Eventually.of_forall fun i=> (hy i).symm)
  unfold attains; rw [integral_prod _ (I'.integrated Θ' J.reached hz hf k q),integral_prod _ (I.integrated Θ J.equal hK hm k' U₁)]
  let Q₀:= (∫ y,g (Θ'.Y,y) ∂Θ'.dice); have ht (z:E'.Slice G): (∫ y,g (z,y) ∂Θ'.dice)= Q₀:= (hx Θ.Y z).trans (hx Θ.Y Θ'.Y).symm
  have hk (z:E.Slice G): (∫ y,f' (z,y) ∂Θ.dice)=Q₀:= (hx z _).symm
  change (∫ z:E'.Slice G, (∫ y,g (z,y) ∂Θ'.dice) ∂E'.order G)=(∫ z:E.Slice G, (∫ y,f' (z,y) ∂Θ.dice) ∂E.order G)
  simp_rw [ht,hk]; simp

variable (hq : T'= re T) (V:Config G c) (κ:Chi) (hv : RG.flags (Pressure.temp s) V=∅)
set_option quotPrecheck false
local notation "V'" => (L).low.links V
include hq hv
lemma merit (hf : (L).Fitted E E') :
    amountP R' (prism T' s κ o.K (V') E') W o.a X.halo X.table q=amountP R (prism T s κ o.K V E) W o.a X.halo X.table U₁ := by
  let Θ:= planted (prism T s κ o.K V E) U₁; let Θ':= planted (prism T' s κ o.K (V') E') q
  have hk := I.laws.data.room; have hM:= I'.laws.data.room; have he₁: Θ.manifest:=planted_valid ..; have he₂:Θ'.manifest:=planted_valid ..
  have hB:bleached Θ:= by change { (roster (D.shell _)) with flags:= RG.flags (Pressure.temp s) V}= _; rw [D.unstored,hv]
  have hQx : RG.flags (Pressure.temp s) (V')=∅ := by
    ext i; rw [show i∈RG.flags (Pressure.temp s) (V') ↔ _ from flagged hC V i (show _ from (by have h:= hk.buys; omega)) (Pressure.temp s),hv]; simp
  have hB': bleached Θ':= by change { (roster q) with flags:= RG.flags (Pressure.temp s) (V')}= _; rw [A.unstored,hQx]
  let p' := weftK (h:=h) (Q:=Q) (H:=H) hC x
  let f' k:=(Θ'.taggedL k).attains R' X.table W o.a (own q) X.halo q; let f k:=(Θ.taggedL k).attains R X.table W o.a (own U₁) X.halo U₁
  have hh k : f' ((L).pullTag Q k)=f k:= by
    let Z:= Θ.taggedL k; let Y'':=Θ'.taggedL ((L).pullTag Q k); have hr:Stellar hC (by assumption) K s Z Y'':= ⟨hB,hB',rfl,rfl,rfl,rfl,rfl,hf,rfl,hk,hM,hq,by have hp:=hk.buys; omega⟩
    exact L'.audit x n hZ p hS hr he₂ he₁ rfl (own q) (own U₁)
  have hg k : f' k=f (p' k):= by
    rw [← hh]
    let w:= Θ'.taggedL ((L).pullTag Q (p' k)); have ht i (hi:i∈I'.unionP q):Deck.reverts hC x ((L).low.cut i)=i:= same_site hC x _ (by omega) hS i hi
    apply I'.vista q (Θ'.taggedL k) w rfl rfl he₂ he₂ _ (fun _ _=>Iff.rfl); refine ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun i hi=>?_,fun i hi=> ?_,fun _ _ _=> rfl⟩
    · exact (congr_arg k.1 (ht _ hi)).symm
    exact (congr_arg k.2 (show (Deck.reverts hC x ((L).low.cut i.1),i.2)=i from Prod.ext (ht i.1 hi) rfl)).symm
  change likely f'=likely f; rw [funext hg]; exact (Deck.Mint.makeup (hC:=hC) x).cashout f

lemma illuminates (hp:Ac.Spark I'.supportP q) (hP: Ac.Spark I.supportP U₁):
    I'.spawn κ (V') q= I.spawn κ V U₁:= by
  letI:Nonempty (Forest (Y).ratio):= Tree.select (decreed H) P.odd_side; letI:Nonempty (Forest (S).ratio):= Tree.select (decreed h) P.odd_side
  have hx' : RG.flags (Pressure.temp s) (V')=∅:= by
    ext i; rw [show i∈ RG.flags (Pressure.temp s) (V') ↔ _ from flagged hC V i (by have h:= I.laws.data.room.buys; omega) (Pressure.temp s),hv]; simp
  have hh E (F:Forest (Y).ratio) (he:(L).Fitted E F) : proceedsA R' (prism T' s κ o.K (V') F) W o.a X.halo X.table q = proceedsA R (prism T s κ o.K V E) W o.a X.halo X.table U₁:= by
    have ha : standsIn (prism T' s κ o.K (V') F) R' X.halo q:=⟨hp,A.attends p _ _,by change RG.flags (Pressure.temp s) (V') ∩ _ = _; rw [hx',A.unstored p,Finset.empty_inter]⟩
    have hw':standsIn (prism T s κ o.K V E) R X.halo U₁:=⟨hP,D.attends _ _ _,by change RG.flags (Pressure.temp s) V ∩ _ = _; rw [hv,D.unstored,Finset.empty_inter]⟩
    unfold proceedsA; rw [if_pos ha,if_pos hw']; exact L'.merit x n hZ p hS hq V κ hv he
  let u := (L).low.cut; let w:= Deck.reverts hC x
  let f' (i:Reserve Y):= proceedsA R' (prism T' s κ o.K (V') (Greenbelt.allot i)) W o.a X.halo X.table q
  let f (i:Reserve S):= proceedsA R (prism T s κ o.K V (Greenbelt.allot i)) W o.a X.halo X.table U₁
  let P (i:Reserve Y) (j:Site c):= Deck.dismount (h:=h) hC he x (i (w j))
  change likely f' = likely f; have heq k:f' k=f (P k):= by
    let F':= Greenbelt.allot («S»:=(S)) (P k); let E':=(L).repeater F'; rw [show f (P k)= _ from (hh F' E' ⟨fun i=>rfl⟩).symm]
    refine Horticulture.Travels.sails _ _ _ rfl rfl rfl rfl rfl rfl I' ?_; intro i hi
    let t:= (Y).ratio.parent i; have hx':t∈ Set.range w := ⟨u t,(same_site hC x _ (by omega) hS t hi)⟩
    change (k t).up i = F'.up ((L).high.cut i); unfold F' Greenbelt.allot P; dsimp only; unfold dismount; dsimp only
    rw [show (S).ratio.parent _= _ from Lace.position (L) i,show w ((L).low.cut ((L).R.parent i))=t from same_site hC x _ (by omega) hS t hi, Deck.hereagain (h:=h) (H:=H) hC he x hx' i rfl]
  rw [funext heq]; have hk : Matchup (P: Reserve Y→ Reserve S):= ((Deck.countingF (Q:=Q) (h:=h) (H:=H) hC he x).expands w (irrevocable ..)); exact hk.cashout f
end YM.RGComparison01.Relay
