import YM.Contacts.Poetry.Locus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Tableau
/-! adapted from Meadow/{Nil,Coset,Tableau,Camp} for all arities. No time evolution assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M oo oo₀ j D' m: ℕ} {K : Teller G} {p a W U V:ℝ}
section sow
variable {S:StepData c f} {T : Tube G S} {R:RG.Rep G f} {X: ConnectedActivityE6.Target G K} {o:Target.Order G W}
    {H : Cash W p a L₀ X o U T R}
variable {Ξ: Lecturer R oo}{χ:Chi}
def held (m: Meter c f) := Sum.elim Meadow.held (fun _=>0) m
def tuck (k:ℕ): Finset (Meter c f):= (@Meadow.tuck c f k).disjSum univ
lemma pocket (k:ℕ) (i:Meter c f): i∈ tuck k ↔ held i≤k:= by unfold held tuck; rcases i with i|i<;>simp [Meadow.pocket]
abbrev Poet (H:Cash W p a L₀ X o U (c:=c) (f:=f) T R) (Ξ:Lecturer R oo)(oo₀:ℕ) := {z:Vines _ _ // Stir H Ξ oo₀ z} -- dep
-- lemma equivalence preimage support Labeling
lemma baked {k:ℕ} : { i: Vines c f| i.fst ≤ oo₀∧∀ j, (i.2 j)⊆Poetry.tuck k}.Finite:= by
  let T: Finset (Meter c f):= Poetry.tuck k; let a i:=Fintype.piFinset (fun _j : Option (Fin i)=> T.powerset) -- Fintype
  let Y:Finset (Vines c f):= (Finset.range (oo₀+1)).sigma a
  apply Y.finite_toSet.subset; rintro ⟨i,j⟩ ⟨hv,hj⟩; change (Sigma.mk i j)∈Y
  change i≤ oo₀ at hv; apply mem_sigma.mpr; refine ⟨mem_range.mpr (by change i<oo₀+1; omega),?_⟩; simp_rw [a,Fintype.mem_piFinset]; exact fun i=>mem_powerset.mpr (hj i)
lemma tiled (H : Cash W p a L₀ X o U T R) (Ξ:Lecturer R oo)(oo₀:ℕ) (k:ℕ): { i : Poet H Ξ oo₀ | ∀ j,i.val.snd j⊆Poetry.tuck k}.Finite := Set.Finite.subset (baked.preimage (show Set.InjOn (fun p:Poet H Ξ oo₀=>p.val) _ from Subtype.val_injective.injOn)) (fun i hi=> show i.val.1≤ oo₀∧∀ j,i.val.snd j⊆ Poetry.tuck k from ⟨i.property.small,hi⟩)
def calendar (H:Cash W p a L₀ X o U T R) (Ξ:Lecturer R oo)(oo₀:ℕ) (k:ℕ) := (tiled H Ξ oo₀ k).toFinset
lemma tunes (i:Poet H Ξ oo₀) (k:ℕ): i∈ Poetry.calendar H Ξ oo₀ k↔∀ j,i.val.2 j ⊆ Poetry.tuck k:= Set.Finite.mem_toFinset ..
lemma retires (i:Poet H Ξ oo₀) : ∀ᶠ k in atTop,i ∈ Poetry.calendar H Ξ oo₀ k:= by
  have hf j : ∀ᶠ k in atTop, i.val.2 j⊆ Poetry.tuck k:= (eventually_all_finset _).mpr fun u _=> (eventually_ge_atTop (held u)).mono (fun _ he=> (pocket ..).mpr he)
  exact (eventually_all.mpr hf).mono fun k h=> (tunes i k).2 h
abbrev owned (H : Cash W p a L₀ X o U T R) (Ξ: Lecturer R oo) (oo₀:ℕ) (i:Poet H Ξ oo₀): H.fragrances:= vintage i.val i.property
def booths (H : Cash W p a L₀ X o U T R) (Ξ: Lecturer R oo) (oo₀:ℕ) : Poet H Ξ oo₀ ↪ H.fragrances:= ⟨owned H Ξ oo₀,enrollment⟩
lemma entrants (u:H.fragrances) (h:Terrain.Lantern H oo₀ (Poetry.unknown Ξ) u): u∈Set.range (booths H Ξ oo₀):= by
  let k:= topic S Ξ; let B:=radiusB p; let b i:= (u.2 i).val.preimage k k.injective.injOn; have hf i j:j∈b i↔k j∈(u.2 i).val:=Finset.mem_preimage
  have he i: caste Ξ S (b i)=(u.2 i).val:= by
    ext y; constructor
    · intro hy; obtain ⟨x,hx,rfl⟩:=mem_map.mp hy; exact (hf _ _).1 hx
    intro hy; obtain ⟨j,rfl⟩:= Poetry.allure S Ξ _ (h.heart i y hy); exact mem_map_of_mem k ((hf i _).2 hy)
  have hu:=h.members
  have hx i: Seed H Ξ oo₀ (b i):= by
    have hy:=h.travels i; refine ⟨(he i).symm ▸ hy.1,?_,?_⟩
    · rw [show (b i).card=(caste Ξ S (b i)).card from (Finset.card_map ..).symm,he]
      have hz: (u.2 i).val.card≤Height.breadth H u:=single_le_sum (f:=fun i=> (u.2 i).val.card) (fun _ _=> Nat.zero_le _) (mem_univ i); omega
    intro j hj; refine (Nat.cast_le (α:=ℝ)).mp ?_
    have hz : H.shapeW (u.2 i).val≤radiusB p:= (single_le_sum (f:=fun i=>H.shapeW (u.2 i).val) (fun i _=> H.positive_volume _) (mem_univ i)).trans (h.hiatus.le.trans (by exact_mod_cast show Pressure.Stores.till p ≤ radiusB p from Nat.div_le_self ..))
    apply le_trans _ hz
    change _≤ Finset.sum _ _; apply le_trans _ (Finset.single_le_sum (fun v hv=> ?_) ((hf i j).1 hj))
    swap
    · obtain ⟨v,rfl⟩:= allure S Ξ v (h.heart i v hv)
      exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    change (vote R.path j:ℝ)≤_ + (exCharge T R (hook Ξ j):ℝ); exact (Nat.cast_le.mpr (breadthQ Ξ j)).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hb i: (u.2 i)=Poetry.Heir _ (hx i):= Subtype.ext (he i).symm
  have hg: Stir H Ξ oo₀ ⟨u.1,b⟩:= by
    refine ⟨?_,hx,fun hc=> h.participation (Eq.trans ?_ hc)⟩
    · have hi:= Beam.on_one u (fun i=> Finset.card_pos.mpr (h.travels i).1.1); change u.fst≤oo₀; omega
    apply Meadow.movement; intro i j; rw [hb,hb]; apply or_congr; · exact ⟨seed_height _ _,fun h=>Subtype.ext (congr_arg (Poetry.caste Ξ S) h)⟩
    exact Iff.rfl
  refine ⟨⟨⟨u.1,b⟩,hg⟩,?_⟩; change Sigma.mk u.fst _=u; congr 1; exact funext fun i=> (hb i).symm
def shine (z:Poet H Ξ oo₀) := ((Poetry.stampP H Ξ z.val).card:ℝ)⁻¹
def offer (χ:Chi) (z:Poet H Ξ oo₀) (V:Config G c) := -(shine z) * stream H χ V (vintage z.val z.property)
def echoing (H:Cash W p a L₀ X o U T R)(Ξ: Lecturer R oo)(oo₀:ℕ) (χ:Chi) (k:ℕ) (x:Site c) (V:Config G c):= ∑ i∈(calendar H Ξ oo₀ k).filter (fun i=>x∈Poetry.stampP H Ξ i.val), Poetry.offer χ i V
variable (H Ξ oo₀)
def barony (χ:Chi) (k:ℕ) (β γ:ℝ) := Meadow.atlas (echoing H Ξ oo₀ χ k + Meadow.garner T.down T.low β γ (radiusB p) k)
lemma rotates (χ:Chi) (k:ℕ) (β γ:ℝ) (x:Site c) (V:Config G c) (s:Signed) (b:Site c): barony oo₀ H Ξ χ k β γ (Lattice.affine s b x) V= barony oo₀ H Ξ χ k β γ x (pull s b V):=(Meadow.astrolabe _ x V (s,b)).symm

end sow
variable {χ:Chi} {X:ConnectedActivityE6.Target G K} {o: Target.Order G W}
open Song AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
section roll
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (Tq : T'=Deck.re T) (hp:R'.path=R.path) (ha:R'.p= R.p) (hz:R'.beta=R.beta) (x : Site C) (hX:4*roomP X.halo (radiusB p) oo oo₀<c.val) {b ℓ : ℕ}
    {C' d z T'' A B r V' u s₁ a' b' c' d' e' D Z q' :ℝ} -- B conflicts
    (N : Captain I b C' d z T'' A B r V' u m χ) (N' : Captain I' j s₁ a' b' c' d' e' D Z q' ℓ χ) -- note args
    (f' : Config G c) (hV: RG.flags (Pressure.temp p) f'= ∅)
    {Ξ : Lecturer R oo} {Ξ':Lecturer R' oo} (hl:ConcordP (fineP h H hC) Ξ Ξ')(hg:2*(generous 0 (radiusB p) oo+3)<c.val) (h₀:2*(roomP X.halo (radiusB p) oo oo₀+generous X.halo (radiusB p) oo)<c.val)
local notation "R₀" => radiusB p
local notation "D'" => roomP X.halo R₀ oo oo₀
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include hC he Tq hp ha hz hX N N' hV hl hg
lemma due (i : Poet I' Ξ' oo₀) (j:Poet I Ξ oo₀) (heq: j.val=forward (L) i.val) (hr:x∈stampP I' Ξ' i.val):
     offer χ i ((L).low.links f')=offer χ j f':= by
  let f:=f'; let F:=(L).low.links f; let z:=i.val; let w:= j.val
  have hc: RG.flags (Pressure.temp p) F=∅:= by ext i; rw [show i∈RG.flags (Pressure.temp p) F↔_ from Deck.flagged hC f' i (show c.val>4 from (by have hv:= I.laws.data.room.buys; omega)) (Pressure.temp p),hV]; simp -- adjust
  have hf:(stampP I Ξ w).card= (stampP I' Ξ' z).card:= by
    have hy:=entered i.property x hr; unfold w; rw [heq, pitchRoll (Ξ:=Ξ) (Ξ':=Ξ') hC he (I:=I) (I':=I') hp]; exact card_image_of_injOn ((garden hC x (show 2* D' < c.val from (by omega))).mono (Finset.coe_subset.mpr hy))
  let C0:= vintage z i.property; let C1:= vintage w j.property; have ht : stream I χ f C1= I.trainedPool χ f C1:= Eq.symm ((congr_fun (N.permitAverage C1).2.2.2.1 f).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hV]; simp)))
  have hx : stream I' χ F C0= I'.trainedPool χ F C0 := Eq.symm ((congr_fun (N'.permitAverage C0).2.2.2.1 F).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hc]; simp)))
  have hh : 2*D' < c.val:=by omega
  suffices h : I'.trainedPool χ F C0= I.trainedPool χ f C1 by unfold offer; rw [ht,hx,h,show shine j=shine i from (by unfold shine; rw [show (stampP I Ξ j.val).card=_ from hf])]
  obtain ⟨j,Hj⟩:=j; dsimp only at heq; subst j
  unfold Cash.trainedPool Gas.term
  apply congr_arg₂ HDiv.hDiv _ rfl
  apply congr_arg₂ HMul.hMul
  · exact (mana i.property).symm.trans ((receipts hC he (I:=I) x hp z hh (entered i.property x hr) i.property.each).trans (mana Hj))
  apply prod_congr rfl; intro j _
  have hy' := rings (h:=h) hC he x i.val i.property hr hh j
  exact gatherP hC he I' I Tq hp ha hz hl hg x D' (by omega) hy' (engirds x i.val i.property hr j) (i.property.each j).earns f χ hV (i.property.each j).hot (Hj.each j).hot

include h₀
lemma arranges (k:ℕ) : echoing I' Ξ' oo₀ χ k x ((L).low.links f')= echoing I Ξ oo₀ χ k x' f':= by
  let T x i:= x∈stampP I' Ξ' i
  let P:=L; let u:=(Poetry.calendar I' Ξ' oo₀ k).filter (fun i=> x∈stampP I' Ξ' i.val); let v:=(Poetry.calendar I Ξ oo₀ k).filter (fun i=> x'∈stampP I Ξ i.val)
  have hm : 2*(D')<c.val:= by omega
  have hh {i : Poet I' Ξ' oo₀} (hi:i∈u) := stitches (Ξ:=Ξ) hC he (I:=I) (I':=I') x hp i.val i.property (mem_filter.mp hi).2 hm
  let f (i: Poet I' Ξ' oo₀) (hi:i∈u): Poet I Ξ oo₀:=⟨forward P i.val, (hh hi).1⟩
  have hv i: held (aisle P i)= held i := by rcases i with (i|i|i|i)|i <;> rfl
  have ht (z:Vines C F): (∀ j,z.snd j⊆tuck k) ↔ (∀ j,(forward P z).snd j⊆ tuck k):= by
    constructor
    · intro h j i hi; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; rw [pocket,hv,← pocket]; exact h _ (by assumption)
    intro h j i hi; rw [pocket, ← hv,← pocket]; exact h _ (mem_image_of_mem (aisle P) (show i∈z.snd j from hi))
  apply Finset.sum_bij f (fun i hi=> ?_) (fun i hi j hj heq=> ?_) (fun b hb=>?_) (fun i hi=>?_)
  · exact mem_filter.mpr ⟨(tunes _ k).mpr ((ht _).1 ((tunes i k).1 (mem_filter.mp hi).1)), (hh hi).2⟩
  · exact Subtype.ext (inquire hC he x j.val i.val j.property i.property (mem_filter.mp hj).2 (mem_filter.mp hi).2 hm (congr_arg Subtype.val heq))
  ·
    obtain ⟨y,hy,hY,h⟩ := returns (Ξ:=Ξ) (Ξ':=Ξ') hC he x hp b.val (I:=I) (I':=I') b.property (mem_filter.mp hb).2 (show 2*(D'+generous X.halo R₀ oo)<c.val from h₀)
    have hk : (⟨y,hy⟩ : Poet I' Ξ' oo₀)∈u:= mem_filter.mpr ⟨(tunes _ _).2 ((ht _).2 (h.symm ▸ (tunes _ _|>.1 (mem_filter.mp hb).1))),hY⟩; exact ⟨_,hk,Subtype.ext h⟩
  exact due hC he Tq hp ha hz x hX N N' f' hV hl hg i (f i hi) rfl (mem_filter.mp hi).2
lemma replay (β γ' : ℝ) (k:ℕ) : barony oo₀ I' Ξ' χ k β γ' x ((L).low.links f')=barony oo₀ I Ξ χ k β γ' x' f':= by
  let b (θ:Seat c):=echoing I Ξ oo₀ χ k ((Meadow.spin θ).symm x') (θ.view f') + Meadow.garner T.down T.low β γ' R₀ k ((Meadow.spin θ).symm x') (θ.view f')
  unfold barony Meadow.atlas; change _=likely b
  rw [← Meadow.revolving hC b]
  apply congr_arg likely; funext θ
  simp only [b,Pi.add_apply]
  rw [show θ.view ((L).low.links f')=(L).low.links ((Meadow.pinch hC θ).view f') from Meadow.estuary hC f' θ]
  apply congr_arg₂ HAdd.hAdd
  · rw [← Meadow.inverts hC θ]; exact arranges hC he Tq hp ha hz _ hX N N' ((Meadow.pinch hC θ).view f') (Meadow.covers_field (Meadow.pinch hC θ) f' hV) hl hg h₀ k
  rw [← Meadow.inverts hC θ]; subst T'; exact Meadow.garner_pack hC ..
end roll
end YM.PhysicalNext.Repeat.Poetry
