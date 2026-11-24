import YM.RG01Estimate.AtlasMint
/-!
 # Short all-grade catalogue. Anchored cub budget for bearing appointments.
 Reusable lexical; countable agenda, not taper across volume. Keeps all matches including
 angular labels; equality for ANY reading on H by Fate cubes. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {Γ:Type} {c f C F L'' : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {S:StepData c f} {T : Tube G S} {R: RG.Rep G f}
    {Y:ConnectedActivityE6.Target G K} {ρ W U v:ℝ}{o: Target.Order G W}
variable (H: Cash W ρ v L'' Y o U T R)(L: Lex Γ f) (m:ℕ)

abbrev arbor (p:hall Γ c f):= H.unionP (songs (S:=S) L p)
abbrev arborX (p:Sons Γ c f):= unionOf (Evoc.arbor H L) p.2
structure Kind (p:hall Γ c f): Prop where
   active : Ac.Spark H.supportP (songs (S:=S) L p)
   size : p.card < m
   vote (i): i∈p → fit R.path i≤ radiusB ρ

structure Admit (p:Sons Γ c f) : Prop where
   count : p.fst+1< m
   hot i : Kind H L m (p.2 i)
   glow : Ursell.coefficient (blocked (arbor H L)) p.2≠0
local notation "B" => radiusB ρ
-- width deterministic depends on lookahead
lemma term (p:hall Γ c f)(h:Kind H L m p): (arbor H L p).Nonempty:= by
   obtain ⟨x,hx⟩:= h.active.1
   obtain ⟨j,hj⟩ : (H.supportP x).Nonempty:= by
      obtain ⟨j,hj,rfl⟩:= mem_map.mp hx; rcases j with j|j
      · exact exChart S T R B Y.halo (.inl (.inl (L j))) -- defeq? exChart accepts T,p genus Long
      exact exChart S T R B Y.halo (Mint.note j)
   exact ⟨j,mem_biUnion.mpr ⟨x,hx,hj⟩⟩

def Atom (p:hall Γ c f)(h:Kind H L m p):H.ThinP:= ⟨songs L p, Evoc.term H L m p h,by rw [white]⟩
lemma atom_inj (p q:hall Γ c f)(h:Kind H L m p)(h': Kind H L m q) (he: Atom H L m p h=Atom H L m q h'):p=q:= Finset.map_injective (mint S L) (congr_arg Subtype.val he)

def issue (p:Sons Γ c f) (h:Admit H L m p): H.fragrances:= ⟨p.1,fun i=>Atom H L m _ (h.hot i)⟩
abbrev flagraph:= {p:Sons Γ c f // Admit H L m p}
def cask : flagraph H L m ↪ H.fragrances:= ⟨fun i=> issue H L m i.val i.property,fun i j hij=> by
    obtain ⟨⟨i,v⟩,hi⟩:=i; obtain ⟨⟨j,w⟩,hj⟩:=j; change Sigma.mk i _= Sigma.mk j _ at hij
    obtain rfl : i=j:= congr_arg Sigma.fst hij
    injection hij with he hh
    have hf:v=w:= funext fun k=> atom_inj H L m _ _ (hi.hot k) (hj.hot k) (congr_fun hh k)
    cases hf; rfl ⟩
lemma radiant (p:Sons Γ c f)(h:Admit H L m p): coefficient (blocked (arbor H L)) p.2=coefficient H.seam (issue H L m p h).2:= by
    apply Meadow.movement; intro i j; apply or_congr _ Iff.rfl
    exact ⟨fun he=> Subtype.ext (congr_arg (songs L) he),fun he=> atom_inj H L m _ _ (h.hot i) (h.hot j) he⟩ -- needs types

lemma scroll (E:Set ℕ)(h:Record Γ S R L E) (v:H.fragrances): Fate.showcase E m v↔ v∈Set.range (cask H L m):= by
    constructor
    · intro ht
      let f₁ i:= (v.2 i).val
      let g i:= (f₁ i).preimage (mint S L) (mint S L).injective.injOn
      have hh i: (songs (S:=S) L (g i))=f₁ i:= by
         ext j; constructor
         · intro h; obtain ⟨p,hp,rfl⟩:= mem_map.mp h; exact Finset.mem_preimage.mp hp
         intro H'; obtain ⟨k,hk,_⟩:= (Evoc.contents H L h _).2 (ht.driver _ _ H'); rw [← hk]; apply Finset.mem_map_of_mem; exact Finset.mem_preimage.mpr (hk ▸ H')
      have hK i: Kind H L m (g i):= by
          refine ⟨(hh i).symm ▸ ht.alive i,?_,fun j hj=>?_⟩ -- rewrite maybe issue
          · exact (show (g i).card=(f₁ i).card from (Finset.card_map _).symm.trans (congr_arg _ (hh i))).trans_lt (ht.limited _)
          exact (fun ⟨k,hk,H⟩=> (mint S L).injective hk ▸ H) ((contents H L h _).2 (ht.driver _ _ (Finset.mem_preimage.mp hj)))
      let u:Sons Γ c f:= ⟨v.1,g⟩
      have hx: v.2=fun i=> Atom H L m (g i) (hK i):= funext fun i=> Subtype.ext (hh i).symm
      have he: Admit H L m u:= by
          refine ⟨ht.rows,hK,fun hp=> ht.possible ?_⟩
          change coefficient (blocked (arbor H L)) g=0 at hp
          rw [hx]; rw [← hp]; symm; apply Meadow.movement; intro i j; apply or_congr _ Iff.rfl; exact ⟨fun he=> Subtype.ext (congr_arg (songs L) he),atom_inj H L m _ _ (hK i) (hK j)⟩
      exact ⟨⟨u,he⟩,congr_arg (Sigma.mk v.1) hx.symm⟩
    rintro ⟨⟨p,hp⟩,rfl⟩
    refine ⟨radiant H L m p hp ▸ hp.glow,hp.count,fun i=> (hp.hot i).active,fun i=>?_,fun i j hj=>?_⟩
    · change (songs (S:=S) L (p.2 i)).card< m; unfold songs; rw [card_map]; exact (hp.hot i).size
    obtain ⟨k,hk,rfl⟩:=mem_map.mp hj; exact (contents H L h _).1 ⟨k,rfl,(hp.hot i).vote _ hk⟩

section hue
variable {d:ℕ}(t:hall Γ c f)(ht:Kind H L m t) (hp:StageMask R S L d)

def optic (l b d:ℕ) := Mint.width l b (b+d)
local notation "Z" => optic Y.halo B d

include hp ht
lemma positioned (i:Header Γ c f) (h : i∈ t) : aisle S i ∈ (arbor H L t):= by
   have he:=H.laws.data.room.sight.1; exact mem_biUnion.mpr ⟨mint S L i,mem_map_of_mem _ h,(location L hp T (show 0<B from lt_of_lt_of_le (by norm_num) he) i (ht.vote _ h) (m:=Y.halo)).1⟩
lemma location_cost : coverNumber (Z) (arbor H L t) ≤ m:= by
  refine le_trans (Ac.cover _ _ ht.active) ((Finset.sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨p,hy,rfl⟩:= mem_map.mp hi; let P:= aisle S p; let J:= optic Y.halo B d
    have hh : H.supportP (mint S L p) ⊆ halo (Z) {P} := (location L hp T (show 0<B from lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) p (ht.vote _ hy)).2.trans (show neighbors (Z) P ⊆ _ from fun i hi=> halo_spec.mpr ⟨_,mem_singleton_self _,(neighbors_mem ..).mp hi⟩)
    refine (Corona.list_cost (D:={P}) _ ⟨hh, Corona.ship_halo _ (fun i hi j hj=>by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩).trans_eq (card_singleton _)
  simp only [Finset.sum_const,songs, card_map,smul_eq_mul,mul_one]; exact ht.size.le

omit ht
variable {t}
lemma wide {p} (h : Admit H L m p) : coverNumber (Z) (arborX H L p) ≤ m*m:= by
  let v':=issue H L m p h
  have hx:= connected_pay H.seam H.smallAt (Z) H.testS v'.2 zero_le_one (show coefficient H.seam v'.2≠0 from radiant H L m p h ▸ h.glow)
  unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx
  have hh i : (coverNumber Z (H.smallAt (v'.2 i)):ℝ) ≤ (m:ℝ):= by exact_mod_cast location_cost H L m (p.2 i) (h.hot i) hp
  have he:(coverNumber Z (arborX H L p):ℝ) ≤ (m:ℝ)*m:= by
     apply hx.trans; refine (sum_le_sum (fun i hi=> hh i)).trans ?_
     rw [sum_const,card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show v'.1+1 ≤ m from h.count.le)) (by positivity)
  exact_mod_cast he

def house (l b d m : ℕ) := 2*optic l b d + m*m*(4*optic l b d+2)
lemma within (x:Site c) {p} (h : Admit H L m p) (hx : x∈arborX H L p) : arborX H L p ⊆ neighbors (house Y.halo B d m) x:= by
  intro i hi; apply (neighbors_mem ..).2; have he:= wide H L m hp h
  apply le_trans (Corona.extent _ (Z) hx hi); unfold house; rw [add_comm (2*_ : ℕ)]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ he) _ -- orientation?
end hue
end YM.RG01Estimate.Evoc
