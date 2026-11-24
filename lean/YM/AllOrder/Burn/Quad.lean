import YM.AllOrder.Burn.Wrap

/-! Adapt Cursor for E

# Young molecule catalogue: every Seed below cover-cost

For marks-free teen with E=0. For books with modeled analytic E, will
supplement with atoms from that section. All allowed Crew here keep true
pillar at SO: invoice available irrespective of upper strength, not asking
for classifiable exactly young. The backwards solve uses wider Micro bound.
Generalizations of Meadow M6. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m π: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "D" => Mint.width X.halo (radiusB p) (2*radiusB p)
open Meadow (Park)
section pure
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} (H : Cash W p a L₀ X o U T R) {ψv : Locale G} (R₀: Seed R ψv)
abbrev clan (m:ℕ) : Finset (Mandala c f):= Finset.disjSum (Meadow.tuck m) Finset.univ
abbrev thing (p:Yard c f): Support c:= H.unionP (stages S R₀.model p)
structure Crew (π m:ℕ) (v : Yard c f) : Prop where
  radius: R.p.B≤2*B
  hot : Ac.Spark H.supportP (stages S R₀.model v)
  sizes : v.card≤π
  earns : ∀ i∈v,ageV R.path i≤B
  slots : v⊆clan m

def parkable (π m:ℕ) : Finset (Yard c f):=(clan m).powerset.filter (Crew H R₀ π m)
lemma parkable_mem (i : Yard c f): i∈parkable H R₀ π m ↔ Crew H R₀ π m i := by unfold parkable; rw [mem_filter,mem_powerset]; exact ⟨And.right, fun h=> ⟨h.slots,h⟩⟩

variable {R₀ H}
lemma center_ticket {v: Yard c f} (h: Crew H R₀ π m v) (i) (hp:i∈v) : stepsV S i∈ thing H R₀ v:= mem_biUnion.mpr ⟨spin S R₀.model i, mem_map_of_mem _ hp, (Burn.footing R₀ h.radius i (h.earns i hp)).1⟩

def activeM {v:Yard c f} (ht : Crew H R₀ π m v) : H.ThinP:= ⟨stages S R₀.model v, by
   obtain ⟨p,hp⟩:= ht.hot.1; obtain ⟨i,hi,rfl⟩:= mem_map.mp hp; exact ⟨stepsV S i,center_ticket ht i hi⟩, by rw [unbound]⟩
lemma crewing {v : Yard c f} (h : Crew H R₀ π m v): coverNumber D (thing H R₀ v) ≤ π:= by
  refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨i,hi',rfl⟩:=mem_map.mp hi; have hx:=Burn.footing (H:=H) R₀ h.radius i (h.earns _ hi'); let z:= stepsV S i
    have he:neighbors D z=halo D ({z}: Finset _):= by ext i; simp only [halo_spec,neighbors_mem]; simp only [mem_singleton]; grind
    have hp : covers D (H.supportP (spin S R₀.model i)) {z}:= ⟨he ▸ hx.2, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  simpa only [sum_const,smul_eq_mul,mul_one,stages, Finset.card_map] using! h.sizes

def needleP (H : Cash W p a L₀ X o U T R) (R₀:Seed R ψv) (π m:ℕ) : (parkable H R₀ π m) ↪ H.ThinP:= ⟨fun i=> activeM ((parkable_mem ..).1 i.property), fun i j h=> Subtype.ext (Finset.map_injective (spin S R₀.model) (congr_arg Subtype.val h))⟩
def steady (H : Cash W p a L₀ X o U T R) (R₀:Seed R ψv) (π m:ℕ) := Finset.univ.map (needleP H R₀ π m)
lemma steady_mem {z} : z∈steady H R₀ π m ↔ ∃ (i:Yard c f), Crew H R₀ π m i ∧ z.val=stages S R₀.model i := by
  constructor
  · intro hi; obtain ⟨i,-,rfl⟩:=mem_map.mp hi; exact ⟨_,(parkable_mem H R₀ _).1 i.property,rfl⟩
  rintro ⟨i,h,r⟩; exact mem_map.mpr ⟨⟨_, (parkable_mem ..).2 h⟩,mem_univ _,Subtype.ext r.symm⟩
lemma check_steady : High.Upper (steady H R₀ π m) π D := by
  intro i hi; obtain ⟨v,h,r⟩:= steady_mem.1 hi
  rw [show i=activeM h from Subtype.ext r]; exact crewing h
lemma pursuit (χ : Chi) (k:ℕ) (hε: R.p.B ≤ 2*radiusB p) (z:H.fragrances) (hu : ¬ Height.burnoff H (Set.range R₀.model) k z) (V : Config G c) (hv: stream H χ V z≠0) : ∀ᶠ i in atTop,z∈High.strands (alt k) (steady H R₀ (alt k) i):= by
  obtain ⟨hπ,ht,hK⟩:= Height.bodies k χ z hu V hv; have hr : coefficient H.seam z.2 ≠ 0:=fun h=>hv (by unfold stream Gas.term; rw [h,zero_mul,zero_div])
  have hp i p (h:p∈(z.2 i).val): p∈Set.range (spin S R₀.model):= (disced ..).2 ((hK i).2.2 p h)
  have ht : ∀ j, H.shapeW (z.2 j).val≤ B:= fun j=> (single_le_sum (f:=fun i=>H.shapeW (z.2 i).val) (fun i _=> H.positive_volume _) (mem_univ j)).trans (ht.le.trans (by exact_mod_cast show Pressure.Stores.till p≤ B from Nat.div_le_self ..))
  suffices hV : ∀ i : Option (Fin z.fst), ∀ᶠ k' in atTop, z.2 i∈ steady H R₀ (alt k) k' from (eventually_all.mpr hV).mono fun k h=> (High.runIn ..).2 ⟨hπ.le,h,hr⟩
  intro i
  let f':= spin S R₀.model; let y:= (z.2 i).val; let b:= y.preimage f' f'.injective.injOn; have hf (i) : i∈b↔ f' i∈y:= Finset.mem_preimage
  have hx : stages S R₀.model b=y:= by
    ext w; constructor; · intro hw; obtain ⟨p,h,rfl⟩:=mem_map.mp hw; exact (hf _).1 h
    intro h; obtain ⟨q,rfl⟩:= hp i w h; exact mem_map_of_mem f' ((hf _).2 h)
  have hs n (ht:n∈b) : ∀ᶠ k in atTop,n∈ clan k:= by cases n with
    | inl v=> exact (eventually_ge_atTop (Meadow.held v)).mono fun _ h=> Finset.inl_mem_disjSum.mpr ((Meadow.pocket ..).2 h)
    | inr v=> exact Eventually.of_forall (fun _=> Finset.inr_mem_disjSum.mpr (Finset.mem_univ _))
  filter_upwards [(eventually_all_finset b).mpr hs] with k h; refine steady_mem.2 ⟨b,⟨hε,hx.symm ▸ (hK i).1,?_,?_,fun j hj=>h j hj⟩,hx.symm⟩
  · refine Eq.trans_le (b:= y.card) ?_ ((hK i).2.1); rw [← hx,stages,card_map]
  intro v hv; rcases v with v|v; swap; · exact Nat.zero_le _
  refine (Nat.cast_le (α:=ℝ)).1 (le_trans ?_ (ht i)); apply le_trans _ (Finset.single_le_sum (fun x hy=> ?_) ((hf _).1 hv))
  swap
  · obtain ⟨w,rfl⟩:= hp i x hy; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  change _≤_ + (exCharge T R (Mint.note v):ℝ); rw [← Mint.balance T R v]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
end pure
end YM.AllOrder.Burn
