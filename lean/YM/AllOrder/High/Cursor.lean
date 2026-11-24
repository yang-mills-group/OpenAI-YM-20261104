import YM.AllOrder.High.Cluster

/-!
# Young molecule catalogue: every Seed below cover-cost

For marks-free teen with E=0. For books with modeled analytic E, will
supplement with atoms from that section. All allowed Crew here keep true
pillar at SO: invoice available irrespective of upper strength, not asking
for classifiable exactly young. The backwards solve uses wider Micro bound.
Generalizations of Meadow M6. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m π: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "D" => Mint.width X.halo (radiusB p) (radiusB p)
open Meadow (Park)
section pure
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} (H : Cash W p a L₀ X o U T R)

structure Crew (π m:ℕ) (v : Meadow.Park c f) : Prop where
  hot : Ac.Spark H.supportP (hatch S v)
  sizes : v.card≤π
  earns : ∀ i∈v,verse R.path i≤B
  slots : v⊆Meadow.tuck m

def parkable (π m:ℕ) : Finset (Meadow.Park c f):=(Meadow.tuck m).powerset.filter (Crew H π m)
lemma parkable_mem (i : Meadow.Park c f): i∈parkable H π m ↔ Crew H π m i := by unfold parkable; rw [mem_filter,mem_powerset]; exact ⟨And.right, fun h=> ⟨h.slots,h⟩⟩

variable {H}
lemma rent (z : Music c f) (h : verse R.path z ≤ B) : pace S z∈ H.supportP (disc S z) ∧ H.supportP (disc S z)⊆ neighbors D (pace S z):= centered X.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) z S T R h
lemma center_ticket {v: Meadow.Park c f} (h: Crew H π m v) (i) (hp:i∈v) : pace S i∈ Meadow.ground H v:= mem_biUnion.mpr ⟨disc S i, mem_map_of_mem _ hp, (rent i (h.earns i hp)).1⟩

def activeM {v:Meadow.Park c f} (ht : Crew H π m v) : H.ThinP:= ⟨hatch S v, by
   obtain ⟨p,hp⟩:= ht.hot.1; obtain ⟨i,hi,rfl⟩:= mem_map.mp hp; exact ⟨pace S i,center_ticket ht i hi⟩, by rw [Mint.unrostered]⟩
lemma crewing {v : Meadow.Park c f} (h : Crew H π m v): coverNumber D (Meadow.ground H v) ≤ π:= by
  refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨i,hi',rfl⟩:=mem_map.mp hi; have hx:=rent (H:=H) i (h.earns _ hi'); let z:= pace S i
    have he:neighbors D z=halo D ({z}: Finset _):= by ext i; simp only [halo_spec,neighbors_mem]; simp only [mem_singleton]; grind
    have hp : covers D (H.supportP (Mint.disc S i)) {z}:= ⟨he ▸ hx.2, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  simpa only [sum_const,smul_eq_mul,mul_one,Mint.hatch, Finset.card_map] using! h.sizes

def needleP (H : Cash W p a L₀ X o U T R) (π m:ℕ) : (parkable H π m) ↪ H.ThinP:= ⟨fun i=> activeM ((parkable_mem ..).1 i.property), fun _i _j h=> Subtype.ext (Finset.map_injective (disc S) (congr_arg Subtype.val h))⟩
def steady (H : Cash W p a L₀ X o U T R) (π m:ℕ) := Finset.univ.map (needleP H π m)
lemma steady_mem {z} : z∈steady H π m ↔ ∃ (i:Meadow.Park c f), Crew H π m i ∧ z.val=hatch S i := by
  constructor
  · intro hi; obtain ⟨i,-,rfl⟩:=mem_map.mp hi; exact ⟨_,(parkable_mem H _).1 i.property,rfl⟩
  rintro ⟨i,h,r⟩; exact mem_map.mpr ⟨⟨_, (parkable_mem ..).2 h⟩,mem_univ _,Subtype.ext r.symm⟩
lemma check_steady : Upper (steady H π m) π D := by
  intro i hi; obtain ⟨v,h,r⟩:= steady_mem.1 hi
  rw [show i=activeM h from Subtype.ext r]; exact crewing h
lemma pursuit (χ : Chi) (he : ∀ i,R.activities.E i=0) (z:H.fragrances) (hu : ¬ Height.tiredV H π z) (V : Config G c) (hv: stream H χ V z≠0) : ∀ᶠ k in atTop,z∈strands π (steady H π k):= by
  obtain ⟨hπ,ht,hK⟩:= Height.children χ z hu V hv; have hr : coefficient H.seam z.2 ≠ 0:=fun h=>hv (by unfold stream Gas.term; rw [h,zero_mul,zero_div])
  have hp i p (h : p∈ (z.2 i).val): Beam.Pennies S p:= by
    rcases (hK i).2.2 p h with hy|⟨j,rfl⟩
    · exact hy
    exact (hv (congr_fun (Height.noLines χ z i j h (he j)) V)).elim
  have ht : ∀ j, H.shapeW (z.2 j).val≤ B:= fun j=> (single_le_sum (f:=fun i=>H.shapeW (z.2 i).val) (fun i _=> H.positive_volume _) (mem_univ j)).trans (ht.le.trans (by exact_mod_cast show Pressure.Stores.till p≤ B from Nat.div_le_self ..))
  suffices hV : ∀ i : Option (Fin z.fst), ∀ᶠ k in atTop, z.2 i∈ steady H π k from (eventually_all.mpr hV).mono fun k h=> (runIn ..).2 ⟨hπ.le,h,hr⟩
  intro i
  let f':= disc S; let y:= (z.2 i).val; let b:= y.preimage f' f'.injective.injOn; have hf (i) : i∈b↔ f' i∈y:= Finset.mem_preimage
  have hx : hatch S b=y:= by
    ext w; constructor; · intro hw; obtain ⟨p,h,rfl⟩:=mem_map.mp hw; exact (hf _).1 h
    intro h; obtain ⟨q,rfl⟩:= (penned ..).1 (hp i w h); exact mem_map_of_mem f' ((hf _).2 h)
  have hs n (ht:n∈b) : ∀ᶠ k in atTop,n∈ Meadow.tuck k:= (eventually_ge_atTop (Meadow.held n)).mono fun _ h=> (Meadow.pocket ..).2 h
  filter_upwards [(eventually_all_finset b).mpr hs] with k h; refine steady_mem.2 ⟨b,⟨hx.symm ▸ (hK i).1,?_,?_,fun j hj=>h j hj⟩,hx.symm⟩
  · refine Eq.trans_le (b:= y.card) ?_ ((hK i).2.1); rw [← hx,hatch,card_map]
  intro v hv; refine (Nat.cast_le (α:=ℝ)).1 (le_trans ?_ (ht i)); apply le_trans _ (Finset.single_le_sum (fun x hy=> ?_) ((hf _).1 hv))
  swap
  · obtain ⟨w,rfl⟩:= (penned ..).1 (hp i x hy); exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  change _≤_ + (exCharge T R (note v):ℝ); rw [Mint.balance T R v]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
end pure
end YM.AllOrder.High
