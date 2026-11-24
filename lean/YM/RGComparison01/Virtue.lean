import YM.RGComparison01.Cabinet
import YM.RGComparison01.Selectors

/-!
 # What survives from the REG log

 Ages typed via catalog. Summable extension in publication and actually
 controlled union support. Recycles `Meadow` conventions with honest
 broadenings, does NOT assume ranks small after projection to a new
 torus/germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Cabinet
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L : Side} {ℓ n m b : ℕ} {ι χ : Type} {K : Teller G}
variable {S : StepData c f} {T : Tube G S} {s W a U : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
    {R : RG.Rep G f} {I : Cash W s a L X o U T R} (D : Cabinet ι I b)

-- path/book labels separately.
abbrev Folder (ι : Type) := Finset ι
abbrev Parenthood (ι : Type) := Ursell.Clusters (Folder ι)
abbrev shell (x : Folder ι) := x.map D.ink
abbrev garden (x : Folder ι) := I.unionP (D.shell x)
abbrev ground (p : Parenthood ι) := unionOf D.garden p.2
abbrev Peach (x : Folder ι) := Ac.Spark I.supportP (D.shell x)
lemma orchard (x:Folder ι) : D.garden x = x.biUnion D.foot := by
  ext i; constructor
  · intro h; obtain ⟨k,hk,hx⟩:= mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:=mem_map.mp hk; exact mem_biUnion.mpr ⟨_,hj,hx⟩
  intro h; obtain ⟨k,hk,hx⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨_,mem_map_of_mem D.ink hk,hx⟩
lemma fruit (x:Folder ι) : Peach D x↔Ac.Spark D.foot x:= by unfold Peach foot shell; rw [Finset.map_eq_image]; exact (Meadow.sparkling _ _ x D.ink.injective.injOn).symm
lemma vines (x : Folder ι) : (shell D x).toLeft=∅ ∧ own (shell D x)=∅ := by
  constructor <;> ext p
  · simp only [mem_toLeft,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:=mem_map.mp h; unfold Cabinet.ink at hx; injection hx
  simp only [own,mem_toLeft,mem_toRight,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:=mem_map.mp h; unfold Cabinet.ink at hx; injection hx with ht; injection ht
lemma unstored (x : Folder ι) : roster (shell D x) = ⟨∅,∅,∅⟩ := by unfold roster; rw [(vines D x).1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩
lemma attends (x:Folder ι) (i j:ℕ) : troupe T R i j (shell D x):= by
  unfold troupe; rw [unstored,(vines D x).1,(vines D x).2]
  constructor; · exact ⟨by simp,by simp,by simp [Packets.seeds]⟩
  exact ⟨fun _ h=> False.elim (notMem_empty _ h),fun _ h=> False.elim (notMem_empty _ h)⟩
lemma spot (x : Folder ι) (i : ι) (h:i∈x) : D.site i∈ D.garden x:= mem_biUnion.mpr ⟨_,mem_map_of_mem D.ink h,(D.sails i).1⟩
lemma within (p : Parenthood ι) (i) : D.garden (p.2 i) ⊆ D.ground p:= Finset.subset_biUnion_of_mem (D.garden ∘ p.2) (mem_univ _)
lemma nonempty (x : Folder ι) (h : D.Peach x) : (D.garden x).Nonempty:= by
  obtain ⟨j,hj⟩:= ((fruit D x).1 h).1; exact ⟨_,D.spot x j hj⟩

def pile (x : Folder ι) (h : Peach D x) : I.ThinP := ⟨D.shell x, D.nonempty x h, by rw [D.unstored]⟩
lemma pines (x y : Folder ι) (hx:D.Peach x) (hy:D.Peach y) (h:D.pile x hx = D.pile y hy) : x=y:= Finset.map_injective _ (congr_arg Subtype.val h)

structure Scene (ℓ:ℕ) (z : Parenthood ι) : Prop where
  start : z.fst+1≤ℓ
  photos (i) : (z.2 i).card≤ℓ
  poses i : D.Peach (z.2 i)
  moves : coefficient (blocked D.garden) z.2≠0

abbrev Record (ℓ:ℕ) := {z:Parenthood ι// Scene D ℓ z}
def covers (z:Record D ℓ) : I.fragrances:= ⟨z.val.fst,fun i=> D.pile (z.val.2 i) (z.property.poses i)⟩

lemma stars (p : Record D ℓ) : coefficient (blocked D.garden) p.val.2=coefficient I.seam (covers D p).2:= by
  apply Meadow.movement; intro i j; apply or_congr _ Iff.rfl; exact ⟨fun h=> Subtype.ext (congr_arg D.shell h),D.pines _ _ (p.property.poses i) (p.property.poses j)⟩

def bureau (ℓ:ℕ) : Record D ℓ ↪ I.fragrances := ⟨covers D,fun ⟨⟨k,p⟩,hp⟩ ⟨⟨j,v⟩,hv⟩ h=> by
  change Sigma.mk k _ = Sigma.mk j _ at h; obtain rfl : k=j := congr_arg Sigma.fst h
  injection h with h he
  have h' : p=v:= funext (fun i=>D.pines _ _ (hp.poses i) (hv.poses i) (congr_fun he i)); subst v; rfl⟩

lemma spectators (p : Folder ι) (h : Peach D p) : coverNumber b (D.garden p) ≤ p.card:= by
  refine (Ac.cover _ _ h).trans ((sum_le_sum (g:=fun _=> 1) (fun i hi=>?_)).trans_eq ?_)
  · obtain ⟨i,hi,rfl⟩:=mem_map.mp hi; let x:=D.site i; have he : neighbors b x=halo b ({x}:Support c):= by ext i; simp only [halo_spec,neighbors_mem]; simp
    have hv : Lattice.covers b (D.foot i) {x}:= ⟨he ▸ (D.sails i).2,Corona.ship_halo _ (fun i hi j hj=>by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hv).trans_eq (card_singleton _)
  rw [sum_const]; simp only [nsmul_eq_mul,mul_one,shell,Finset.card_map,Nat.cast_id]
lemma saber (p: Cabinet.Record D ℓ) : coverNumber b (D.ground p.val) ≤ ℓ*ℓ:= by
  let z:=covers D p; have hx := connected_pay I.seam I.smallAt b I.testS z.2 zero_le_one (show coefficient I.seam z.2≠0 from
    (stars D p) ▸ p.property.moves)
  unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have h i : (coverNumber b (I.smallAt (z.2 i)):ℝ)≤ℓ:= by
    exact_mod_cast (D.spectators _ (p.property.poses i)).trans (p.property.photos i)
  have he : (coverNumber b (D.ground p.val):ℝ) ≤ ℓ * (ℓ:ℝ):= by
    refine le_trans hx ((Finset.sum_le_sum (fun i _=> h i)).trans ?_); rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (show ((z.fst+1:ℕ):ℝ)≤ℓ from (by exact_mod_cast p.property.start)) (by positivity)
  exact_mod_cast he

def garage (b ℓ : ℕ) := (ℓ*ℓ)*(4*b+2)+2*b
lemma extent (p : Cabinet.Record D ℓ) (x:Site c) (hx : x∈D.ground p.val) : D.ground p.val ⊆ neighbors (garage b ℓ) x := by
  intro i hi; apply (neighbors_mem ..).2; apply (Corona.extent _ b hx hi).trans
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (saber D p)) _

abbrev Age (k : ℕ) (x : Cabinet.Record D ℓ) := ∀ i j,j∈x.val.2 i→D.hold j≤k
def stand (k : ℕ) := (D.finite k).toFinset
lemma parchment (ℓ k : ℕ) : {i: Cabinet.Record D ℓ | Age D k i}.Finite:= by
  let s:= (stand D k).powerset
  let F : Finset (Parenthood ι) := (Finset.range ℓ).sigma (fun i=> Fintype.piFinset fun _ : Option (Fin i) => s)
  apply Set.Finite.subset ((F.finite_toSet).preimage (show Set.InjOn (fun p:Record D ℓ=>p.val) _ from Subtype.val_injective.injOn))
  rintro ⟨⟨a,b⟩,h⟩ hp; change (Sigma.mk a b) ∈ F; refine mem_sigma.mpr ⟨mem_range.mpr h.start,?_⟩
  apply Fintype.mem_piFinset.mpr; intro i
  exact mem_powerset.mpr (fun j hj=> by apply (D.finite k).mem_toFinset.mpr; exact hp i j hj)

def podium (ℓ k : ℕ) := (D.parchment ℓ k).toFinset
lemma posted (k : ℕ) (x:Record D ℓ) : x ∈ D.podium ℓ k ↔ Age D k x:= Set.Finite.mem_toFinset _
lemma interns (p : Record D ℓ) : ∀ᶠ k in atTop,p∈ D.podium ℓ k:= by
  have h i : ∀ᶠ k in atTop,∀ j∈p.val.2 i,D.hold j≤k:= (eventually_all_finset _).mpr (fun j _=> eventually_ge_atTop _)
  exact (eventually_all.mpr h).mono (fun k hv=> (D.posted k p).2 hv)
end YM.RGComparison01.Cabinet
