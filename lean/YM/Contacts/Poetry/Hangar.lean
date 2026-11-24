import YM.Contacts.Poetry.Setup
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Mantel
/-! Extends Meadow/Mantel for arbitrary degrees & labelled E-alignment. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L : Side} {M m n j : ℕ} {P : Teller G}
variable {S : StepData c f} {T : Tube G S} {p : ℝ} {R : RG.Rep G f}
    {a v W q A : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} (H : Cash W p a L Q o A T R) {χ : Chi}
local notation "B" => radiusB p
variable (Ξ:Lecturer R m)
abbrev Park (c f:Side):= Finset (Meter c f)
abbrev Vines (c f:Side) := Ursell.Clusters (Park c f) -- nameslobby check
abbrev ground (p:Park c f):= H.unionP (caste Ξ S p)
abbrev stampP (z:Vines c f):= unionOf (ground H Ξ) z.2 -- check
structure Seed (n:ℕ) (p:Park c f) : Prop where
  hot : Ac.Spark H.supportP (caste Ξ S p)
  sizes : p.card≤ n
  earns i : i∈p → vote R.path i≤B -- p rename
structure Stir (n:ℕ) (z:Vines c f) : Prop where
  small : z.fst≤ n
  each i : Seed H Ξ n (z.2 i)
  moves : coefficient (blocked (ground H Ξ)) z.2≠0
variable {H Ξ}
lemma family_ne {x : Park c f} (hq:Seed H Ξ n x) : x.Nonempty:= by obtain ⟨p,hp⟩:= hq.hot.1; obtain ⟨i,hi,rfl⟩:=mem_map.mp hp; exact ⟨i,hi⟩
lemma ground_ne {x} (hq:Seed H Ξ n x): (ground H Ξ x).Nonempty:= by
  obtain ⟨i,hi⟩:= family_ne hq; have hz:= Poetry.domain Ξ Q.halo B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) T i (hq.earns i hi)
  exact ⟨lobby S i,Finset.mem_biUnion.mpr ⟨_,mem_map_of_mem _ hi,hz.1⟩⟩
lemma centers {x} (hq:Seed H Ξ n x) {i} (hi:i∈x): lobby S i∈ground H Ξ x:= Finset.mem_biUnion.mpr ⟨topic S Ξ i, mem_map_of_mem _ hi, (Poetry.domain Ξ Q.halo B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) T i (hq.earns i hi)).1⟩
def Heir (y : Park c f) (ht : Seed H Ξ n y) : H.ThinP := ⟨caste Ξ S y,ground_ne ht,by rw [Poetry.snowy]⟩
lemma seed_height {x y:Park c f} (he:Seed H Ξ n x) (hp:Seed H Ξ n y) (h:Heir x he=Heir y hp): x=y:= Finset.map_injective (topic S Ξ) (congr_arg Subtype.val h)
def vintage (z:Vines c f) (hz:Stir H Ξ n z): H.fragrances:= ⟨z.1,fun i=>Heir (z.2 i) (hz.each i)⟩
lemma enrollment : Injective (fun i : {z:Vines c f// Stir H Ξ n z}=> vintage i.val i.property):= by
  rintro ⟨⟨i,z⟩,hp⟩ ⟨⟨j,k⟩,hx⟩ he
  change Sigma.mk i _=Sigma.mk j _ at he; obtain rfl : i=j:= congr_arg Sigma.fst he
  injection he with he hh
  have h': z=k:= funext fun i=> seed_height (hp.each i) (hx.each i) (congr_fun hh i)
  cases h'; rfl
lemma mana {p : Vines c f} (h : Stir H Ξ n p): coefficient (blocked (ground H Ξ)) p.2=coefficient H.seam (vintage p h).2:= by
  apply Meadow.movement; intro i j; apply or_congr _ Iff.rfl
  exact ⟨fun he=> Subtype.ext (congr_arg (caste Ξ S) he),seed_height (h.each i) (h.each j)⟩

lemma your {z} (i:Option (Fin z.fst)): ground H Ξ (z.2 i) ⊆ stampP H Ξ z:= Finset.subset_biUnion_of_mem (ground H Ξ ∘ z.2) (mem_univ _)

local notation "D" => generous Q.halo B m
-- diameter via coverNumber, cluster, startup uses R covariance floor
lemma cover_loc {z} (h : Seed H Ξ n z): coverNumber D (ground H Ξ z) ≤ n:= by
  set A:= caste Ξ S z
  refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨i,hi,rfl⟩:=mem_map.mp hi; have hx:=h.earns i (by assumption)
    let p:= lobby S i
    have he:neighbors D p=halo D ({p}: Finset _):= by ext i; simp only [halo_spec,neighbors_mem]; simp only [mem_singleton]; grind
    have hp : covers D (H.supportP (topic S Ξ i)) {p}:= ⟨he ▸ (Poetry.domain Ξ Q.halo B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) T i hx).2, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  simp only [sum_const,smul_eq_mul,mul_one,Poetry.caste, Finset.card_map]; exact h.sizes
lemma wages {z} (h : Stir H Ξ n z) : coverNumber D (stampP H Ξ z) ≤ n*(n+1) := by
  let p:=vintage z h
  have hx:= connected_pay H.seam H.smallAt D H.testS p.2 zero_le_one (show coefficient H.seam p.2≠0 from mana h ▸ h.moves)
  unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have h(i): (coverNumber D (H.smallAt (p.2 i)):ℝ)≤ n:= by exact_mod_cast cover_loc (h.each i)
  have he:(coverNumber D (stampP H Ξ z):ℝ)≤ n*(n+1):= by
    refine le_trans hx ((Finset.sum_le_sum (fun i _=> h i)).trans ?_)
    rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin]; push_cast
    rw [mul_comm]; gcongr; exact_mod_cast (show p.fst≤n from ‹Stir H Ξ n z›.small)
  exact_mod_cast he

def roomP (l b m n:ℕ) := n*(n+1)*(4*generous l b m+2)+2*generous l b m
lemma entered {z} (h : Stir H Ξ n z) (x:Site c) (hx:x∈ stampP H Ξ z): stampP H Ξ z ⊆ neighbors (roomP Q.halo B m n) x:= by
  intro i hi; apply (neighbors_mem ..).2
  have he := wages h; apply (Corona.extent _ D hx hi).trans; unfold roomP; exact (add_le_add_left (Nat.mul_le_mul_right _ he) (2*_)).trans_eq (by ring)
end YM.PhysicalNext.Repeat.Poetry
