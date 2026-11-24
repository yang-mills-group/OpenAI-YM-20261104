import YM.Contacts.Terrain.Hulls
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Utopian
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Quips
/-!
# Add one legacy E head per fine site to low, pointed canonically. Label depends on torus.
 Actual repr for this stage. Numbers determine holes; not inserting family in gauge integral.
 Conditional regards 'model' assumption (constructed later); separation paid
 via Height cockpit. Unknowns immediate.
 -/
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
structure Lecturer (R: RG.Rep G f) (n:ℕ) where
  place : Site f ↪ ℕ
  site (x) : (R.activities.reg (place x)).site=x
  support (x): (R.activities.reg (place x)).support=neighbors n x
-- `verse(new)=0`. arity & depth gate done BEFORE.
variable (S) (K:Lecturer R n)
abbrev Meter (c f:Side):= Music c f ⊕ Site f
def hook (i:Meter c f):=Sum.elim Mint.note (fun i=> (Sum.inl (.inl (K.place i)):Coat.LogIndex c f)) i
lemma rope : Injective (hook K (c:=c)) := by
  rintro (x|x) (y|y) h <;> unfold hook at h <;> simp only [Sum.elim] at h
  · exact congr_arg Sum.inl (Mint.record h)
  · rcases x with x|x|x|x <;> simp [Mint.note] at h
  · rcases y with y|y|y|y <;> simp [Mint.note] at h
  exact congr_arg Sum.inr (K.place.injective (Sum.inl_injective (Sum.inl_injective h)))
def topic : Meter c f ↪ Head S := ⟨fun i=> .inr (.inr (.inl (hook K i))), fun _i _j h=> rope K (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))⟩
def unknown (i:ℕ) := i∉ Set.range K.place
lemma allure (x:Head S) (h : Beam.Pennies S x ∨ ∃ k:ℕ,¬unknown K k ∧ x=Opacity.key S k) : x∈ Set.range (topic S K):= by
  rcases h with h|⟨k,h,rfl⟩
  · obtain ⟨i,rfl⟩:= (penned S _).1 h; exact ⟨.inl i,rfl⟩
  obtain ⟨i,rfl⟩ : k ∈ Set.range K.place:= Classical.byContradiction h
  exact ⟨.inr i,rfl⟩

def vote (R: PathData G) : Meter c f → ℕ := Sum.elim (verse R) (fun _=>0)
def lobby : Meter c f→ Site c:= Sum.elim (pace S) (S.ratio.parent)
-- bound lobby support.A no budget
variable {S}
lemma breadthQ (i: Meter c f) : vote R.path i≤ exCharge T R (hook K i):= by
  rcases i with i|i; · exact Nat.le_of_eq (Mint.balance ..)
  exact Nat.zero_le _
def generous (l b m:ℕ):= Mint.width l b b + m
lemma habitat (m b:ℕ) (hb:0<b) (T:Tube G S) (i : Site f): S.ratio.parent i∈ areas R T m b (topic S K (Sum.inr i)) ∧ areas R T m b (topic S K (Sum.inr i)) ⊆ neighbors (generous m b n) (S.ratio.parent i):= by
  let V:=neighbors n i; change _∈ regularFoot S.ratio m b R (K.place i) ∧ regularFoot S.ratio m b R (K.place i) ⊆ _; rw [regularFoot,K.support]
  have hx : i∈ V:= (neighbors_mem ..).mpr (separation_self _ ▸ Nat.zero_le _)
  constructor
  · exact halo_subset _ _ (mem_image_of_mem _ (show i∈RG.inspected V from mem_union_left _ hx))
  intro x hx; obtain ⟨z,hz,hx⟩:= halo_spec.mp (inspected_price S.ratio m b V hb (show x∈ enlargement S.ratio m b (inspected V) from hx)); obtain ⟨w,h',rfl⟩:=mem_image.mp hz
  apply (neighbors_mem ..).2
  have he' : separation (S.ratio.parent i) (S.ratio.parent w)≤ n+1:= (Work.E04.parent_separation ..).trans (Nat.add_le_add_right ((neighbors_mem ..).mp h') _)
  apply (separation_triangle _ (S.ratio.parent w) x).trans; unfold generous Mint.width; nlinarith only [hb,he',hx]
lemma domain (m b:ℕ) (hb:0<b) (T:Tube G S) (i:Meter c f) (hi: vote R.path i≤ b): lobby S i∈ areas R T m b (topic S K i) ∧ areas R T m b (topic S K i) ⊆ neighbors (generous m b n) (lobby S i):= by
  rcases i with i|i
  · obtain ⟨he,hz⟩:= centered m b b hb i S T R hi; exact ⟨he,fun x hx=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp (hz hx)).trans (Nat.le_add_right ..))⟩
  exact habitat K _ _ hb T i
abbrev caste (S:StepData c f) := fun z:Finset (Meter c f)=> z.map (topic S K)
lemma frozen (z:Finset (Meter c f)): (caste K S z).toLeft=∅ ∧ Matter.own (caste K S z)=∅ := by
  constructor <;> ext p
  · simp only [mem_toLeft,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:= mem_map.mp h; unfold topic at hx; injection hx
  simp only [own,mem_toLeft,mem_toRight,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:=mem_map.mp h; unfold topic at hx; injection hx with he; injection he
lemma snowy (z:Finset (Meter c f)): roster (caste K S z)= ⟨∅,∅,∅⟩:= by unfold roster; rw [(frozen K z).1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩
lemma posed (z:Finset (Meter c f)) (i j:ℕ) : troupe T R i j (caste K S z):= by
  unfold troupe; rw [snowy,(frozen K z).1,(frozen K z).2]
  constructor
  · constructor
    · simp
    · simp
    simp [Packets.seeds]
  constructor
  · intro _ h; exact False.elim (notMem_empty _ h)
  intro _ h; exact False.elim (notMem_empty _ h)
end YM.PhysicalNext.Repeat.Poetry
