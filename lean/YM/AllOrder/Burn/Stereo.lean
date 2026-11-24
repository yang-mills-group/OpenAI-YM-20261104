import YM.AllOrder.High.Cursor
import YM.AllOrder.Burn.Cooling
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Quips
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
open Till
-- Section carrier: reach model specified at ALL error & pure calls too. Choose sensors.Scope.Impulse payer elsewhere.
abbrev Locale (G:Gauge) := ∀ n:Side,Trio.Offer G n
structure Seed (R:RG.Rep G f)(v:Locale G) where
 model : Site f ↪ ℕ
 reg (i:Site f) : (R.activities.reg (model i)).support=court i R.p.B ∧ (R.activities.reg (model i)).site=i
 value (i:Site f) : R.activities.E (model i)=v f i
 off : Plateau.gardenfold R.p.B v

abbrev Mandala (c f: Side):= Music c f ⊕ Site f
abbrev Yard (c f: Side):= Finset (Mandala c f)
-- embedding
variable (S:StepData c f)
def scratch (U: Site f ↪ ℕ) (s:Mandala c f) : ConnectedActivityE6.Coat.LogIndex c f := s.elim note (fun s=> .inl (.inl (U s)))
lemma distinctive (U: Site f ↪ ℕ) : Injective (scratch (c:=c) U):= by
 rintro (x|x) (y|y) hx; exact congr_arg Sum.inl (record hx); have hh : note x ≠ Sum.inl (Sum.inl (U y)):= (by rcases x with x|x|x|x <;> simp [Mint.note]); exact False.elim (hh hx)
 have hh : note y ≠ Sum.inl (Sum.inl (U x)):= (by rcases y with y|y|y|y <;> simp [Mint.note]); exact False.elim (hh hx.symm)
 exact congr_arg Sum.inr (U.injective (Sum.inl_injective (Sum.inl_injective hx))) -- load order maybe multiline

def spin (U:Site f ↪ ℕ): Mandala c f ↪ Head S:= ⟨fun w=>Sum.inr (.inr (.inl (scratch U w))),fun _ _ h=> distinctive U (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))⟩
lemma disced (U:Site f ↪ ℕ)(z:Head S) : z∈Set.range (spin S U) ↔ Beam.Pennies S z∨ ∃ j∈Set.range U,Opacity.key S j=z := by
 constructor; · rintro ⟨y,rfl⟩; rcases y with i|i; exact Or.inl ((penned ..).2 ⟨_,rfl⟩); exact Or.inr ⟨_,⟨i,rfl⟩, rfl⟩
 rintro (hx | ⟨k,⟨i,h⟩,rfl⟩); obtain ⟨i,rfl⟩:= (penned ..).1 hx; exact ⟨.inl i,rfl⟩; rw [← h]; exact ⟨.inr i,rfl⟩ -- syntax

abbrev stages (U:Site f ↪ ℕ) (s:Yard c f): Molecule S:= s.map (spin S U)
lemma untouched (U:Site f ↪ ℕ)(s:Yard c f) : (stages S U s).toLeft=∅ ∧ Matter.own (stages S U s)=∅:= by
 constructor <;> ext p
 · simp only [mem_toLeft,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:=mem_map.mp h; unfold spin at hx; injection hx
 simp only [own,mem_toLeft,mem_toRight,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:=mem_map.mp h; unfold spin at hx; injection hx with he; injection he -- repr
lemma unbound (U:Site f ↪ ℕ)(s:Yard c f): roster (stages S U s)=⟨∅,∅,∅⟩:= by unfold roster; rw [(untouched S U s).1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩
-- locality & rent. expand supports_FULL. no shrinking preferences.
open Deck Stellar
abbrev ageV (A:PathData G)(i:Mandala c f) := i.elim (verse A) (fun _=>0)
def stepsV (i:Mandala c f):Site c:= i.elim (pace S) S.ratio.parent
local notation "σ" => Mint.width X.halo (radiusB p) (2*radiusB p)
variable {S}{T:Tube G S}{R:RG.Rep G f}{H:Cash W p a L₀ X o U T R}{v:Locale G} (Y:Seed R v)
-- Pays radiusB(S') ≤2B. aim Strong toute. input.He.St.H Cost.
local notation "A₀"=>Y.model
lemma footing (hY:R.p.B≤2*radiusB p) (i: Mandala c f)(h:ageV R.path i ≤ B) : stepsV S i∈ H.supportP (spin S A₀ i) ∧ H.supportP (spin S A₀ i) ⊆ neighbors σ (stepsV S i):= by
 have hB:0 < B:= lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1
 rcases i with i|i; · exact centered X.halo B (2*B) hB i S T R (h.trans (by omega : B ≤ 2*B))
 -- determine covering.Neighborhood.
 change S.ratio.parent i∈ Raw.regularFoot S.ratio X.halo B R (A₀ i)∧ Raw.regularFoot S.ratio X.halo B R (A₀ i)⊆ _
 unfold regularFoot; rw [(Y.reg i).1]; constructor
 · exact halo_subset _ _ (mem_image_of_mem _ (show i∈ RG.inspected (court i R.p.B) from Finset.mem_union_left _ (halo_subset _ _ (mem_singleton_self _))))
 intro x hx; obtain ⟨y,hy,hx'⟩:= halo_spec.mp (inspected_price S.ratio X.halo B (court i R.p.B) hB hx); obtain ⟨z,hz,rfl⟩:=mem_image.mp hy; have hh:separation (S.ratio.parent i) (S.ratio.parent z)≤R.p.B+1:= (Work.E04.parent_separation ..).trans (Nat.add_le_add_right (by simpa only [halo_spec,mem_singleton,exists_eq_left] using hz) _); exact (neighbors_mem ..).2 ((separation_triangle (S.ratio.parent i) (S.ratio.parent z) x).trans ((Nat.add_le_add hh hx').trans (by unfold Mint.width; nlinarith only [hB,hY])))
end YM.AllOrder.Burn
