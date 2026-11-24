import YM.LocalTaylorR2.Marker.Steno
import YM.LocalTaylorR2.Marker.Primula
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Parcel
import YM.LocalTaylorR2.License
import YM.LocalTaylorR2.Scaling
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
open Tail Blush Next.Foundations Planned.GuardedAtom
open Ovens Extra.Histories Progress.DirectedRecipe YM.Planned
variable {v r B w σ a e s' δ : ℝ}{A':BudgetPoint}{l0 q η : ℝ}
variable (t:Cloud R)(take : H.fragrances→ℕ→ Prop) (z:ℂ)(s: Site c)

structure Modesty {m:Side}(G:Gauge) (p:BudgetPoint)(o:Site m)(X:ℕ→ Support m)(F:ℕ→ Config G m→ℂ)(e:ℝ):Prop where
    regular : ∀ i,p.Regular (X i) (F i)
    price : ∃ w:ℕ→ℝ,(∀ i,p.supBounds o (X i) (F i) (w i)) ∧ SumBudget (fun i=> Push.Local.reservedMass p (X i) (w i)) e

def arcs (l:ℕ) (i:H.fragrances): Config G c→ℂ:= z • (Complex.ofReal ∘ subtensor t.live H i take Chi.canonical l + Complex.I • (Complex.ofReal ∘ subtensor t.pale H i take Chi.canonical l))
def sheetC (l:ℕ) := stuff (Blush.enter H) (arcs H t take z l)
lemma arc (l:ℕ)(i:H.fragrances): Blush.pane H t z i= arcs H t (fun z p=> ¬take z p) z l i+arcs H t take z l i:=by
    unfold pane arcs; funext U; all_goals simp only [Pi.add_apply,Function.comp_apply,Pi.smul_apply,smul_eq_mul, recovery _ H i take U Chi.canonical l,Complex.ofReal_add]; ring
-- ext U ext maybe wrong `ext`; test
lemma voyage (l:ℕ): fields H t z=sheetC H t (fun z p=>¬ take z p) z l + sheetC H t take z l:=by
    funext i; unfold Blush.fields sheetC; rw [Pi.add_apply]; by_cases h : i∈ Set.range (Blush.enter H)
    · obtain ⟨i,rfl⟩:=h; rw [stuffed,stuffed,stuffed]; exact arc H t take _ _ i
    simp only [Progress.DirectedRecipe.blank _ _ h, add_zero]

lemma mark_law (Q:YM.ConnectedActivityE6.Target G P): markBill t.live Q=markBill t.pale Q:=by unfold markBill; rw [t.rates,t.turnout]
-- accountant uniform perReal and Either.Zero
lemma modesty (L:ℕ) (u:ℝ) (hz:∀ (M:Leaf R), s∈M.crest.image S.ratio.parent →
    ∃ f:H.fragrances→ℝ,(∀ i, A'.Regular (locus M H s i) (subtensor M H i take Chi.canonical L) ∧ A'.supBounds s (locus M H s i) (subtensor M H i take Chi.canonical L) (f i))∧ SumBudget (fun i=> Push.Local.reservedMass A' (locus M H s i) (f i)) (markBill M Q*u)) (hs:s∈ t.live.crest.image S.ratio.parent):
    Modesty G A' s (Blush.scope H t s) (sheetC H t take z L) (2*‖z‖*(markBill t.live Q*u)):=by
   obtain ⟨v',hv,hy⟩:= hz t.live hs; obtain ⟨y',ht,hp⟩:=hz t.pale (t.turnout ▸ hs : s∈ t.pale.crest.image S.ratio.parent); simp_rw [← Blush.arches H t] at ht hp; rw [← mark_law t] at hp
   let g i:=‖z‖*(v' i+y' i)
   have h (i:H.fragrances): A'.Regular (locus t.live H s i) (arcs H t take z L i)∧A'.supBounds s (locus t.live H s i) (arcs H t take z L i) (g i):=by
      have h':= regular_smul Complex.I (ornate (ht i).1); have h:= ornate (hv i).1
      have he:= bound_smul Complex.I (pricingG (ht i).1 (ht i).2); rw [Complex.norm_I,one_mul] at he
      exact ⟨regular_smul z (regular_add h h'),bound_smul z (bound_add h h' (pricingG (hv i).1 (hv i).2) he)⟩
   set s' := Blush.scope H t s; let C:= Blush.enter H; let f:= stuff C g
   have he(i:ℕ): A'.Regular (s' i) (sheetC H t take z L i)∧ A'.supBounds s (s' i) (sheetC H t take z L i) (f i):=by
     unfold s' scope f C sheetC; by_cases hx:i∈Set.range (Blush.enter H)
     · obtain ⟨i,rfl⟩:= hx; rw [(Blush.enter H).injective.extend_apply,stuffed,stuffed]; exact h i
     rw [Function.extend_apply' _ _ _ hx,Progress.DirectedRecipe.blank _ _ hx,Progress.DirectedRecipe.blank _ _ hx]
     exact regular0 ..
   have hb : SumBudget (fun i=>Push.Local.reservedMass A' (locus t.live H s i) (g i)) (2*‖z‖*(markBill t.live Q*u)):=by
     convert budget_scale (norm_nonneg z) (budget_plus hy hp) using 1; · funext i; unfold g Push.Local.reservedMass; ring
     ring
   refine ⟨fun i=> (he i).1,f,fun i=> (he i).2,transfer_budget C ?_ ?_ hb⟩
   · intro i; unfold f C s' scope; rw [(Blush.enter H).injective.extend_apply,stuffed]
   intro j hj; unfold f; rw [Progress.DirectedRecipe.blank _ _ hj,Push.Local.reservedMass, mul_zero]
end YM.LocalTaylorR2.Marker
