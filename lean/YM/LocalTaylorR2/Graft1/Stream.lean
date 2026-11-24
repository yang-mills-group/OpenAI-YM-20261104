import YM.LocalTaylorR2.Marker.Steno
import YM.LocalTaylorR2.Graft1.Bulk
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

variable (Φ:Leaf R→ H.fragrances→ Config G c→ℝ)
def spear (i:H.fragrances): Config G c→ℂ:= z • (Complex.ofReal ∘ Φ t.live i + Complex.I • (Complex.ofReal ∘ Φ t.pale i))
def scroll1  := stuff (Blush.enter H) (spear H t z Φ)
-- accountant uniform perReal and Either.Zero
lemma GraftingStop (u:ℝ) (hz:∀ (M:Leaf R), s∈M.crest.image S.ratio.parent →
    ∃ f:H.fragrances→ℝ,(∀ i, A'.Regular (locus M H s i) (Φ M i) ∧ A'.supBounds s (locus M H s i) (Φ M i) (f i))∧ SumBudget (fun i=> Push.Local.reservedMass A' (locus M H s i) (f i)) (markBill M Q*u)) (hs:s∈ t.live.crest.image S.ratio.parent):
    Modesty G A' s (Blush.scope H t s) (scroll1 H t z Φ) (2*‖z‖*(markBill t.live Q*u)):=by
   obtain ⟨v',hv,hy⟩:= hz t.live hs; obtain ⟨y',ht,hp⟩:=hz t.pale (t.turnout ▸ hs : s∈ t.pale.crest.image S.ratio.parent); simp_rw [← Blush.arches H t] at ht hp; rw [← mark_law t] at hp
   let g i:=‖z‖*(v' i+y' i)
   have h (i:H.fragrances): A'.Regular (locus t.live H s i) (spear H t z Φ i)∧A'.supBounds s (locus t.live H s i) (spear H t z Φ i) (g i):=by
      have h':= regular_smul Complex.I (ornate (ht i).1); have h:= ornate (hv i).1
      have he:= bound_smul Complex.I (pricingG (ht i).1 (ht i).2); rw [Complex.norm_I,one_mul] at he
      exact ⟨regular_smul z (regular_add h h'),bound_smul z (bound_add h h' (pricingG (hv i).1 (hv i).2) he)⟩
   set s' := Blush.scope H t s; let C:= Blush.enter H; let f:= stuff C g
   have he(i:ℕ): A'.Regular (s' i) (scroll1 H t z Φ i)∧ A'.supBounds s (s' i) (scroll1 H t z Φ i) (f i):=by
     unfold s' scope f C scroll1; by_cases hx:i∈Set.range (Blush.enter H)
     · obtain ⟨i,rfl⟩:= hx; rw [(Blush.enter H).injective.extend_apply,stuffed,stuffed]; exact h i
     rw [Function.extend_apply' _ _ _ hx,Progress.DirectedRecipe.blank _ _ hx,Progress.DirectedRecipe.blank _ _ hx]
     exact regular0 ..
   have hb : SumBudget (fun i=>Push.Local.reservedMass A' (locus t.live H s i) (g i)) (2*‖z‖*(markBill t.live Q*u)):=by
     convert budget_scale (norm_nonneg z) (budget_plus hy hp) using 1; · funext i; unfold g Push.Local.reservedMass; ring
     ring
   refine ⟨fun i=> (he i).1,f,fun i=> (he i).2,transfer_budget C ?_ ?_ hb⟩
   · intro i; unfold f C s' scope; rw [(Blush.enter H).injective.extend_apply,stuffed]
   intro j hj; unfold f; rw [Progress.DirectedRecipe.blank _ _ hj,Push.Local.reservedMass, mul_zero]
-- agnostic where Realm Clutch/Buoy marks apply.
variable (ψ: Reel.Scroll G f)
lemma scrollSub (Q:Leaf R→ H.fragrances→ Config G c→ℝ): scroll1 H t z (Φ - Q)= scroll1 H t z Φ - scroll1 H t z Q :=by
   funext i; unfold scroll1; rw [Pi.sub_apply]; by_cases he:i∈Set.range (Blush.enter H)
   · obtain ⟨i,rfl⟩:= he; rw [stuffed,stuffed,stuffed]; ext1 V; simp [spear]; ring -- * j addresses
   rw [Progress.DirectedRecipe.blank _ _ he,Progress.DirectedRecipe.blank _ _ he,Progress.DirectedRecipe.blank _ _ he,sub_self]
local notation "ξ0"=> betaF G x L
variable {ε E':ℝ} {δ0:Target.Expense Q}
variable (hg:Trailer Q δ0 L W μ x o A'.order A'.power l Chi.canonical ε E')(hpX:0<E')(ht:Stamp T)(hq:A'.supportExponent+2≤ δ0.earn)
   (hb:A'.B=radiusB x)(hx:A'.threshold=Pressure.temp x)
abbrev slate (l:ℕ) (M:Leaf R) (i:H.fragrances):= roadway M H i take ψ Chi.canonical l
local notation "Z'"=>Blush.scope H t s
local notation "E!"=> markBill t.live Q
abbrev highway (l:ℕ):= scroll1 H t z (slate H take ψ l)
include ht hx hg hpX hb hq
variable (i m₀:ℕ)(hi:i ≤ l+1)(he:∀ u q,take u q→i≤q)(hK:s∈ t.live.crest.image S.ratio.parent)
local notation "p!"=> ξ0^ requested i ε
local notation "Pt"=> Modesty G A' s Z'
include he hi hK
lemma surrender (J:Cash W x μ L Q o C T (Reel.bend R ψ)): Pt (highway H t take z ψ l) (2*‖z‖*(E! *(p!/E'))):=by
   exact GraftingStop H t z s (slate H take ψ l) _ (fun M hz=> Marker.spend H hg hpX ht hq hb hx J M s hz take i hi he) hK
open Reel
lemma towP
   (hX:∀ u q,take u q→q ≤ l)(q: Strand)(QF:∀ t:Strand,Cash W x μ L Q o C T (Reel.bend R (R.activities.E+Reel.Strand.dial t • ψ)))(hv:0≤Reel.Strand.dial q):
   Pt (sheetC H t take z l - highway H t take z (R.activities.E+Reel.Strand.dial q • ψ) l) (2*‖z‖*(E! *((Reel.Strand.spelling l* Reel.Strand.dial q)* p!/E'))):=by
   let φ t:=R.activities.E+Reel.Strand.dial t • ψ; let W q':= slate H take (φ q') l; let σ:= W Strand.bud; let β:= W q
   have he' : sheetC H t take z l= scroll1 H t z σ:=by
      have he: φ Strand.bud= R.activities.E:=by simp [φ,Strand.dial,Strand.bud]
      have h : σ=fun M i=> subtensor M H i take Chi.canonical l:= by unfold σ W slate; rw [he]; exact funext fun M=>funext fun i=> funext fun V=> Marker.rewind M H i take l (hX i) le_rfl Chi.canonical V -- arg
      rw [h]; rfl
   rw [he']; show Pt (scroll1 H t z σ- scroll1 H t z β) _; rw [← scrollSub]; refine GraftingStop H t z s (σ-β) _ (fun M h=> ?_) hK
   have he q': Coast A' s (locus M H s) (W q' M) (markBill M Q*(p!/E')):= ⟨Marker.spend H hg hpX ht hq hb hx (QF q') M s h take i hi he⟩
   obtain ⟨A,a',v,d,r,B,D,K,t,z,s₀,w,k,j,x',b,F,w',R0,hv',hB,hf⟩:= hg; obtain ⟨N,v'⟩:= hf _ _ S T ht R C H -- binders count
   have hD:= (Coast.strandsP A' s (locus M H s) (fun i=>W i M) q he (fun i U hv=> blueBudget M H i take ψ N l QF (hX i) le_rfl A' hx s U hv) hv).ocean
   convert! hD using 2; ring_nf; rfl
end YM.LocalTaylorR2.Marker
