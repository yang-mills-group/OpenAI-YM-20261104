import YM.RemainderComparison.Aria.Oars
import YM.AllOrder.Burn.Moment
set_option autoImplicit false
noncomputable section
/-! # Ports from actual Representation; folding for the Mark manuscript.
 Use the name scheme on model-vac reading: each fine site supplies one pack.B.Left. Group by coarse origin
 × site within same parent block. Qin ANY Hp sufficiently short relative physical.P.Width L.Mesh.
 This creates Crew.S eligible labels (with `.Seedlings.BoxOf` tariff, socket footprints etc.Model) for ANY Cash
 Appointment at Earth.Epoch.Uri.Seat`. Eventually λ_l permit on repograph.
-/
namespace YM.QuadraticLocal.Venue
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open RemainderComparison RemainderComparison.Aria RemainderComparison.Seedlings BoxOf AllOrder.Burn AllOrder AllOrder.Till -- namespace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n f c C F L₀:Side}{P:Patch}{M D':ℕ}{K:Teller G}{X:ConnectedActivityE6.Target G K}
variable {h:f.val=c.val*P.L.val}{H:F.val=C.val*P.L.val}{Q:KernelChoices}(hC:C.val=c.val*M)(he:2≤c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ}
    {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
variable {Z:Site C}{r m N k:ℕ} {a W K₀ v : ℝ}{o : ConnectedActivityE6.Target.Order G W}
namespace Score
variable {g:StepData n f} {u:Tube G g} {P:Teller G} {J:ConnectedActivityE6.Target G P}
    (A:Cash W p a L₀ J o v u R) {s:AllOrder.Burn.Locale G}(C:AllOrder.Burn.Seed R s)
local notation "δ"=> Mint.width J.halo (radiusB p) (2*radiusB p)
local notation "Kx"=> Aria.Score
variable (hw:R.p.B≤2*radiusB p)
include hw
def nameBook : Aria.Score A (Site g.ratio.count) (Mint.width J.halo (radiusB p) (2*radiusB p)) where
 book _:=Finset.univ
 charges _ _ _:= Subset.rfl
 index := g.ratio.splitSites.symm.toEmbedding.trans C.model
 advice s i n h:= by
    let y : Site f:= g.ratio.assemble (s,i); let z:= Opacity.key g (C.model y); obtain ⟨h₁,h₂⟩:= AllOrder.Burn.footing (H:=A) C hw (Sum.inr y) (show 0≤ radiusB p from Nat.zero_le _); change s∈A.supportP z ∧ A.supportP z⊆neighbors δ s; exact (show g.ratio.parent y=s from g.ratio.assemble_parent (s,i)) ▸ (show g.ratio.parent y∈_ ∧ _⊆ neighbors δ (g.ratio.parent y) from ⟨h₁,h₂⟩)
-- recognition.Metadata.Tag
variable (sset:Set ℕ)
local notation "Yx"=> nameBook A C hw
lemma name_ref (i:ℕ): (i∈Set.range (nameBook A C hw).index) ↔ i∈Set.range C.model:=by
 constructor
 · rintro ⟨s,rfl⟩; exact ⟨g.ratio.assemble s,rfl⟩
 rintro ⟨j,rfl⟩; exact ⟨g.ratio.splitSites j,congr_arg C.model (g.ratio.splitSites.symm_apply_apply _)⟩
-- grant all old tolls? supply exception for any not in textbook (may later discard older e with finite cost).
def pose : BoxOf A:= Aria.Score.pose A _ (nameBook A C hw)
lemma grant (p:Set ℕ)(q:Set ℕ)(h:∀ i:ℕ, i∉ Set.range C.model → R.activities.regularOccurrence R.p i≠0 → i∈p∨ i∈q): BoxOf.Grant A (Venue.Score.pose A C hw) p q:= by
 apply Aria.Score.stars; intro i hi hv hT; have ht:i∈ Set.range C.model:= by by_contra hx; exact (h _ hx hT).elim hi hv
 obtain ⟨⟨s,j⟩,rfl⟩:= (name_ref A C hw _).2 ht; exact ⟨s,j,0,mem_univ _,rfl⟩
-- section stamp comparison
omit hw
section wrap
variable {P: Patch} -- conflicts h ... use previous P? revert
end wrap
end Score
namespace Score
variable (C' : Cash W p a L₀ X o K₀ T' R') (c' : Cash W p a L₀ X o v T R) (hq : T'= Deck.re T)(ht:R'.path=R.path)(hx:R'.p=R.p)(hw':R'.p.B≤2*radiusB p)(hw:R.p.B≤2*radiusB p)
open AllOrder.Burn
variable {s:AllOrder.Burn.Locale G} (z: Seed R s) (z':Seed R' s)
set_option quotPrecheck false
local notation "Q₀"=> (L).high.cut
local notation "q₀"=> (L).low.cut
local notation "δ"=> Mint.width X.halo (radiusB p) (2*radiusB p)
local notation "X₀"=> nameBook C' z' hw'
local notation "Y₀"=> nameBook c' z hw
include hC he c' C' z z' hx hw' hw
lemma wears : Aria.Wears hC he C' c' δ X₀ Y₀:=by
 let p₀:Site C × Site P.L→ Site F:= (decreed H).assemble; let b₀ : Site c × Site P.L → Site f:=(decreed h).assemble; have hz(x:Site C)(i: Site P.L): (L).high.cut (p₀ (x,i)) = b₀ (q₀ x,i):= (L).regions x i;
 refine ⟨rfl,fun j i _ _=>?_,fun j i n _ V _=>?_⟩
 · let u:=b₀ (q₀ j,i); let v:=p₀ (j,i); have he : u=(Q₀) v:= (hz j i).symm; change (R.activities.reg (z.model u)).support=Finset.image _ (R'.activities.reg (z'.model v)).support; rw [(z.reg _).1,(z'.reg _).1,hx,he, Till.court,Till.court,← Finset.image_singleton]; exact Deck.ringed (fineP h H hC) _ _
 let u:=b₀ (q₀ j,i); let v:=p₀ (j,i); have he : u=(Q₀) v:= (hz j i).symm; change R'.activities.E (z'.model v) _ =R.activities.E (z.model u) _; rw [z'.value,z.value]; apply z.off; rw [he, (L).high.expansion]; exact fun _ _ _=>rfl
end Score
end YM.QuadraticLocal.Venue
