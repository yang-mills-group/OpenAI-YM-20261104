import YM.RGComparison01.Marks.Flights
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Relay
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {c f C F L₀: Side} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC:C.val=c.val*M} {he : 2≤ c.val}
variable {T:Tube G (stepped Q h)} {T':Tube G (stepped Q H)} {R : RG.Rep G f} {R':RG.Rep G F}
  {I : Cash W s a L₀ X o U T R} {I' : Cash W s a L₀ X o u T' R'}
  {D : Cabinet ι I b} {A : Cabinet χ I' b} {Z : χ → ι}
    (L':Relay (A:=A) (D:=D) hC he Z)
local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {E : Tree.Forest (stepped Q h).ratio} {E' : Tree.Forest (stepped Q H).ratio}
variable (x : Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (p : Cabinet.Folder χ)
    (hS:A.garden p⊆neighbors n x)
local notation "q" => (A.shell p)
local notation "U₁" => (D.shell (send Z p))
open PhysicalNext.Repeat.Lotus Team Merge Palette Switch Pledge Pillow
variable {σ:Type} (M₀:σ→ Leaf R)(M₁:σ→ Leaf R')
variable (d: Ribbon R k)(A':Ribbon R' k)
set_option quotPrecheck false
local notation "D'"=> Drawing.cabinet I d
local notation "AA"=> Drawing.cabinet I' A'
local notation "P₁"=> Mint.width X.halo (radiusB s) (radiusB s+k)
-- span accessible proof from Ribbon with physical marks anchored on faith
structure Lens (θ : A'.Node→d.Node) (t:σ→A'.Node) (x:Site C) (n:ℕ) : Prop where
   walks : Ribbon.Drops d A' (Deck.fineP h H hC) θ
   position (i:σ) : (M₁ i).turn = Wing.logKey (t i).val
   down (i:σ) : (M₀ i).turn = Wing.logKey (θ (t i)).val
   ranks (i:σ) : separation x ((decreed H).parent (A'.home (t i))) ≤ n
   reads (i:σ)(U:Config G f): (M₀ i).ingredient U=(M₁ i).ingredient ((L).high.links U)
namespace Lens
variable {d A' M₁ M₀} {θ : A'.Node→d.Node}{t:σ→A'.Node}
    (p':Lens (hC:=hC) (he:=he) (H:=H) (h:=h) M₀ M₁ d A' θ t x n)
include p'
lemma wiring (hp:R'.path=R.path)(hR:R'.beta=R.beta)(hy:R'.p=R.p) (hw: 2*(P₁+3)<c.val) :
    Veils (I:=I) (I':=I') (A:=Drawing.cabinet I' A') (D:=Drawing.cabinet I d) (Z:=Sum.map (Drawing.down hC he hp) θ) (hC:=hC) (he:=he) M₀ M₁ (Sum.inr ∘ t) x n:= by
   refine ⟨Drawing.relay hC he hp _ _ p'.walks hy hR hw,fun i=>?_,fun i=> ?_, p'.ranks, fun J u i=>?_⟩
   · unfold Palette.sign; rw [p'.position]; rfl
   · unfold Palette.sign; rw [p'.down]; rfl
   let L':= L
   unfold Leaf.paidU Leaf.fond
   rw [hR,J.rolls,(J.glassU _).2.2,p'.reads,p'.position,p'.down]
   apply congr_arg
   rw [J.D.1,J.D.2]; let s₀:= x; let k':= t i
   let P₀:= regularFoot (decreed H) 0 B R' k'.val
   have ht:= (A'.covers (decreed H) 0 B (lt_of_lt_of_le (by norm_num) I'.laws.data.room.sight.1) k').2
   have hf:4<f.val:=by
     have hp:= P.L.pos; have he:= h ▸ (show c.val ≤ c.val*P.L.val from Nat.le_mul_of_pos_right _ hp : _); omega
   have hx := Ribbon.descentZ (h:=h) (H:=H) d A' hC he p'.walks 0 B k' hf
   change regularFoot (decreed h) _ _ _ _=_ at hx
   let y:=(decreed H).parent (A'.home k')
   change Coat.enforce _ _ _ _=Coat.enforce _ _ _ (Coat.plaza _ (regularFoot (decreed h) _ _ _ _)); rw [hx]
   exact J.porter P₀ _ (by unfold Mint.width at *; omega) y ht _ _
-- tagged footprint image. root marker origin options
lemma desc (i:σ): ((M₁ i).crest.image (decreed H).parent).image (L).low.cut=(M₀ i).crest.image (decreed h).parent:= by
   have hk: (M₀ i).crest= (R.activities.reg (θ (t i)).val).support:= by unfold Leaf.crest; rw [p'.down]; rfl
   have ht: (M₁ i).crest= (R'.activities.reg (t i).val).support:= by unfold Leaf.crest; rw [p'.position]; rfl
   rw [hk,p'.walks.view,ht,image_image,image_image]; exact image_congr fun i _=> (Lace.position (L) i).symm
end Lens
end YM.RGComparison01.Relay
