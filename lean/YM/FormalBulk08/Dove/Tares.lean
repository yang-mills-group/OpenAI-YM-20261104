import YM.FormalBulk08.Dove.Seat

/-! Expose uniform X & histories at ALL CUTS. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E e r:ℕ}
namespace Lab
structure Test (W:Lab G K X) where
    x:X
    N:ℕ
    M:ℕ
    sat : W.neck x ≤ N
    next:N ≤ M
variable {W:Lab G K X}
namespace Test
variable (W)
def testBed:= W.wturn (x (W:=W))
variable {W}
abbrev ND (W:Lab G K X): Pin (testBed W).scrolls:= ⟨Test.N,Test.sat⟩
abbrev MD (W:Lab G K X): Pin (testBed W).scrolls:= ⟨Test.M,fun i=> i.sat.trans i.next⟩
end Test
open Test
structure meshPoint (W : Lab G K X) extends Leaf W.scrolls where
    top:ℕ
    summit:ℕ
    wing:b ≤ top
    extra: top≤ summit
structure transferPoint (W: Lab G K X) extends Leaf W.scrolls where
    top:ℕ
    summit:ℕ
    wing:b<top
    extra:top≤ summit
variable (hp:Use W ρ E)(h:LocalRatio ρ)(hs:G.Simple)(a:hue G)
def meshPoint.role (x:meshPoint W): Deck (Test.ND W):= ⟨⟨⟨x.a,x.top,x.summit,x.zone.trans x.wing,x.extra⟩,x.b,x.zone⟩,x.wing⟩
def transferPoint.mark (x:transferPoint W): Turn (Test.ND W):= ⟨⟨⟨x.a,x.top,x.summit,x.zone.trans x.wing.le,x.extra⟩,x.b,x.zone⟩,x.wing⟩
abbrev aurum (W:Lab G K X): Time (meshPoint W):= (chron W.scrolls).reach (·.toLeaf)
abbrev purseP (W:Lab G K X): Time (transferPoint W):= (chron W.scrolls).reach (·.toLeaf)
def purseR (ξ:ℝ)(x:meshPoint W):ℝ:=ratioR (W.V x.a).S x.top x.b ξ
def spinR (ξ:ℝ)(x:transferPoint W):ℝ:= ratioR (W.V x.a).S x.top (x.b+1) ξ
include h hs hp
-- also e.g. render RegIR keeps E and possibly `T U k≥j` filtered by these indices. cheap
lemma weigh (he:e≤E)(hR:1≤r)(hu:r≤e+2): Totem (aurum W) (fun _=> fame _) (fun i=> W.width i.a i.b) (purseR targetPower) (fun i=> saga ρ a W i.a i.top i.b e r) (fun i=> saga ρ a W i.a i.summit i.b e r):=
   (final_dust (ND W) (MD W) (W.observed hp _) (Test.next) h hs a _ _ he hR hu).links (meshPoint.role (W:=W))
lemma weigh_shift (he:e≤E)(hR:1≤r)(hu:r≤ e+2): Totem (purseP W) (fun _=> fame _) (fun i=> W.width i.a i.b) (spinR targetPower) (fun i=> eating ρ a W (fun _=>i.top) i.a i.b e r) (fun i=> eating ρ a W (fun _=>i.summit) i.a i.b e r) :=
    (precoat (ND W) (MD W) (W.observed hp _) Test.next h hs a he hR hu).links (transferPoint.mark (W:=W))
lemma hear : Priced (purseP W) (spinR targetPower) (fun x=> bandK ρ a W (fun _=> x.top) x.a x.b) (fun x=> bandK ρ a W (fun _=>x.summit) x.a x.b) E :=
    fun i hi=> (barn (ND W) (MD W) (W.observed hp _) Test.next h hs a i hi).link transferPoint.mark
-- include arbitrary beyond rank by 0 using full valence. use for continuity
lemma weigh_all (he:e≤E) (r): Totem (aurum W) (fun _=>fame _) (fun i=> W.width i.a i.b) (purseR targetPower) (fun i=> saga ρ a W i.a i.top i.b e r) (fun i=>saga ρ a W i.a i.summit i.b e r):= by
    by_cases hg :1≤r∧r≤e+2;exact weigh hp h hs a he hg.1 hg.2
    have hh (i : meshPoint W) (p)(u:i.b≤p) : saga ρ a W i.a p i.b e r=0:= by
        by_contra he; obtain ⟨H,U,V⟩:= (genu (W.V i.a) (W.wood i.a) (W.toEmpire.bill i.a) ρ a h hs u).valence _ _ he; omega
    simp_rw [show ∀ i:meshPoint W, saga ρ a W i.a i.top i.b e r=0 from fun i=>hh i _ i.wing, show ∀ i:meshPoint W,saga ρ a W i.a i.summit i.b e r=0 from fun i=>hh i _ (i.wing.trans i.extra)]; apply Aster.voids
end Lab
end YM.FormalBulk08.Dove
