import YM.QuadraticLocal.Normalization.Escrow
/-!
## Before pose.θ E packets allocation & strong contracts

 The compiler ALREADY arranges the E supports of EVERY general-e pre-ready
 re-expression, not just organizes K. This is the disjoint union description
 of the carriers & their footprints. `∃` Model designation for output means
 either belongs to old analytic membership Sector (actual rooted modelView) or to a
 real, full-footprint ERR address preserving its stencil/location; cost through
 hearty reserved exponent
 -- generally even larger than `supportExponent`. No pre-reset pledge that these
 E addresses pass Valid (no affine readout here!!) Price and re-expression.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary.Guard.Dusk
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n}
open Lapis Herb Weaving Morning
open Lattice RG Pressure Push.AbsoluteSums
open PhysicalNext Repeat
variable (M : Locale G) (α y ξ β t:ℝ)
noncomputable def day (n:Side):ℕ ↪ ℕ:= ⟨fun i=> (Burn.keys n).symm (.inr i),fun _ _ h=>Sum.inr_injective ((Burn.keys n).symm.injective h)⟩
local notation "S"=> (Site n)
@[simp] lemma days (i:ℕ): Burn.keys n (day n i) = .inr i:= (Burn.keys n).apply_symm_apply _
lemma billing (i:ℕ) : (i∈ Set.range (day n)) ↔ ∃ x:ℕ,(Burn.keys n) i=.inr x:= by constructor <;> rintro ⟨x,hx⟩; exact ⟨x,hx ▸ days x⟩; exact ⟨x,(keys n).injective ((days x).trans hx.symm)⟩
local notation "L"=> ( shipment R c p X v M β α t )
local notation "I"=> ( Set.range (Burn.pivot n) )
lemma lineage {n:Side} (k:ℕ) : k∉ Set.range (Burn.pivot n) ↔ k ∈ Set.range (day n):= by
 rw [billing,rolled]; cases Burn.keys n k <;> simp
-- Mind Consumer.Clock.Proof.` Uses paneling representation with ALL hard
-- re-expressions Book.Member.Op Heads.T.Route Banker pays. Includes Nursery.e*M already.
structure BeforeBook (R:PathData G)(c:Clip)(p:BudgetPoint) (X: Listing G n) (v: Collection.Source G n)
   (σ C:ℝ) : Prop where
     former i : ( shipment R c p X v M β α t ).activities.reg (Burn.pivot n i)= Burn.spine p i ∧ (shipment R c p X v M β α t).activities.E (Burn.pivot n i)= M n i
     rooted i : (shipment R c p X v M β α t).activities.reg (day n i)=X.reg i ∧ (shipment R c p X v M β α t).activities.E (day n i)= v.logRead i
     exactK : (shipment R c p X v M β α t).activities.EBound p (Guard.costM p y+σ)
     mirrors : Nonempty (Burn.Seed ( shipment R c p X v M β α t ) M)
     herr : Collection.Local X p v σ C
     quote : (shipment R c p X v M β α t).activities.KBound p ξ
     ethnic : ( shipment R c p X v M β α t ).activities.ForcedFamily p
variable {z:ℝ}(hx:Rosary.Guard.Dusk.Escrow (R:=R) (c:=c) (p:=p) (X:=X) (v:=v) (w:=w) (H:=H) α M y β t ξ z)
include hx
lemma witnessed : BeforeBook M α y ξ β t R c p X v H w:= by
   refine ⟨fun i=> Burn.earns p (X.read v) M i,fun i=> ?_,hx.fullbudget.unweighted,hx.splice.2.2,hx.old,hx.attention.2.1,hx.attention.1⟩
   change ((Burn.press p (X.read v) M).reg (day n i)) = X.reg i ∧ ((Burn.press p (X.read v) M).E (day n i)) = v.logRead i; simp [Burn.press,days]; exact ⟨rfl,rfl⟩ -- simplify
end YM.AllOrder.Rosary.Guard.Dusk
