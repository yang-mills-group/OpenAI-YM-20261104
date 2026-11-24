import YM.FVA2.TreeT.Wake
/-!
# `Desk.TreeJet` result for strict-rank control at the prescribed stencils

Needs a nontrivial classical nonlinear jet statement (`TreeT.innate`). To see it
actually instantiated at our choice (!) see `Inked/TrueF.lean`: proved there from
nonlinear `Jrad` realization & midpoint jet properties proved in `Gen/`.
This component alone is conditional on that hypothesis.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Landau.Detect MS.High MS.Arts
open MS.City MS.Plane.Wire MS.Wind MS.Wind.Modeled MS.Tone MS.Momentum MS.Tone.Frame Lattice
open MS.Native MS.Native.Wilsonian MS.Menus MS.Local.Physical MS.Outlook MS.Emit MS.Land
open MS.Pearl MS.Garment.Wick MS.Plane.Domain MS.Lifting
open MS.Book MS.Book.Program MS.Book.Convolve MS.High.Knobs MS.Color MS.Wind.Leading MS.Heat.Signal
open Teller Graft Capacity Desk Lambda
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n d k r:ℕ}{S:Deck G}{J:Booked S}{b:Bool}{p:Team}{A:Glyph S d}
variable (V:FullBook S)(T:MS_Data G J)(i: Plaid S d)
local notation "Γ"=>Archive
local notation "ι"=> Land.read i
local notation "Ω"=>run ( Glyph.lit V.toLitBook ι )
local notation "L"=> Lane4 G
-- Degree d, even including the unit case.
/-- Highest-rank Taylor test on the original stencils (raw column, before W-compensation).
Rank at each `n` from the MS data. See `treeOK`, which promotes this test to the required
hypothesis in the strict-rank implementation on the full compensated book. -/
def innate {S:Deck G}(V:FullBook S)(J:Booked S)(i: Plaid S d) : Prop :=
    ∀ (n k:ℕ) (w:List (Lane4 G)), w.length=( Land.read i ).grade+n → fieldDim wfield w+k≤d →
      torch k (run (Glyph.lit V.toLitBook (Land.read i))) w =
        if fieldDim wfield w+k=d then J.optics d i n 0 w else 0
lemma treeOK (h:G.Simple) (H:innate V J i) (p:Team) :
    Desk.TreeJet V p ( Archive d ( T.marks d i )) (Land.read i) := by
    intro u hu n hn A HA t
    obtain he:= Outlook.fieldD T.bulkOK ( T.markOK d i) MS.Motif.wisdom ( J.law d i|>.moodQ );
    have hV: PhysicalHF ι ( Archive d (T.marks d i)) := MS.Mach.initialHF ( J.law d i ) (sizeG i) ( T.markOK d i )
    let V':= horizonF V p A; let F:= scoreF V p A; apply excuse (v:=(d:ℤ))
    · rintro ⟨x,y⟩ w hW k hk; have hx:Tag (ι).grade A:=fun j=>( HA j ).upper; have ht X (j:ℕ): Graft.Above false wfield d ((ι).grade+j) (Tone.run ( F X j )):= by
         intro l hl hv; refine ⟨ ( City.run_this _ _ ).routine (ray l) 0, fun p h=>?_ ⟩; refine (Wake.signature ( k:=p ) V HA hv).trans ?_; rw [ H _ _ l hv (by omega),if_neg (by omega) ]
      have hw X (j:ℕ) : Rank ( V' j X) ((ι).grade+(j:ℤ)):= Capacity.RootL V hx j X
      change torch k ( V' n _ _) w= _; rw [ ( Pulse.shield ( aquaF V p A ) h (fun i t=> hw t i) x ( ht x ) n ).1 (exp y) hW hk, Wake.signature V HA hW,H n k w hW hk]; exact ( Data.torched T.bulkOK ( J.law d i ) ( T.markOK d i ) _ _ _ _ _ hW hk).symm
    · exact fun x w=> ( (aquaF V p A).owes n|>.stay x.1).joint.routine _ _
    · exact fun x w=> (he.master.road ℝ (ray w) _ (Nat.zero_le _) (fun i=> Bool.noConfusion i) (fun i=> Bool.noConfusion i)).1 _
    exact hu
end YM.FVA2.TreeT
