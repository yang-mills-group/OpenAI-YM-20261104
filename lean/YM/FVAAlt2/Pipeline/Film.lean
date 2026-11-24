import YM.FVAAlt2.Boot.Labels
import YM.FVAAlt2.Repop.Toward
import YM.FVAAlt2.Periodic.Field
/-! # Packaging per-regulator script **solely in LocalFormal** banks and their render-back to W

No `Frame/GridStep` computation of output tensors when taking this script. Real $χ(t)$ UnitCost before choosing epochs, order ≥r then freeze. Fields are unrestricted (Sense._.Skew) no budget. Prices constants intentionally forgotten after THIS step when defining next W: effAction copied only *after* projecting constant $out$ (all its common t coefficients). Constants retained in single-step (Extent.Complete theorem `Aperture.posts_vac`) and may be paid later if computing the partition function itself. Single mark R.fire; full product input, so enough for correlations not connected cumulants, rather uses equality only that bit with `logMarked` under this gauge (uses representation of FULL vacuum denominator). Any necessary regrouping needs compatible W or separate marker.R.Transit. `Era.levels` *not actual-coupling RW*; they do not proclaim $α$ mismatches re Run (Buffet.E^natural) estimated. See also `Repop/Singer`. Only genuine Chain & real likelihood in each step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m :ℕ} {G:Gauge} {R X:Type} [DecidableEq R] {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side}
open Oracle Period.Field
variable (C:Circuit M N) (Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (Γ: History G)(K: Bulk.Chain Γ)(P: Period.Field.SeriesT C Q Γ)
variable (S: Marker.Census R)(u:R) (A: X→ Boot.Scout (G:=G) m)
variable (L:Page M→ Binding.Scale)
variable (p:ℕ) -- period
namespace See
variable {C Γ}
local notation:max "x_" k:max=> P.vol k
abbrev world (m:ℕ) := Γ.S.side m p
set_option quotPrecheck false
local notation:max "f_" k:max => (Γ.S.side (P.vol k) p)
local notation:max "U_" k:max => P.stepData C Γ p k
local notation:max "F_" k:max => Halo.bios ( P.stepData C Γ p k )
local notation:max "P_" k:max => P.records C Γ p k
local notation:max "J_" k:max => directive (P.stepData C Γ p k)
local notation:max "K_" k:max => ( P.readyKin C Γ K p k )
local notation:max "w_" k:max=> Page.opening M k
local notation:max "B_" k:max=> ( Boot.ink S u Γ (P.vol (w_ k)) p (A k) )
-- types
abbrev Agenda := (k:Page M)→ Colors S G (Γ.S.side (P.vol k) p)
-- cast things preserving DEFINITIONS. agenda not chosen random in existence.
def castF {X:ℕ→ Sort*}{i j:ℕ}(h:i=j) (x:X i):X j:= h ▸ x
protected lemma poster {X:ℕ→ Sort*}{i j:ℕ}(p:(i:ℕ)→X i→Prop)(x:X i)(h:i=j)(H:p i x): p j ( castF h x ) :=by subst j; exact H
lemma transferred {X Y: ℕ→ Sort*}{i j:ℕ}(p:(i:ℕ)→X i→Y i→Prop)(x:X i)(y:Y i)(h:i=j)(H:p i x y): p j (castF h x) (castF h y):=by subst j; exact H
abbrev size (x:Flap M):= Γ.S.side (P.vol x.next+1) p
variable {S p}
abbrev before (k:Flap M)(U: Colors S G (Γ.S.side (P.vol k.prev) p)): Colors S G (size P p k):= castF (X:=fun i=> Colors S G (Γ.S.side i p)) (P.links k) U
-- Connector Ledger.S.Fields***projections.Client. No Heal.S.E.Payment assumed. only takes align.Scheduler after.
variable (p)
variable (S)
variable {f: Side}

def visible (p':RG.Clip)(U: PathData G)(F:UnitCost)(V:Colors S G f)(x:ℕ)(b:fieldDir G f 1):ℂ:= if x=0 then -(↑(Assembly.jet (mainTerm p' U ∘ (represent (n:=f))) 2 b):ℂ) else -(↑(coeff (x+2) (Prim.tale ( Gala.feeAct p' U F V b ))):ℂ)
def noseC (F:UnitCost)(V:Colors S G f)(i:ℕ)(b:fieldDir G f 1):ℂ := Comparison.RG02.Moving.Path.motion (Arm.shineM F V u b) (V.power (Arm.pub u)+i)

-- chooses time program before field moments, per r. Alignment & Kit.Model(u operator) fixed before output restrictions, even if W.vac has an arbitrary constant. Slot.S.unit
structure Times (r:ℕ) where
    cloth : (Page M)→ UnitCost
    top (w:X) : cloth ( Page.opening M w ) = Boot.dormant
    holds (w:Page M): Ribbon.Align r (L w) (cloth w)
-- unscaled reporting at t.Screen. Stage.Fee.
variable (r:ℕ)(V:Times (L:=L) r) -- parameter arg? implicit?
local notation:max "t_" k:max => V.cloth k
variable [Fintype R]
abbrev lifeT (k:Flap M)(W: Colors S G (Γ.S.side (P.vol k.prev) p)) := Adjacent.born ( Symmetry.Orbit.ground (K_ k) (F_ k) (J_ k) (before P k W) r ) (V.cloth k.prev) 0 r
abbrev boostT (k:Flap M)(W: Colors S G (Γ.S.side (P.vol k.prev) p)) := Adjacent.born ( Symmetry.Orbit.words (K_ k) (F_ k) (J_ k) (before P k W) r (S.fire u) ) (V.cloth k.prev) 0 r
-- uses `Symmetry.Orbit` ground / marks log. logMarked denominator full.Mark chooses era at registration, assembly across stages not substituting artifact.P.All.
structure Task (k:Flap M) (W:Colors S G (Γ.S.side (P.vol k.prev) p))(W':Colors S G (Γ.S.side (P.vol k.next) p)): Prop where
   proper (i:ℕ)(hi:i≤r) (x: fieldDir G (Γ.S.side (P.vol k.next) p) 1): visible S (P_ k.next).clip (P_ k.next).path (t_ k.next) W' i x=(lifeT K P S (p:=p) L r V k W) i x-(lifeT K P S (p:=p) L r V k W) i 0
   mark_w (i:ℕ)(hi:i≤r) (x: fieldDir G (Γ.S.side (P.vol k.next) p) 1): noseC S u (t_ k.next) W' i x=(boostT K P S u (p:=p) L r V k W) i x
structure Setup (X':Agenda P S p): Prop where
   top (w:X): X' (w_ w)=B_ w
   allows (i:Page M): Bulk.Well (X' i) ∧ (X' i).power (Arm.pub u)=m
   walks i: Task K P S u (p:=p) L r V i (X' i.prev) (X' i.next)

def prime {x:Page M} (X': Agenda P S p)(b:fieldDir G (Γ.S.side (P.vol x) p) 1) (e:ℕ): ℂ:= noseC S u (t_ x) (X' x) e b
-- scalar capture chosen stop.Comparable. Used with Universe overlaps replacing storytellers
-- open.No Top for expressions at x outside.
end See
end YM.RegulatorIR.FVAAlt2.Pipeline
