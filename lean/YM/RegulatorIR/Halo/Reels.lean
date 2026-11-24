import YM.RegulatorIR.Halo.Caps

/-!
# Auxiliary IR for certificate
Extend quadratics and T tape over family of all repetitions of sides. Need
single *industry* proof BEFORE substituting lengths for conclusion. Dummy Strip
sights for repeats (no propagation estimate invoked there). -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side}


variable {S:Heir n G} (H: Reel S) (w: W)

def Common (H: Reel S) := ∀ i,H.forest i=Halo.bios (H.steps i)

namespace Sight

def extent (M:W→ℕ)(w: W): Side→ℕ:= fun _=>M w
def slab (z:Side): Side:= 4*z
def ray (i:Page (extent M w)): Page M:= ⟨w,i.downW,i.good⟩
def slide' (i:Flap (extent M w)): Flap M:= ⟨w,i.offset,i.ok⟩
def big (n:Page M→Side)(i:Page (extent M w)) := slab i.bindW*n (ray w i) -- n implicit unsolved expected

def width (w: W)(z : Side) := ((slab z).val:ℝ)*S.P w
-- all outputs in units of original spacing, same in replicas
include H
lemma refined (i): Even ((big w (n:=n) i).val):= (H.even (ray w i)).mul_left _
lemma context (i):S.l (ray w i)*(big w (n:=n) i).val=width (S:=S) w i.bindW:=by
 rw [big, PNat.mul_coe,Nat.cast_mul]; unfold width; rw [mul_left_comm, H.phase]; rfl

def radar (i):= Carto G _ _ (refined H w i) (context H w i)
-- declare H before w order see Lean variable H before w

def stations (i: Flap (extent M w)): GridStep (radar H w i.prev) (radar H w i.next) :=⟨(S.frames (slide' w i)).line,(S.frames (slide' w i)).driftL,(S.frames (slide' w i)).addon⟩
private def sky' : Heir (big w (n:=n)) G where
  P:=width (S:=S) w
  hp:=fun z=>mul_pos (by exact_mod_cast (slab z).property) (S.hp w)
  l:=fun i=>S.l (ray w i)
  hl:=fun i=> S.hl (ray w i)
  climb i:= S.climb (slide' w i)
  maps:= radar H w
  frames:= stations H w
  sight:=fun _=> { pole:=0, space:= fun _ _=>0, run:=fun _ _=>0 }
def eternal:= sky' H w
-- stars
variable (hc:Common H)
include hc

def optic (i:Flap (extent M w)):= H.steps (slide' w i)
def bloom (i:Flap (extent M w)): StepData (big w (n:=n) i.next) (big w (n:=n) i.prev):= climbS (H.steps (slide' w i)) (slab i.volW)

def grove : Reel (eternal H w):= {
 clock:= fun i=>H.clock (ray w i), steps:= bloom H w, phase:= context H w, even:= refined H w
 deep:=fun i=>by have h:= H.deep (ray w i); refine h.trans (le_mul_of_one_le_left (by omega) (slab i.bindW).property) -- arg names
 realms:=fun _=>rfl, teeth:=fun i=> H.teeth (slide' w i), forest:=fun i=>bios (bloom H w i), landscape:=fun i=> Field.Square.proper ..
 stem:=fun i=> H.stem (ray w i), apex:=fun _=> H.apex w, Dtr:=fun i=> H.Dtr (slide' w i), pulses:=fun i=> H.pulses (slide' w i)
 meanF:=fun i=> H.meanF (slide' w i), bondF:=fun i=> H.bondF (slide' w i)
 moduli:= fun i=>by
    have hp:= H.moduli (slide' w i)
    let l:= slide' w i
    rw [H.realms,H.realms, hc] at hp
    exact arrange (S:=H.steps (slide' w i)) (slab i.volW) _ _ (refined H w i.prev) (refined H w i.next) _ _ (context H w i.prev) (context H w i.next) hp
 powers := fun i=>by
    obtain ⟨t,ht,hr⟩:=H.powers (slide' w i)
    refine ⟨t,?_,hr⟩; let L:=H.steps (slide' w i);rw [hc] at ht
    intro v; change Lab (barkN v) (dry v) (prism (climbS L _) (bios _) _ _) _; rw [axi]; exact ht v }
end Sight
end YM.RegulatorIR.Halo
