import YM.AllOrder.Floe.Assembly
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent Iron
namespace PlanV
-- finite deposit rank.W widths shape per each Stage (prevents context leakage through future high). want all axes (through e≤N), reconstruction one horizon.BetaPost. Lower output horizon narrower than *incident* borrowing.
def index (i:Age) : ℕ:= i.e*i.e + (i.e-i.slots)
local notation "I"=>index
variable {i j:Age}
lemma ante (h:Age.before i j) : I i < I j:= by
 rcases h with h|⟨h,hp⟩; unfold index; apply lt_of_lt_of_le (b:=j.e*j.e) _ (by omega); calc
  _ ≤ i.e*i.e+i.e:= by omega
  _ < (i.e+1)*(i.e+1):=by nlinarith only [i.e.zero_le]
  _ ≤ j.e*j.e:= Nat.mul_le_mul h h
 unfold index; have h₁ : j.slots < i.slots:= by unfold Age.r at hp; omega
 have he:i.slots≤ i.e := i.paid; rw [h]; omega
lemma levies (p:ℕ)(i:Age)(h:index i≤p): i∈ tape p := Age.in_scope.mpr ((Nat.le_mul_of_pos_right i.e (lt_of_lt_of_le (by norm_num) i.senior)).trans ((le_add_of_nonneg_right (a:=i.e*i.e) (Nat.zero_le _)).trans h)) -- binder implicits
lemma bandkey (i:Age): index i ≤ i.e*i.e+i.e:= by unfold index; omega
lemma index_mono (i:Age) (h:i∈Age.scope N) : index i≤ N*N+N:= (bandkey _).trans (Nat.add_le_add (Nat.mul_le_mul (Age.in_scope.mp h) (Age.in_scope.mp h)) (Age.in_scope.mp h))
-- sufficient pre exponent hierarchy
open Rent
lemma power_boost (k:ℕ) : k≤ gateE k N +1:=by unfold gateE; omega

def heavy (N:ℕ) : ℕ→ℕ
 | 0=>1
 | k+1=> gateE (heavy N k) N+1
abbrev guard (N:ℕ) (i:Age):= heavy N (index i)
lemma heavy_mono (N:ℕ): Monotone (heavy N) := monotone_nat_of_le_succ fun n=> power_boost _
lemma guard_ok (N:ℕ): Aligned (guard N) N:= ⟨fun i=> heavy_mono N (Nat.zero_le _), fun h=> heavy_mono N (ante h)⟩

end PlanV
end YM.AllOrder.Floe.Step
