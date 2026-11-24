import YM.QuadraticLocal.Rebirth.Reprints
import YM.QuadraticLocal.Campaign.Stencil
/-!
# A copy- and test-blind workshop shape

Lawful through all Epochs in its range. Set up all currents before invoice. In particular
 no registration of support stencil at output index if another marker frees money later. This
 is a parameter of the analytic comparison on the local unmarked continuation, not a
 communicator for arbitrary volume across infinite copies. Keep proof `OriginNames.frontFine`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Syl
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
variable {V: Type} [Fintype V] [DecidableEq V] {R:Census V}
variable {G:Gauge}
/- `School K N h`: set j height, any ar-count and t arity weights with Ministry, permit j in the Burn schedule, from Setup.Op K.L.S from Account.Pl.T.Encoding. -/
structure School (vac:ℕ) where
    order : ℕ
    pieces : ℕ
    horizon : ℕ
    sense : pieces ≤ YM.AllOrder.Burn.horizon vac+2
    price : order ≤ YM.AllOrder.Burn.horizon vac+1
    tall : order+horizon ≤ YM.AllOrder.Burn.horizon vac+2

namespace School
open YM.AllOrder
variable {i j k u:ℕ}
local notation "p₀"=> AllOrder.Burn.horizon
local notation "Z"=> Burn.horizon k
variable (U:School k)
variable (h:PriceCompiler.StepStages j i)(hp:Burn.horizon k+2 ≤ i)
def room : Mentor.Opportunity j i := ⟨U.pieces,U.order+1,h,U.sense.trans hp,Nat.le_trans (Nat.add_le_add_right U.price 1) hp,Nat.le_add_left ..⟩
local notation "K"=> (School.room U h hp)
-- layout and authorized height for any future use. Geometry committed by Root.Payment.Meters.Supplier before φ stage. Allow decay.H≤y. Not resetting mark source budget scope.
variable {α ι : Type}{n:Side} {D: Earn.Passport n V} {w:V→ℝ} (t:V→ℕ) {a b:ℝ}
variable (M:ι→ Earn.Row D R G α)
lemma future (hv: Earn.Scene.Armada M w t a b U.order U.pieces U.horizon): Mentor.Cruise.Voter M a U.order (School.room U h hp|>.count) (School.room U h hp|>.stage) k i:=by
 let S:= U.pieces; have hf: U.order≤ i:= (U.price.trans ((Z+1).le_succ.trans hp)); have ht: U.horizon≤ i:= le_trans (Nat.le_add_left ..) ( U.tall.trans hp ); refine ⟨fun i=> ?_, hv.quota, le_rfl,?_⟩
 · have he:= Scene.Armada.degreeR t hv.toMinistry _ (hv.purchases.usable i); exact ⟨hv.honor _,hv.purchases.spend _,he.1.trans hf,he.2.1.trans ht⟩
 intro C; rw [Press.tall M C t hv.purchases.usable]; exact (Nat.add_le_add_left (hv.crew _) _).trans U.tall
lemma quality (V: Mentor.Opportunity j i) : 1 ≤ V.stage:= V.pos
end School
end YM.QuadraticLocal.Syl
