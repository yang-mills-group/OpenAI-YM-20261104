import YM.Integration.WilsonMaxwellThermometerBareIncidenceRate
import YM.XSpace.Diastole

/-! The original finite, fully reannounced public ground on a moving field.
Every finite co-ordinate of the elected ground layout is retained on the
separated Maxwell side before making a common first-order change. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFiledIncidenceRate
open Filter Set Finset Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement XSpace.Tornado
open WilsonMaxwellThermometerBareIncidenceRate
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)(V:Store G){n d:ℕ}

/-- On the very same auxiliary transaction, after applying the full filed
zero-order field counterterm, with its actual finite-dimensional wages. -/
theorem original {I:Fin n→Type} [∀j,Fintype (I j)]
    (B:∀j,Module.Basis (I j) ℂ (Sec G d)){K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀u:pack n,∀c∈M.Box,M.rel u c∈K →
    ∀p:Tags G d n,‖cooked W V d ⟨M,u,c⟩ 0 p-scene (M.rel u c) d (visor W V M d ∘ p)‖≤
      (C*M.spacing)*∏j,∑i,‖(B j).repr (visor W V M d (p j)) i‖:=by
  obtain ⟨C,hC,fee⟩:=moving W d (fun j i=>B j i) compact apart
  refine ⟨C,hC,?_⟩
  filter_upwards [fee] with M ok
  intro u c hc hk p
  let v (j:Fin n)(i:I j):ℂ:=(B j).repr (visor W V M d (p j)) i
  have bought:assembled d (fun j i=>B j i) v=visor W V M d ∘ p :=by
    funext j
    exact (B j).sum_repr _
  rw [plate0]
  simpa only [bought] using ok u c hc hk v

/-- The W/V ordinary quotient on a requested face, with true unit at the
complement, on the same positive denominator and actual moving configuration. -/
theorem faces {I:Fin n→Type} [∀j,Fintype (I j)]
    (B:∀j,Module.Basis (I j) ℂ (Sec G d)){K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀u:pack n,∀c∈M.Box,M.rel u c∈K →
    ∀p:Tags G d n,∀s:Finset (Fin n),
    let f:=missing p s
    ‖(∑w∈tally 0 n,if ∀j:Fin n,j∉s→w (some j)=0 then
      PowerSeries.coeff (w none) (numberA W d ⟨M,u,c⟩ (pulseU w (deck (V.layout W M d)) p) s) else 0)-
      scene (M.rel u c) d (visor W V M d ∘ f)‖≤
      (C*M.spacing)*∏j,∑i,‖(B j).repr (visor W V M d (f j)) i‖:=by
  obtain ⟨C,hC,fee⟩:=original W V B compact apart
  refine ⟨C,hC,?_⟩
  filter_upwards [fee] with M ok
  intro u c hc hk p s
  dsimp only
  simpa only [detail] using ok u c hc hk (missing p s)

end YM.Integration.WilsonMaxwellThermometerFiledIncidenceRate
