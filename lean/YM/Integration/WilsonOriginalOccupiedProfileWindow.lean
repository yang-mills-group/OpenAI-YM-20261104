import YM.Integration.WilsonOriginalOccupiedWindow

/-! Price a different true raw source salary at each optical date inside the full signed withdrawal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedProfileWindow
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open WilsonOriginalOccupiedWindow

include simple in
theorem original (n d a p:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → (∀j:Fin L,b+j.val+1 ≤ N) →
    (∀j:Fin L,(j.val:ℝ) ≤ C*(1+Real.log (H (b+j.val+1)))^d) →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(rows:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))) (s:marks.Mode) (S:Fin L → ℝ),
    (∀j,0 ≤ S j) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (rows j).regular (rows j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*((S j)^s.val.card*Poly.toll (rows j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),flags (Ψ (b+1)).p.threshold W=∅ →
      ‖∑j:Fin L,credit R marks (N:=N) (show b+1 ≤ b+j.val+1 by omega) Ψ (rows j) s W‖ ≤
      ((e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card)*
        ∑j:Fin L,(S j)^s.val.card/WilsonOriginalOccupiedDateShare.weight j.val:=by
  obtain ⟨floor,paid⟩:=WilsonOriginalOccupiedDatedInvoice.original R simple marks n d a p np load C e cp ep
  obtain ⟨i0,always⟩:=eventually_atTop.mp paid
  refine ⟨max floor i0,?_⟩
  intro b N per m k L high base live span way D Q π Γ Ψ course ticket rows s S sp restore W clear
  let B:ℝ:=(e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card
  let z:Fin L → ℂ:=fun j=>credit R marks (N:=N) (show b+1 ≤ b+j.val+1 by omega) Ψ (rows j) s W
  have each:∀j:Fin L, ‖z j‖ ≤ B*((S j)^s.val.card/WilsonOriginalOccupiedDateShare.weight j.val):=by
    intro j
    let q:=rows j
    letI:Countable q.I:=q.count
    letI:Nonempty q.X:=⟨q.x⟩
    have ftop:i0 ≤ b+j.val:=by omega
    have lower:floor ≤ b+1:=by omega
    have earlier:b+1 ≤ b+j.val+1:=by omega
    have age:b+j.val+1-(b+1)=j.val:=by omega
    have earn:=always _ ftop N per m k (b+1) (live j) earlier lower base (by simpa only [age] using span j)
      way D Q π Γ Ψ course ticket q.X q.I q.o q.A q.w q.positive q.regular q.hard q.earned q.forced q.x s W clear
    let D:=(WilsonOriginalOccupiedSalary.debit q.regular q.hard)^s.val.card
    have Dpos:0<D:=pow_pos (zero_lt_one.trans_le (le_max_left ..)) _
    let G₀:=(H (b+j.val+1))^a*Poly.toll q.w s/D
    have one:1 ≤ G₀*(S j)^s.val.card:=by
      dsimp only [G₀]
      rw [div_mul_eq_mul_div,one_le_div Dpos]
      simpa only [D,q,mul_assoc,mul_comm,mul_left_comm] using restore j
    have hold:G₀*‖z j‖ ≤ B/WilsonOriginalOccupiedDateShare.weight j.val:=by
      simpa only [G₀,D,z,credit,q,B,age] using earn.1
    calc ‖z j‖ ≤ (G₀*(S j)^s.val.card)*‖z j‖:=le_mul_of_one_le_left (norm_nonneg _) one
         _=(S j)^s.val.card*(G₀*‖z j‖):=by ring
         _ ≤ (S j)^s.val.card*(B/WilsonOriginalOccupiedDateShare.weight j.val):=
           mul_le_mul_of_nonneg_left hold (pow_nonneg (sp j) _)
         _=B*((S j)^s.val.card/WilsonOriginalOccupiedDateShare.weight j.val):=by ring
  change ‖∑j:Fin L,z j‖ ≤ B*_
  calc _ ≤ ∑j:Fin L,‖z j‖:=norm_sum_le _ _
       _ ≤ ∑j:Fin L,B*((S j)^s.val.card/WilsonOriginalOccupiedDateShare.weight j.val):=
         sum_le_sum fun j _=>each j
       _ = _:=Finset.mul_sum .. |>.symm

end YM.Integration.WilsonOriginalOccupiedProfileWindow
