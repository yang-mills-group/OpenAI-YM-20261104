import YM.Integration.WilsonOriginalOccupiedDatedInvoice

/-! The complete signed occupied optical correction accumulated on a single original posterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedWindow
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

structure Slice {V:Type} [DecidableEq V] (J:Marker.Census V) {t per:ℕ}
    (P:RG.Rep G (R.family.side t per)) where
  X : Type
  I : Type
  count : Countable I
  x : X
  o : V → Site (R.family.side t per)
  A : Gallery X I o P J
  w : V → ℝ
  positive : ∀v,0<w v
  regular : ℝ
  hard : ℝ
  earned : A.E.Paid w P.p.B P.p.supportExponent regular
  forced : A.K.Paid w P.p.B P.p.supportExponent (hard*κ t)

def credit {t b N per:ℕ} (bt:b ≤ t) (Ψ:∀j,RG.Rep G (R.family.side j per))
    (row:Slice R marks (Ψ t)) (s:marks.Mode) (W:Config G (R.family.side b per)):ℂ:=
  (((Ψ b).eval W:ℂ)⁻¹)*((gust R.family.path N per t (row.A.density row.x) b bt W).part s-
    (gust R.family.path N per t (fun U=>((Ψ t).eval U:ℂ) • Poly.pass (row.A.E.log row.x U)) b bt W).part s)

include simple in
theorem original (n d a p:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → (∀j:Fin L,b+j.val+1 ≤ N) →
    (∀j:Fin L,(j.val:ℝ) ≤ C*(1+Real.log (H (b+j.val+1)))^d) →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(rows:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))) (s:marks.Mode),
    (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (rows j).regular (rows j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*Poly.toll (rows j).w s) →
    ∀W:Config G (R.family.side (b+1) per),flags (Ψ (b+1)).p.threshold W=∅ →
      ‖∑j:Fin L,credit R marks (N:=N) (show b+1 ≤ b+j.val+1 by omega) Ψ (rows j) s W‖ ≤
      (e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card:=by
  obtain ⟨floor,paid⟩:=WilsonOriginalOccupiedDatedInvoice.original R simple marks n d a p np load C e cp ep
  obtain ⟨i0,always⟩:=eventually_atTop.mp paid
  refine ⟨max floor i0,?_⟩
  intro b N per m k L high base live span way D Q π Γ Ψ course ticket rows s restore W clear
  let B:ℝ:=(e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card
  let z:Fin L → ℂ:=fun j=>credit R marks (N:=N) (show b+1 ≤ b+j.val+1 by omega) Ψ (rows j) s W
  by_cases empty:L=0
  · subst L;simp only [Finset.univ_eq_empty,Finset.sum_empty,norm_zero]
    exact mul_nonneg (mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)) (Nat.cast_nonneg _)
  have bN:b+1 ≤ N:=(by simpa using live ⟨0,Nat.pos_of_ne_zero empty⟩)
  have bp:0 ≤ B:=mul_nonneg (mul_nonneg ep.le (pow_nonneg (ActualRunKernelPackets.regulator_pos R N per (b+1) bN).le _)) (Nat.cast_nonneg _)
  have each:∀j:Fin L, ‖z j‖ ≤ B*(1/WilsonOriginalOccupiedDateShare.weight j.val):=by
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
    have enough:1 ≤ (H (b+j.val+1))^a*Poly.toll q.w s/(WilsonOriginalOccupiedSalary.debit q.regular q.hard)^s.val.card:=by
      apply (one_le_div (pow_pos (zero_lt_one.trans_le (le_max_left ..)) _)).2;exact restore j
    have step:=earn.2 enough
    simpa only [B,z,credit,q,age,one_div,div_eq_mul_inv,one_mul] using step
  change ‖∑j:Fin L,z j‖ ≤ B
  calc _ ≤ ∑j:Fin L,‖z j‖:=norm_sum_le _ _
       _ ≤ ∑j:Fin L,B*(1/WilsonOriginalOccupiedDateShare.weight j.val):=sum_le_sum fun j _=>each j
       _ = B*(1-1/((L:ℝ)+1)):=by
         rw [←mul_sum,Fin.sum_univ_eq_sum_range (fun k:ℕ=>1/WilsonOriginalOccupiedDateShare.weight k) L,
           WilsonOriginalOccupiedDateShare.total]
       _ ≤ B:=mul_le_of_le_one_right bp (sub_le_self _ (by positivity))

end YM.Integration.WilsonOriginalOccupiedWindow
