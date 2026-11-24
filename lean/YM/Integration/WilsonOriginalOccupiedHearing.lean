import YM.Integration.WilsonOriginalOccupiedCorridor
import YM.Integration.WilsonOriginalOccupiedClear
import YM.Integration.WilsonOriginalOccupiedTransport
import YM.Integration.WilsonOriginalOccupiedSource

/-! The same genuine lower conditional law for every signed hard-amplitude tap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedHearing
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedTap WilsonOriginalOccupiedSource WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b t:ℕ}
variable {V:Type} [DecidableEq V] [Fintype V] {marks:Marker.Census V}
variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (ticket:TicketP R.alloy R.kit D Q)
  {X I:Type} [Countable I] [Nonempty X] (o:V → Site (R.family.side t per))
  (A:Gallery X I o (Ψ t) marks)(w:V → ℝ)(wp:∀v,0<w v)

include course ticket way wp in
theorem original (floor:m ≤ b)(top:t ≤ N)(bt:b ≤ t){load:ℕ}
    (stage:∀i,b ≤ i → load ≤ R.alloy.B.a.clock.J i) (load_ok:∀s:marks.Mode,s.val.card ≤ load)
    (cap:∀i,b ≤ i → LocalComparison.forcedDivisor R.family i ≤ 1)
    (s:marks.Mode) (n:ℕ)(size:s.val.card ≤ n)(T q:ℂ)(inv:T*q=1)(small:‖q‖ ≤ 1)
    (regular:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)
    (paid:∀z∈nodes n T,(gallery z A).K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)
    (x:X)(W:Config G (R.family.side b per))(clear:flags (Ψ b).p.threshold W=∅):
    Poly.toll (wallet R w bt) s *
      ‖(((Ψ b).eval W:ℂ)⁻¹)*((gust R.family.path N per t (A.density x) b bt W).part s-
      (gust R.family.path N per t ((gallery 0 A).density x) b bt W).part s)‖ ≤
        (‖q‖*price n)*(shards marks s).card:=by
  let Z:=(fun z:ℂ=> (gallery z A).density x)
  let Y:=(fun z:ℂ=>(gust R.family.path N per t (Z z) b bt W).part s)
  let vac:=((Ψ b).eval W:ℂ)⁻¹
  let fee:=Poly.toll (wallet R w bt) s
  let J:=fun i:Fin (n+1)=>T*node i
  have live (i:Fin (n+1)):J i∈nodes n T:=
    mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
  have pack (z:ℂ)(hz:z∈nodes n T):(gallery z A).Pays w (Ψ t).p.supportExponent 1 1:=⟨regular,paid z hz⟩
  have law:=(course.1.walk t (floor.trans bt) top).truep.valid
  have income (z:ℂ)(hz:z∈nodes n T):Integrable (Z z) (prior G _):=
    QuadraticLocal.Tariff.integrable marks o w wp (gallery z A) x (pack z hz) (Ψ t).p.exponent_pos.le law
  have stencil:=WilsonOriginalOccupiedTransport.original R (N:=N) (Z 1) (Z 0) (fun j=>Z (J j)) (weight q) s bt
    (income 1 (by simp [nodes])) (income 0 (by simp [nodes])) (fun i=>income _ (live i))
    (WilsonOriginalOccupiedSource.original A w wp s size T q inv paid x) W
  have physical : Z 1=A.density x:=funext (WilsonOriginalOccupiedSource.one A x)
  change Y 1 - Y 0 = ∑i:Fin (n+1),weight q i*Y (J i) at stencil
  have active : 0 < fee:=Poly.worth (positive R w wp bt) s
  have costs (i:Fin (n+1)):fee*‖vac*Y (J i)‖ ≤ (shards marks s).card:=by
    obtain ⟨K,L,_,bill,_,same⟩:=WilsonOriginalOccupiedCorridor.original R way D Q π Γ Ψ course ticket
      o (gallery (J i) A) w wp floor top bt stage load_ok cap (pack _ (live i))
    have e:=WilsonOriginalOccupiedClear.original L (positive R w wp bt) bill.1 x s W clear
    rw [same x] at e
    exact e
  have exact_read:vac*(Y 1-Y 0)=∑i:Fin (n+1),weight q i*(vac*Y (J i)):=by
    rw [stencil,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [←physical]
  change fee*‖vac*(Y 1-Y 0)‖ ≤ _
  rw [exact_read]
  calc
    _ ≤ fee*∑i:Fin (n+1),‖weight q i*(vac*Y (J i))‖:=mul_le_mul_of_nonneg_left (norm_sum_le ..) active.le
    _ = ∑i:Fin (n+1),‖weight q i‖*(fee*‖vac*Y (J i)‖):=by
      rw [mul_sum];apply sum_congr rfl;intro i _;rw [norm_mul];ring
    _ ≤ ∑i:Fin (n+1),‖weight q i‖*((shards marks s).card:ℝ):=
      sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (costs i) (norm_nonneg _)
    _ ≤ _:=by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (earned n q small) (Nat.cast_nonneg _)

end YM.Integration.WilsonOriginalOccupiedHearing
