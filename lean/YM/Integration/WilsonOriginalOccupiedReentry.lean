import YM.Integration.WilsonOriginalOccupiedOptical
import YM.QuadraticLocal.Startup.Arbor

/-! Rescale only occupied marker costs while keeping every actual quiet forced activity unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedReentry
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] {J:Census V}
variable {G:Gauge} {n:Side} {P:Rep G n} {o:V → Site n} {X:Type}
def busy (z:Poly J):Poly J:=Poly.inject fun s=>if s=J.quiet then 0 else z.part s

private theorem busy_part (z:Poly J)(s:J.Mode):(busy z).part s=if s=J.quiet then 0 else z.part s:=rfl

private theorem price (w:V → ℝ)(wp:∀v,0<w v)(r:ℝ)(h:1 ≤ r)(z:Poly J):
    Poly.price (Stoop.radius w r) (busy z) ≤ r⁻¹*Poly.price w z:=by
  unfold Poly.price
  rw [mul_sum]
  apply sum_le_sum
  intro s _
  have r0:0 ≤ r⁻¹:=inv_nonneg.mpr (zero_le_one.trans h)
  change Poly.toll (Stoop.radius w r) s*‖if s=J.quiet then 0 else z.part s‖ ≤ _
  by_cases empty:s=J.quiet
  · rw [if_pos empty,norm_zero,mul_zero]
    exact mul_nonneg r0 (mul_nonneg (Poly.worth wp s).le (norm_nonneg _))
  · rw [if_neg empty,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (Stoop.shrink w s empty wp h) (norm_nonneg _)

theorem original (A:Hard X P.p P.activities.forced P.activities.K o J) (w:V → ℝ)
    (wp:∀v,0<w v)(r κ h:ℝ)(rp:1 ≤ r)(room:2*h ≤ r)(kp:0 ≤ κ)(small:κ ≤ 1/2)
    (rent:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent (κ^2))
    (old:A.Paid w P.p.B P.p.supportExponent (h*κ)):
    A.Paid (Stoop.radius w r) P.p.B P.p.supportExponent κ:=by
  obtain ⟨z,nonnegative,gauge,quiet⟩:=rent.earns
  obtain ⟨f,heard,account⟩:=old.wages
  let v:=Stoop.radius w r
  have rpos:0<r:=zero_lt_one.trans_le rp
  have vp:∀j,0<v j:=fun j=>div_pos (wp j) rpos
  let g:=fun i=>Poly.bead J (z i:ℂ)+busy (f i)
  have parts (i:ℕ)(s:J.Mode):(g i).part s=(if s=J.quiet then (z i:ℂ) else (f i).part s):=by
    by_cases eq:s=J.quiet
    · simp [g,busy_part,Poly.bead,Poly.part_send,eq]
    · simp [g,busy_part,Poly.bead,Poly.part_send,eq]
  have value (i:ℕ):Poly.price v (g i) ≤ z i+r⁻¹*Poly.price w (f i):=by
    refine (Poly.addition vp _ _).trans ?_
    rw [show Poly.price v (Poly.bead J (z i:ℂ))=z i by simp [Poly.bead,abs_of_nonneg (nonnegative i)]]
    exact add_le_add le_rfl (price w wp r rp (f i))
  refine ⟨g,?_,?_⟩
  · intro i x U s
    rw [parts]
    by_cases eq:s=J.quiet
    · subst s;rw [if_pos rfl,A.quiet]; exact ⟨by simpa using gauge i U,rfl⟩
    · rw [if_neg eq];exact heard i x U s
  · intro root
    let S:=fun i=>(P.activities.forced i).support
    let a:=P.p.supportExponent
    let weigh:=fun i=>Real.exp (a*coverNumber P.p.B (S i))
    let q:=fun i=>if root∈S i then z i*weigh i else 0
    let F:=fun i=>if root∈S i then Poly.price w (f i)*weigh i else 0
    have each (i:ℕ):(if root∈S i then Poly.price v (g i)*weigh i else 0) ≤ q i+r⁻¹*F i:=by
      by_cases lives:root∈S i
      · simp only [q,F,if_pos lives]
        exact (mul_le_mul_of_nonneg_right (value i) (Real.exp_pos _).le).trans_eq (by ring)
      · simp [lives,q,F]
    have rh:r⁻¹*h ≤ 1/2:=(inv_mul_le_iff₀ rpos).2 (by linarith)
    have bound:κ^2+r⁻¹*(h*κ) ≤ κ:=by
      nlinarith only [mul_le_mul_of_nonneg_right rh kp,mul_le_mul_of_nonneg_right small kp]
    apply budget_of_sum
    · intro i
      split
      · exact mul_nonneg (Poly.nonnegative vp _) (Real.exp_pos _).le
      · rfl
    · intro D
      calc _ ≤ ∑i∈D,(q i+r⁻¹*F i):=sum_le_sum fun i _=>each i
           _ ≤ κ^2+r⁻¹*(h*κ):=by
             rw [sum_add_distrib,←mul_sum]
             exact add_le_add (budget_sum (quiet root) D) (mul_le_mul_of_nonneg_left (budget_sum (account root) D) (inv_nonneg.mpr rpos.le))
           _ ≤ _:=bound
end YM.Integration.WilsonOriginalOccupiedReentry
