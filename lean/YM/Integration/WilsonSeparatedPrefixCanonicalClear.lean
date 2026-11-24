import YM.Integration.WilsonReportHarvestLedgerFlat
import YM.Integration.WilsonReportHarvestResidentRootFee
import YM.Integration.WilsonSeparatedPrefixCanonicalWalk

/-! The complete ordinary reading of an original zero-ride marked board on
a globally clear held field. Every nonempty mode is billed at one of its own marks. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClear
open Set Finset Lattice RG Wilson Marker Source MergeProof Accent Push AbsoluteSums Extra.Histories
open Ac Extra.Trajectories GridApprox.Nil RG05Readout.Many
open Push.Local Extra.Multi ConnectedActivityE6 Pressure Extra.Iteration RG05Readout.Address
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{I:Type}[Fintype I][DecidableEq I]{J:Census I}
variable {P:Rep G n}{o:I → Site n}{w:I → ℝ}{α:ℝ}{F:Config G n → Poly J}

omit [Fintype I] in
theorem rooted {H:Support n → Config G n → Poly J}{ρ:ℝ} (bank:Towed w id H P.p.B α ρ)
    (positive:∀i,0<w i)(exponent:0≤α)(s:J.Mode)(x:Site n)(U:Config G n)
    (hit:∀Z,(H Z U).part s≠0 → x∈Z):
    Poly.toll w s*‖∑Z,(H Z U).part s‖≤ρ:=by
  obtain ⟨wallet,_,money,atoms⟩:=bank
  have invoice:=money x
  have cost:SumBudget (fun Z:Support n=>Poly.toll w s*‖(H Z U).part s‖) ρ:=by
    apply budget_mono invoice
    · intro z;exact mul_nonneg (Poly.worth positive s).le (norm_nonneg _)
    intro z
    by_cases active:(H z U).part s=0
    · rw [active,norm_zero,mul_zero];exact invoice.1 z
    change _≤ if x∈z then wallet z*Real.exp (α*(coverNumber P.p.B z:ℝ)) else 0
    rw [if_pos (hit z active)]
    exact ((Poly.member positive s _).trans ((atoms z).fares positive |>.2 U)).trans
      (le_mul_of_one_le_right ((atoms z).fares positive).1 (Real.one_le_exp (mul_nonneg exponent (Nat.cast_nonneg _))))
  have total:=cost.2.2
  rw [tsum_fintype] at total
  exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Poly.worth positive s).le).trans
    (by simpa only [Finset.mul_sum] using total)

theorem original (board:MenuBoard P (fun _:I=>(0:Three G n)) F o w α 1)
    (positive:∀i,0<w i)(exponent:0≤α)(U:Config G n)(clear:flags P.p.threshold U=∅)(s:J.Mode):
    Poly.toll w s*‖((P.eval U:ℂ)⁻¹ • F U).part s‖≤Real.exp (Fintype.card J.Mode:ℝ):=by
  obtain ⟨H,K,legal,hH,_,same⟩:=board.grants
  let z:=∑Z,H Z U
  have component(t:J.Mode):Poly.toll w t*‖z.part t‖≤1:=by
    by_cases present:t.val.Nonempty
    · obtain ⟨v,member⟩:=present
      rw [show z.part t=∑Z,(H Z U).part t from Poly.part_sum ..]
      apply rooted hH positive exponent t (o v) U
      intro Z nonzero
      by_contra absent
      exact nonzero ((legal.exp Z).1.toBorne.scope U t (fun missing=>absent (missing member)))
    · have eq:t=J.quiet:=Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp present)
      subst t
      change Poly.toll w J.quiet*‖(∑Z,H Z U).part J.quiet‖≤1
      rw [Poly.part_sum]
      simp [(legal.exp _).1.sil]
  have total:Poly.price w z≤(Fintype.card J.Mode:ℝ):=by
    exact (Finset.sum_le_sum (fun t _=>component t)).trans_eq (by simp)
  have read:((P.eval U:ℂ)⁻¹ • F U)=Poly.pass z:=by
    rw [same]
    have law:=(WilsonReportHarvestLedgerFlat.returned P (fun _:I=>(0:Three G n)) (fun _=>0) legal U clear).1
    have rows:(fun (_:I) (Z:Config G n)=>(0:Three G n).2.1 Z+(0:ℂ))=(fun _:I=>(0:Three G n).2.1):=by
      funext _ Z;apply add_zero
    have m:Mach J (fun _:I=>(0:Three G n).2.1 U+(0:ℂ))=0:=by simp [Mach]
    change (P.eval U:ℂ)⁻¹ • restore P (fun (_:I) Q=>(0:Three G n).2.1 Q+(0:ℂ))
      (fun _=>profile P.activities (0:Three G n).2.2) H K U=Poly.pass (Mach J (fun _:I=>(0:Three G n).2.1 U+(0:ℂ))+z) at law
    rw [rows,m,zero_add] at law
    exact law
  rw [read]
  exact (Poly.member positive s _).trans ((Poly.pass_budget positive _).trans (Real.exp_monotone total))

end YM.Integration.WilsonSeparatedPrefixCanonicalClear
end
