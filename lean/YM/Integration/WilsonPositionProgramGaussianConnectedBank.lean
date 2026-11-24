import YM.Integration.WilsonPositionProgramGaussianMomentReturn

/-! The finite connected logarithm after one Gaussian hearing of the entire rooted intake. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianConnectedBank
open Finset MeasureTheory Multi Marker Next.SectorChange Next.Rank Comparison.RG02.Cumulants
open WilsonPositionProgramGaussianMomentBank WilsonPositionProgramGaussianMomentReturn WilsonPositionProgramDisjointWallet
open Extra.Trajectories (connected)
open scoped BigOperators Classical
variable {V I:Type}[DecidableEq V][Fintype V][DecidableEq I][Fintype I]{R:Census V}
  (Q:Matrix I I ℝ)(positive:Q.PosDef)(hQ:Q.IsSymm)(σ:ℝ)(diag:∀i,Q i i≤σ)

def price (R:Census V)(I:Type)[Fintype I](σ B:ℝ)(k:ℕ)(s:R.Mode):ℝ:=
  salary (R:=R) (fun u=>mobiusTop u.val.card) s *
    ((number R:ℝ)*difference R I σ B k*(max 1 (room R I σ B k))^(number R))

include positive diag in
theorem original (w:V→ℝ)(hw:∀v,0<w v)(p q:Hot R→Normal.poly I)(k:ℕ){B δ:ℝ}(hb:1≤B)(hd:0≤δ)
    (hp:∀i z,Poly.toll w i.val*‖Cloud.paint z (p i)‖≤B*(1+‖z‖)^k)
    (hq:∀i z,Poly.toll w i.val*‖Cloud.paint z (q i)‖≤B*(1+‖z‖)^k)
    (fee:∀i z,Poly.toll w i.val*‖Cloud.paint z (p i-q i)‖≤δ*(1+‖z‖)^k)(s:R.Mode):
    let a:=Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) p
    let b:=Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) q
    Poly.toll w s*‖(connected a).part s-(connected b).part s‖ ≤ δ*price R I σ B k s := by
  let a:=Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) p
  let b:=Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) q
  let C:=max 1 (room R I σ B k)
  have rows(i:R.Mode):=WilsonPositionProgramGaussianMomentReturn.original Q positive hQ σ diag w hw p q k hb hd hp hq fee i
  have blank(i:Hot R)(z:I→ℝ):Poly.toll w i.val*‖Cloud.paint z (q i-q i)‖≤δ*(1+‖z‖)^k:=by simp;positivity
  have other(i:R.Mode):=WilsonPositionProgramGaussianMomentReturn.original Q positive hQ σ diag w hw q q k hb hd hq hq blank i
  have normalized(t:Hot R→Normal.poly I):(Cloud.prescription Q hQ (Cloud.shift (0:I→ℝ)) t).part R.quiet=1:=by
    rw [Cloud.prescribed,driven_quiet]
    exact Cloud.wick_one ..
  have sig:0≤difference R I σ B k:=by
    unfold difference words stock salary WilsonMarkedInheritedGaussianMoment.charge
    have h:=zero_le_one.trans hb
    positivity
  let μ:(parts R).Mode→ℂ:=fun u=>mobiusTop u.val.card
  have bound:=common w hw μ (fun i=>a.part i.val) (fun i=>b.part i.val) s (le_max_left 1 _) (mul_nonneg hd sig)
    (fun i=>(rows i.val).1.trans (le_max_right _ _)) (fun i=>(other i.val).1.trans (le_max_right _ _))
    (fun i=>(rows i.val).2)
  change Poly.toll w s*‖(connected a).part s-(connected b).part s‖≤δ*price R I σ B k s
  rw [log_partition a (normalized p),log_partition b (normalized q)]
  apply bound.2.trans_eq
  unfold price μ number
  ring

end YM.Integration.WilsonPositionProgramGaussianConnectedBank
end
