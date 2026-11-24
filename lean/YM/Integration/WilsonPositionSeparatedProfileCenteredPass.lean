import YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
import YM.Integration.WilsonPositionSeparatedProfileCenteredSource
import YM.MergeProof.North.Tan

/-! The exact normalized cell reassembly commutes with the original joint
Wilson density before evaluation at the held gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredPass
open Function Set MeasureTheory Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open RG05Readout.Harvest RG05Readout.Many RG05Readout.Records PhysicalNext.Repeat.Legato
open WilsonPositionSeparatedProfileCenteredBranch WilsonPositionSeparatedProfileCenteredSource
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] [DecidableEq I] {N p:ℕ}

omit [DecidableEq I] in
private theorem collected {j k:ℕ} (live:k≤j) (a:ℂ) (F:I→Goods G (R.family.side j p)) (budget:∀i,Integrable (F i) (prior G _)):
    gust R.family.path N p j (a • ∑i,F i) k live=a • ∑i,gust R.family.path N p j (F i) k live:=by
  induction live using Nat.decreasingInduction with
  | self=>simp only [gust_base]
  | of_succ b hb ih=>
    have fee (i:I):=gust_live R.family.path N p j (F i) (budget i) hb
    rw [gust_step R.family.path N p j _ hb,ih,StepData.push_smul _ _ _ _ (integrable_finsetSum' _ fun i _=>fee i),
      Float.push_list _ fee Finset.univ (R.family.path.levels.transition_mass ..)]
    simp_rw [←gust_step R.family.path N p j _ hb]

omit [DecidableEq I] in
theorem weighted {k:ℕ} (top:k≤N) (a:ℂ) (F:I→Goods G (R.family.side N p)) (smooth:∀i,Continuous (F i)):
    dyes R.family k N p top (a • ∑i,F i)=a • ∑i,dyes R.family k N p top (F i):=by
  let X (i:I) (U:Config G (R.family.side N p)):ℂ:=((R.family.path.rep N p N).eval U:ℂ)*F i U
  have fee (i:I):Integrable (X i) (prior G _):=dye_grow R.makes (smooth i)
  have paper:(fun U=>((R.family.path.rep N p N).eval U:ℂ)*(a • (∑i,F i)) U)=a • ∑i,X i:=by
    funext U;simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,X,←Finset.mul_sum];ring
  unfold dyes;rw [paper,collected R top a X fee]

theorem journey_row {k:ℕ} (top:k+1≤N) (F:Bin G (R.family.side N p)) (well:timely F) (g:Body):
    journey R.family p k N 0 (arises R.family p N k top F) g=
      (Fintype.card (Bud R.family p k):ℂ)⁻¹ • ∑i:Bud R.family p k,dyes R.family k N p (k.le_succ.trans top) (arrangement R N p top F g i):=by
  let S:=R.family.path.levels.clock.op k p
  let β:=R.family.path.β N p (k+1)
  have row (i:Bud R.family p k):S.push β (sailS R.family k p (arises R.family p N k top F) g i)=dyes R.family k N p (k.le_succ.trans top) (arrangement R N p top F g i):=by
    rw [show dyes R.family k N p (k.le_succ.trans top) (arrangement R N p top F g i)=S.push β (dyes R.family (k+1) N p top (arrangement R N p top F g i)) from gust_step ..,
      arrangement,covariance R N p top _ _ (well _)]
    rfl
  unfold journey Address.average blast
  simp only [pow_zero,one_smul]
  congr 1;exact Finset.sum_congr rfl fun i _=>row i

/-- The genuine weighted lower census is the earlier Wilson density of the
same global ultraviolet test, on every field and with its original vacuum. -/
theorem cutoff {k:ℕ} (D:I→ℕ) (v:(i:I)→Palette R.family (D i)) (r:ℝ) (Ψ:Wave I) (top:k+1≤N) {cap:ℝ}
    (rp:0<r) (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap) (room:r*cap+2*R.family.S.a k<R.family.S.radius p) (m:ℕ)
    (well:timely (constellation (C:=R.family) (p:=p) D v r Ψ top m)) (g:Body):
    journey R.family p k N 0 (arises R.family p N k top (constellation D v r Ψ top m)) g=
      dyes R.family k N p (k.le_succ.trans top) (constellation D v r Ψ (k.le_succ.trans top) m g):=by
  let X:=arrangement R N p top (constellation D v r Ψ top m) g
  let c:ℂ:=(Fintype.card (Bud R.family p k):ℂ)⁻¹
  have reg (i:Bud R.family p k):Continuous (X i):=(well _).comp (Wilson.continuous_pull ..)
  have before:c • ∑i,X i=constellation D v r Ψ (k.le_succ.trans top) m g:=by
    funext U;simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact assembled R.family D v r Ψ top rp enclosed room m g U
  rw [journey_row R top _ well g,←before,weighted R (k.le_succ.trans top) c X reg]

end YM.Integration.WilsonPositionSeparatedProfileCenteredPass
