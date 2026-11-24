import YM.Integration.WilsonOriginalPublicNodalFiling

/-! The occupied constant letters and their true normalized vacuum in the
comparison on the original older Wilson law and the independent public board. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
namespace YM.Integration.WilsonOriginalPublicNodalUnits
open Finset PowerSeries Lattice Wilson RG Labels Source XSpace Pert.Asymptotics
open RegulatorIR.FVAAlt2 PhysicalNext.Repeat.Legato Extra.Histories
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOriginalPublicNodalTransport (group)
open WilsonPositionProgramCopyTop (planted normalized)
open WilsonOriginalPublicNodalFiling (residual printed)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)(z:I→ Cover)
    (a:Columns R d)(S:Finset I)(unit:∀i,i∉S→a i=0)

theorem product (n:Side)(U:Config G n):
    group R d z a n U=∏i,(R.family.localSection (d i)).places (Pi.single (a i) 1) (wrap n (z i)) U:=by
  simpa only [group,Sound.Figure.prop,Boot.scout,Function.comp_apply,Finset.prod_apply]
    using congrFun (Boot.combined R univ d a z n) U

include unit in
theorem field (n:Side):
    group R d z a n=group R (fun i:S=>d i) (fun i:S=>z i) (fun i:S=>a i) n:=by
  funext U
  rw [product R d z a n U,product R (fun i:S=>d i) (fun i:S=>z i) (fun i:S=>a i) n U]
  rw [Finset.prod_coe_sort S (fun i=>(R.family.localSection (d i)).places (Pi.single (a i) 1) (wrap n (z i)) U)]
  apply (Finset.prod_subset (Finset.subset_univ S) _).symm
  intro i _ hi
  rw [unit i hi]
  exact congrFun (R.makes.sections (d i)).unit _

include unit in
omit [LinearOrder I] in
theorem depth:
    Kick.depthF univ d a=Kick.depthF univ (fun i:S=>d i) (fun i:S=>a i):=by
  unfold Kick.depthF
  rw [Finset.sum_coe_sort S (fun i=>((R.family.labels.level (d i)).grades (a i)).2)]
  apply (Finset.sum_subset (Finset.subset_univ S) _).symm
  intro i _ hi
  rw [unit i hi,Frame.zero_degree]

include unit in
theorem paper (P:Period)(tree:P.Tree):
    normalized R P d z a tree=normalized R P (fun i:S=>d i) (fun i:S=>z i) (fun i:S=>a i) tree:=by
  have common:planted R P d z a=planted R P (fun i:S=>d i) (fun i:S=>z i) (fun i:S=>a i):=by
    funext U
    exact Complex.ofReal_inj.mp (congrFun (field R d z a S unit P.side) U)
  unfold normalized
  rw [common]

variable {N per K u:ℕ}
include unit in
theorem reduced (P:Period)(tree:P.Tree)(uk:u≤K)(U:Config G (R.family.side u per))(q:ℕ)(g:ℝ):
    residual R d z P tree (N:=N) uk U a q g =
      residual R (fun i:S=>d i) (fun i:S=>z i) P tree (N:=N) uk U (fun i:S=>a i) q g:=by
  unfold WilsonOriginalPublicNodalFiling.residual printed
  rw [field R d z a S unit,depth R d a S unit,paper R d z a S unit P tree]

omit R in
private theorem vacuumSeries (P:Period)(tree:P.Tree):
    Taylor.expandTaylor (tree.basis G) (fun _=> (1:ℂ))=1:=by
  ext1 j
  rw [Taylor.expandTaylor,PowerSeries.coeff_mk]
  cases j with
  | zero=>simp [Taylor.divided_zero]
  | succ j=>
    rw [PowerSeries.coeff_one,if_neg (Nat.succ_ne_zero _)]
    apply Taylor.from_real (tree.basis G)
    intro W
    rw [Taylor.divided_eval,iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _) (1:ℂ)]
    simp

theorem blank (P:Period)(tree:P.Tree)(unmarked:∀i,a i=0):
    normalized R P d z a tree=1:=by
  have common:planted R P d z a=fun _=>1:=by
    funext U
    apply Complex.ofReal_inj.mp
    change group R d z a P.side U=((1:ℝ):ℂ)
    rw [product]
    simp only [Complex.ofReal_one]
    apply prod_eq_one
    intro i _
    rw [unmarked i]
    exact congrFun (R.makes.sections (d i)).unit _
  unfold normalized
  rw [common]
  change Bare.normalized tree G (Taylor.expandTaylor (tree.basis G) (fun _=> (1:ℂ)))=1
  rw [vacuumSeries,Bare.normalize_unit]

/-- Even in a nonempty occupied mask, a genuinely unit original tuple has no
signed residual, at any of the two periods or any held Gibbs configuration. -/
theorem original (P:Period)(tree:P.Tree)(unmarked:∀i,a i=0)(kn:K≤N)(uk:u≤K)
    (U:Config G (R.family.side u per))(q:ℕ)(g:ℝ):
    residual R d z P tree (N:=N) uk U a q g=0:=by
  have groupOne:group R d z a (R.family.side K per)=fun _=>1:=by
    funext B
    rw [product]
    apply prod_eq_one
    intro i _
    rw [unmarked i]
    exact congrFun (R.makes.sections (d i)).unit _
  have height:Kick.depthF univ d a=0:=by
    unfold Kick.depthF
    exact sum_eq_zero fun i _=>by rw [unmarked i,Frame.zero_degree]
  unfold WilsonOriginalPublicNodalFiling.residual printed
  rw [groupOne,actualTransport_const R.family R.makes kn (1:ℂ) uk U,blank R d z a P tree unmarked,height]
  simp [PowerSeries.coeff_one]

end YM.Integration.WilsonOriginalPublicNodalUnits
end
