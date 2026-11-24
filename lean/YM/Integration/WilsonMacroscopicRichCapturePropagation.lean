import YM.Integration.WilsonMacroscopicRichReportedPosterior
import YM.Integration.WilsonMacroscopicRichCaptureClass

/-! Propagate the complete filed capture density to the earlier physical field, with the original coarse normalizer at that field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCapturePropagation
open Function Set Lattice Wilson RG OPE OPE.Orbits Spec PhysMS Cells Push.GridApprox
open RG16 RG16.Literal Trace.Physical.GermGraph Source Labels RGComparison.Core16
open PhysicalNext.Repeat.Legato FilteredWilsonProduct FilteredIntrinsicGramReadout
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){u b N p:ℕ}

open private steps from YM.Integration.WilsonMacroscopicRichCaptureRoots

def returned (ub:u≤b)(h:ℕ)(Z:Config G (R.family.side b p)→ℂ)(V:Config G (R.family.side u p)):ℂ:=
  ((R.family.S.a u:ℂ)^h * pushTo R.family.path N p ub (fun U=>Z U/(R.family.S.a b:ℂ)^h) V) /
    ((R.family.path.rep N p u).eval V:ℂ)

theorem original (T:Slices R.family.path.levels p)(ub:u≤b)(bN:b≤N)(h:ℕ)
    (Y:Cut R.family N p)(Z:Config G (R.family.side b p)→ℂ)
    (accounts:credit R.family N p h Y b bN=Z):
    returned R (N:=N) ub h Z=WilsonMacroscopicRichReportedPosterior.observation R T (ub.trans bN) h Y:=by
  let C:=R.family
  let raw:Cut C N p:=fun U=>(bare (C.beta N p) U:ℂ)*Y U
  have ab:(C.S.a b:ℂ)^h≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
  have atB:(fun U=>Z U/(C.S.a b:ℂ)^h)=pushTo C.path N p bN raw:=by
    funext U
    rw [←accounts]
    change ((C.S.a b:ℂ)^h*pushTo C.path N p bN raw U)/(C.S.a b:ℂ)^h=_
    field_simp
  funext V
  have vacuum: (traversal T (ub.trans bN)).vacuum (G:=G) (line C.path p u N) V=(C.path.rep N p u).eval V:=
    congrFun (vacuum_eq T R.makes.wilson (ub.trans bN)) V
  have denom:((C.path.rep N p u).eval V:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (vacuum ▸ (Descent.positive (line C.path p u N) (traversal_ok T (ub.trans bN)) V).ne')
  unfold returned
  rw [atB,steps C.path N p ub bN raw]
  obtain hread:=WilsonMacroscopicRichReportedPosterior.density R T (ub.trans bN) h Y V
  change (credit C N p h Y u (ub.trans bN) V)/_=_
  rw [hread]
  exact (div_eq_iff denom).2 (mul_comm _ _)

variable {f:Extraction.Order}{S:Table R.family.book}{I:Type}[Fintype I]{d:I→ℕ}

theorem portfolio (F:Final R.family f S)(reader:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(T:Slices R.family.path.levels p)(ub:u≤b)(bN:b≤N)(h:ℕ)
    (v:(i:I)→(Climb.Bel R.family.book).Field (d i))(r:ℝ)(m:ℕ)(x : I → Cover)
    (Q:Grades d→store R.family h p b)(accounts:∀g,credit R.family N p h
      (WilsonReportingProductInvoice.source F reader J v r m N p x g) b bN=value (C:=R.family) h N p b (Q g)):
    returned R (N:=N) ub h (∑g,value (C:=R.family) h N p b (Q g)) =
      WilsonMacroscopicRichReportedPosterior.observation R T (ub.trans bN) h
        (field F reader J v r m x (N,p)):=by
  let C:=R.family
  let Y (g:Grades d):=WilsonReportingProductInvoice.source F reader J v r m N p x g
  have cont (g:Grades d):Continuous (Y g):=by
    change Continuous (∏ i,C.O N p (component F reader J v g r i) (location C.S m N p (x i)))
    rw [show (∏ i,C.O N p (component F reader J v g r i) (location C.S m N p (x i)))=
      fun U=>∏ i,C.O N p (component F reader J v g r i) (location C.S m N p (x i)) U
      from funext fun _=>Finset.prod_apply ..]
    exact continuous_finsetProd _ fun _ _=>C.continuousO ..
  apply original R T ub bN
  have original:field F reader J v r m x (N,p)=∑g,Y g:=by rw [field_expansion];rfl
  rw [original]
  have total:=IntrinsicProductLinearity.credit_sum C N p h b bN (fun _:Grades d=>(1:ℂ)) Y cont
  simp only [one_smul] at total
  rw [total]
  exact Finset.sum_congr rfl fun g _=>accounts g

end YM.Integration.WilsonMacroscopicRichCapturePropagation
