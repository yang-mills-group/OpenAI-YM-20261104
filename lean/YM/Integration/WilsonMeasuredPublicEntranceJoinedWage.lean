import YM.Integration.WilsonMeasuredPublicEntranceTwoHostEar
import YM.Integration.WilsonReflectedPublicCommonSoftLaw
/-! Both real occupied wages and the full regular test, from the same
individually fitted original public Wilson fields, at arbitrary grades. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceJoinedWage
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonThermometerUnitFilingFieldRange WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonMeasuredPublicEntranceOrderedPeers
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){V:Type}[Fintype V](d:V → ℕ)
local notation "C" => R.family
local notation "H" f:max => R.family.path.levels.clock.hatBeta f
local notation "P" N:max p:max f:max => R.family.path.rep N p f
local notation "Ω" => fun i=>orbitCost ((C).labels.level (d i))
local notation "w₀" f:max => WilsonReflectedPublicMountedInvoice.wage R f

def money (f:ℕ)(q:V → ℕ)(z:Bool)(i:V):ℝ:=
  if z then (2+Ω i)*((H f)^(q i+d i))⁻¹ else w₀ f
def printed {f p:ℕ}(X E:∀i,Coefficient ((C).labels.level (d i)) ((C).side f p))(z:Bool)(i:V):
    Coefficient ((C).labels.level (d i)) ((C).side f p):= if z then E i else X i

theorem original (simple:G.Simple):
    ∀ᶠ f:ℕ in atTop,∀(p K N:ℕ)(fk:f ≤ K)(kn:K ≤ N)(A:∀i,Arm R (d i) N p f K)
      (q:V → ℕ)(c:V → ℂ)(row:V → Three G ((C).side f p))(X E:∀i,Coefficient ((C).labels.level (d i)) ((C).side f p)),
    (∀i,WilsonReflectedPublicGuardedColumns.Joined R (A i) fk kn (c i) (row i) (w₀ f) (Ω i*(1+w₀ f)) ((2+Ω i)*((H f)^(q i+d i))⁻¹) (X i) (E i)) →
    let he:=printed R d X E
    let B:=money R d f q
    (∀z v,0≤B z v) ∧ (∀z v,(he z v).Format (A v).o (C).params (P N p f)) ∧
    (∀z v,(he z v).remBound (A v).o (P N p f) (LocalComparison.forcedDivisor (C) f) (B z v)) ∧
    (∀v z t,WilsonSeparatedPrefixCanonicalMounted.salary R d f p (he z) (B z) v+B t v≤(H f)^9) ∧
    ∀v U,‖incidence (N:=N) R d (fun i=>(A i).o) (he false) v U‖≤WilsonReflectedPublicCommonSoftLaw.gross R (d v) f ∧
      ‖incidence (N:=N) R d (fun i=>(A i).o) (he true) v U‖≤WilsonReflectedPublicCommonSoftLaw.net R (d v) f (q v):=by
  have rise:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  let reserve:ℝ:=∑v:V,(6+4*Ω v)
  filter_upwards [rise.eventually_ge_atTop reserve,rise.eventually_ge_atTop 3] with f reserved large
  change 3≤H f at large
  have ample(v:V):6+4*Ω v≤H f:=(Finset.single_le_sum (fun i _=>show 0≤6+4*Ω i by linarith only [orbitCost_one_le ((C).labels.level (d i))]) (Finset.mem_univ v)).trans reserved
  intro p K N fk kn A q c row X E filed he B
  have hp:1≤H f:=(R.family.path.levels.fits.delayed f).le
  have hz:0≤H f:=zero_le_one.trans hp
  have wage₀:0≤w₀ f ∧ w₀ f≤2*(H f):=by
    have logh:=Real.log_nonneg hp
    have arg:0<2+Real.log (H f):=by linarith
    have inner:0≤Real.log (2+Real.log (H f)):=Real.log_nonneg (by linarith)
    change 0≤1+Real.log (2+Real.log (H f)) ∧ 1+Real.log (2+Real.log (H f))≤2*(H f)
    constructor <;> linarith only [inner,hp,Real.log_le_sub_one_of_pos arg,Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hp)]
  have hm(v:V):0≤(2+Ω v)*((H f)^(q v+d v))⁻¹:=mul_nonneg (by linarith only [orbitCost_one_le ((C).labels.level (d v))]) (inv_nonneg.mpr (pow_nonneg hz _))
  have base(z:Bool)(v:V):0≤ B z v:=by cases z;exact wage₀.1;exact hm v
  have bounds (v:V):B false v≤(H f)^2 ∧ B true v≤(H f)^2 ∧
      ((C).labels.level (d v)).coeffSize (he false v).x ≤(H f)^2 ∧
      ((C).labels.level (d v)).coeffSize (he true v).x ≤(H f)^2:=by
    have op:=orbitCost_one_le ((C).labels.level (d v))
    have non:0≤Ω v:=zero_le_one.trans op
    have hq:2+Ω v≤H f:=by linarith only [ample v,op]
    have flat:(H f)≤(H f)^2:=by simpa only [pow_one] using pow_le_pow_right₀ hp (by omega:1≤2)
    have sb:B true v≤H f:=(mul_le_of_le_one_right (by linarith only [non] :0≤2+Ω v)
      (inv_le_one_of_one_le₀ (one_le_pow₀ hp : 1≤(H f)^(q v+d v)))).trans hq
    have two:2≤H f:=by linarith only [large]
    have hb:B false v≤(H f)^2:=wage₀.2.trans ((mul_le_mul_of_nonneg_right two hz).trans_eq (by ring))
    have a:=filed v
    have quoted:Ω v*(1+w₀ f)≤(H f)^2:=calc
      _≤Ω v*(3*H f):=mul_le_mul_of_nonneg_left (by linarith only [wage₀.2,hp]) non
      _=(3*Ω v)*(H f):=by ring
      _≤(H f)*(H f):=mul_le_mul_of_nonneg_right (by linarith only [ample v,op]) hz
      _=(H f)^2:=by ring
    exact ⟨hb,sb.trans flat,a.coordinate.trans quoted,a.difference.primary.trans (sb.trans flat)⟩
  refine ⟨base,?_,?_,?_,?_⟩
  · intro z v;cases z;exact (filed v).cash.1;exact (filed v).difference.form
  · intro z v;cases z;exact (filed v).cash.2;exact (filed v).difference.paid
  · intro v z t
    have cap (j:Bool):B j v≤(H f)^2:=by cases j;exact (bounds v).1;exact (bounds v).2.1
    have label (j:Bool):((C).labels.level (d v)).coeffSize (he j v).x≤(H f)^2:=by
      cases j;exact (bounds v).2.2.1;exact (bounds v).2.2.2
    have pow4:(H f)^4 ≤ (H f)^8:=pow_le_pow_right₀ hp (by omega)
    have pow2:(H f)^2 ≤ (H f)^8:=pow_le_pow_right₀ hp (by omega)
    calc
      _≤(H f)^6*(H f)^2+(H f)^2*(H f)^2+(H f)^2:=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (label z) (pow_nonneg hz _))
          (mul_le_mul_of_nonneg_left (cap z) (pow_nonneg hz _))) (cap t)
      _=(H f)^8+(H f)^4+(H f)^2:=by ring
      _≤(H f)^8+(H f)^8+(H f)^8:=add_le_add (add_le_add (le_refl _) pow4) pow2
      _=3*(H f)^8:=by ring
      _≤(H f)*(H f)^8:=mul_le_mul_of_nonneg_right large (pow_nonneg hz _)
      _=(H f)^9:=by ring
  · intro v
    exact WilsonReflectedPublicCommonSup.original R (A v) fk kn (c v) (row v) (q v) (X v) (E v) (filed v)

end YM.Integration.WilsonMeasuredPublicEntranceJoinedWage
end
