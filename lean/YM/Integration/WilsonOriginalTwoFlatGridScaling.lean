import YM.Integration.WilsonOriginalTwoFlatGridRadius
import YM.Integration.WilsonMatrixTicketLanesQuota
import YM.Integration.IntrinsicProductLinearity
import YM.SharpGram.Clauses

/-! The unrestricted and flat measurements are linear in exactly the same
original numerator.  Normalize a finite roster by its *own* true paid
columns, and put the product of those prices back only once. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatGridScaling
open Function Filter Set Lattice RG Source Labels Wilson OPE Next.Rank Overlay Bid
open MergeProof Ribbons Accent ManyCopies Cells Extra.Histories RG16 RG16.Literal
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Set Function Filter MeasureTheory Next.UVStress
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "β" => (P).clock.hatBeta
local notation "a" => R.family.S.a
open WilsonOriginalTwoFlatGridCapture (word)

private theorem paidScale {d j N p:ℕ}(ready:(C).ref d ≤ j)(live:j≤N)(z:ℂ)(x:(C).label d):
    Spindle.paid C d j N p (z • x)=‖z‖*Spindle.paid C d j N p x:=by
  apply (mul_left_inj' (pow_ne_zero d ((C).S.a_pos j).ne')).mp
  rw [WilsonMatrixTicketLanesQuota.quota,mul_assoc,WilsonMatrixTicketLanesQuota.quota]
  exact SharpGram.quota_smul (p:=p) R.makes z x ready live

def gap (N p u:ℕ)(live:u≤N)(F:Cut C N p):ℂ:=
  (C).omega N p F-WilsonThermometerUnitFilingCoarse.reading R (N:=N)
    (credit C N p 0 F u live) u le_rfl

private theorem gapScale {N p u:ℕ}(live:u≤N)(F:Cut C N p)(cont:Continuous F)(z:ℂ):
    gap R N p u live (z • F)=z*gap R N p u live F:=by
  have cs:credit C N p 0 (z • F) u live=z • credit C N p 0 F u live:=by
    simpa using IntrinsicProductLinearity.credit_sum C N p 0 u live (fun _:Unit=>z) (fun _=>F) (fun _=>cont)
  have meas:(C).omega N p (z • F)=z*(C).omega N p F:=by
    unfold Family.omega Wilson.moment
    simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul]
  unfold gap WilsonThermometerUnitFilingCoarse.reading
  rw [cs,meas,gust_base,gust_base]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

variable {I:Type}[Fintype I](d:I→ℕ)
private theorem wordScale {j N p:ℕ}(live:j≤N)(o:I → Cover)(z:I→ℂ)(Y:∀i,(C).label (d i)):
    word R d j N p live o (fun i=>z i • Y i)=(∏i,z i) • word R d j N p live o Y:=by
  funext U
  simp only [word,Pi.smul_apply,smul_eq_mul,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (((C).linearO N p (d i) _).map_smul (z i) (Y i)) U

variable [DecidableEq I][Nonempty I]{r W pupil}(L:Package R.family W r pupil)
include L in
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}
    (stop:Stop C 0 J u)(B q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀{t:ℝ},0<t → t≤a (u+3) → a j<t → t≤(β j)^B*a j →
    ∀N p:ℕ,∀hN:j<N,∀o:I → Cover,(∀i,8*‖(C).S.gridPoint j (o i)‖≤t) →
    (Pairwise fun i i'=>2*a j*(((P).budget j).B:ℝ)^2 ≤
      ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    ∀Y:∀i,(C).label (d i),∀fare:I→ℝ,(∀i,0<fare i) →
      (∀i,Spindle.paid C (d i) j N p (Y i)≤fare i) → ∀uj:u≤j,
    ‖gap R N p u (uj.trans hN.le) (word R d j N p hN.le o Y)‖≤(∏i,fare i)*((β j)^q)⁻¹:=by
  have ready:∀ᶠj:ℕ in atTop,∀i,(C).ref (d i)≤j:=eventually_all.mpr fun i=>eventually_ge_atTop _
  filter_upwards [WilsonOriginalTwoFlatGridRadius.original R simple L d slow stop 0 B q,ready] with j bought allow
  intro t tp small fine span N p hN o inside apart Y fare positive income uj
  let V(i:I):=(↑(fare i):ℂ)⁻¹ • Y i
  have vfee(i:I):Spindle.paid C (d i) j N p (V i)≤(β j)^0:=by
    rw [show V i=(↑(fare i):ℂ)⁻¹ • Y i from rfl, paidScale R (allow i) hN.le,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg (positive i).le,pow_zero]
    exact inv_mul_le_one_of_le₀ (income i) (positive i).le
  have restored:(fun i=>(↑(fare i):ℂ) • V i)=Y:=by
    funext i
    have nz:(↑(fare i):ℂ)≠0:=by exact_mod_cast (positive i).ne'
    simp [V,smul_smul,nz]
  have approximate:=bought tp small fine span N p hN o inside apart V vfee uj
  have cont:Continuous (word R d j N p hN.le o V):=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  rw [←restored,wordScale,gapScale R _ _ cont,norm_mul,norm_prod]
  simp only [Complex.norm_real,Real.norm_of_nonneg (positive _).le]
  exact mul_le_mul_of_nonneg_left approximate (Finset.prod_nonneg fun _ _=>(positive _).le)

end YM.Integration.WilsonOriginalTwoFlatGridScaling
end
