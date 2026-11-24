import YM.Integration.WilsonPhysicalExteriorCompensatedQuote
import YM.Integration.WilsonPhysicalExteriorFundedRows

/-! The literal common-bulk experiment: the native torus source and
the independently filed full continuum MS word, with a separate
subtraction and normalization at every independently selected mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFiledWord
open Filter Real Finset PowerSeries Lattice PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Book MS.Book.Program MS.Tide MS.Fleet MS.Tone
open FVAAlt2 Lobby FVA2 Register RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorIndependentPrice WilsonPhysicalExteriorIndependentWord
open WilsonPhysicalExteriorRegisteredRows WilsonPhysicalExteriorRunningRows
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}{I:Type}{n:ℕ}
variable (R:Run G) (M:MS_Data G O) (Q:Prescription B)
local notation "PS" => PowerSeries ℂ

private theorem identity (P:Team) (u:ℝ) (F:PS) : reprice P u u F=F := by
  let a:=shift P u
  have za:constantCoeff a=0:=(coeff_zero_eq_constantCoeff_apply _).symm.trans (share P u)
  have unit:IsUnit (coeff 1 a):=(ann P u).symm ▸ isUnit_one
  let b:=a.substInvOfIsUnit unit
  have zb:constantCoeff b=0:=constantCoeff_substInvOfIsUnit ..
  change first P u (undo P u F)=_
  have ex:first P u (undo P u F)=PowerSeries.subst a (PowerSeries.subst b F):=by
    calc
      _=PowerSeries.subst a (undo P u F):=congrFun (PowerSeries.coe_substAlgHom ..) _
      _=_:=congrArg _ (congrFun (PowerSeries.coe_substAlgHom ..) F)
  rw [ex,PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' zb)
    (PowerSeries.HasSubst.of_constantCoeff_zero' za)]
  dsimp only [b]
  rw [PowerSeries.subst_substInvOfIsUnit_left _ za,PowerSeries.X_subst]

def finite (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i)) (v eps:Fin n→ℝ) (u:ℝ)
    (T:Trial I (Fin n)) (w:I) : PS :=
  C (WilsonPhysicalExteriorSlotReference.engineering eps (labels d b))*
    inserted R Q (labels d b) v (u-T.profile.θ w) (situated T w)

def independent (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i)) (v eps:Fin n→ℝ) (u:ℝ)
    (T:Trial I (Fin n)) (w:I) (x:Fin n→QP) : PS :=
  C (WilsonPhysicalExteriorSlotReference.ratio eps (spacing T w) (labels d b))*
    ∑a:Array B d,rate Q (labels d b) v (u-T.profile.θ w) (u-T.profile.θ w) a*
      PowerSeries.mk (fun k=>tour M (fun i=>owner (a i)) u x univ k)

private theorem labels_read (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i))
    (v:Fin n→ℝ) (y e:ℝ) {N:Side} (s:Fin n→Site N) :
    readings R Q (labels d b) v y y e s =
      ∑a:Array B d,rate Q (labels d b) v y y a*newEra R.metals.O
        (basisR R) Q y (fun i=>owner (a i)) s e := by
  unfold readings
  apply sum_congr rfl;intro a _;rw [identity]
  simp only [labels]

private theorem recorded (hG:G.Simple) (taylor:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i)) (v eps:Fin n→ℝ) (u:ℝ) (T:Trial I (Fin n)) (w:I) :
    finite R Q d b v eps u T w=
      C (WilsonPhysicalExteriorSlotReference.ratio eps (spacing T w) (labels d b))*
      ∑a:Array B d,rate Q (labels d b) v (u-T.profile.θ w) (u-T.profile.θ w) a*
        newEra R.metals.O (basisR R) Q (u-T.profile.θ w) (fun i=>owner (a i)) (situated T w) (spacing T w) := by
  rw [←labels_read R Q d b]
  exact WilsonPhysicalExteriorIndependentWord.measured R Q M hG taylor (labels d b) v eps _ _
    (spacing T w) (situated T w) (exp_pos _).ne'

private theorem account (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i)) (v:Fin n→ℝ)
    (y:ℝ) (ρ:ℂ) (F X:Array B d→PS) (k:ℕ) :
    coeff k (C ρ*(∑a:Array B d,rate Q (labels d b) v y y a*F a)-
      C ρ*(∑a:Array B d,rate Q (labels d b) v y y a*X a))=
    ρ*WilsonPhysicalExteriorCompensatedQuote.total Q d b v y y k (fun a l=>coeff l (F a)-coeff l (X a)) := by
  rw [←mul_sub,coeff_C_mul]
  apply congrArg (fun x:ℂ=>ρ*x)
  let sep:Fintype (Array B d):=@Pi.instFintype (Fin n) (fun i=>Glyph B (d i))
    (fun i j=>Classical.propDecidable (i=j)) (Fin.fintype n) (fun _=>inferInstance)
  let placed:Fintype (Array B d):=@Pi.instFintype (Fin n) (fun i=>Glyph B (d i))
    (instDecidableEqFin n) (Fin.fintype n) (fun _=>inferInstance)
  have roster:@Finset.univ (Array B d) sep=@Finset.univ (Array B d) placed :=
    congrArg (fun t:Fintype (Array B d)=>@Finset.univ (Array B d) t) (Subsingleton.elim _ _)
  have paid:=(WilsonPhysicalExteriorCompensatedQuote.signed Q d b v y y k F X).symm
  rw [roster] at paid
  exact paid

/-- Every actual measured finite term enters before the signed subtraction.
The target uses the independently determined MS marked amplitudes. -/
theorem coefficient (hG:G.Simple) (taylor:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i)) (v eps:Fin n→ℝ) (u:ℝ)
    (T:Trial I (Fin n)) (w:I) (x:Fin n→QP) (k:ℕ) :
    coeff k (finite R Q d b v eps u T w-independent M Q d b v eps u T w x)=
      WilsonPhysicalExteriorSlotReference.ratio eps (spacing T w) (labels d b)*
        WilsonPhysicalExteriorCompensatedQuote.total Q d b v (u-T.profile.θ w) (u-T.profile.θ w) k
          (fun a l=>Lobby.evaluateR R.metals.O (basisR R) Q (fun i=>owner (a i)) T u l w-
            tour M (fun i=>owner (a i)) u x univ l) := by
  let y:=u-T.profile.θ w
  let X (a:Array B d):PS:=PowerSeries.mk (fun l=>tour M (fun i=>owner (a i)) u x univ l)
  let F (a:Array B d):PS:=newEra R.metals.O (basisR R) Q y (fun i=>owner (a i)) (situated T w) (spacing T w)
  rw [recorded R M Q hG taylor d b v eps u T w]
  unfold independent
  have e:=account Q d b v y (WilsonPhysicalExteriorSlotReference.ratio eps (spacing T w) (labels d b)) F X k
  simpa only [F,X,PowerSeries.coeff_mk,Lobby.evaluateR,y] using e

/-- Including unequal marker spacings costs exactly the engineering
degree of their true declared slots. -/
theorem sharp (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B (d i)) (e T:ℝ) (eps:Fin n→ℝ)
    (he:0<e) (hT:0<T) (paid:∀i,e/T≤eps i) :
    ‖WilsonPhysicalExteriorSlotReference.ratio eps e (labels d b)‖≤T^(∑i,d i) := by
  have hv (i:Fin n):0<eps i:=(div_pos he hT).trans_le (paid i)
  have paid' (i:Fin n):e/eps i≤T:=by
    apply (div_le_iff₀ (hv i)).mpr
    rw [mul_comm];exact (div_le_iff₀ hT).mp (paid i)
  have h:WilsonPhysicalExteriorSlotReference.ratio eps e (labels d b)=
      ((∏i,(e/eps i)^(d i):ℝ):ℂ):=by simp [WilsonPhysicalExteriorSlotReference.ratio,labels]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (prod_nonneg fun i _=>pow_nonneg (div_nonneg he.le (hv i).le) _)]
  calc
    _≤∏i,T^(d i):=prod_le_prod (fun i _=>pow_nonneg (div_nonneg he.le (hv i).le) _)
      (fun i _=>pow_le_pow_left₀ (div_nonneg he.le (hv i).le) (paid' i) _)
    _=_:=prod_pow_eq_pow_sum _ _ _

end YM.Integration.WilsonPhysicalExteriorFiledWord
end
