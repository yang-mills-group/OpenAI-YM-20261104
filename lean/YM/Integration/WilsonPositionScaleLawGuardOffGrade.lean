import YM.Integration.WilsonPositionScaleLawGuardGradeClock

/-! To every physical coupling order a fixed original field lives in its top homogeneous grade. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardOffGrade
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize Asymptotics
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGrade (grade)
open scoped Topology Classical Asymptotics
variable {ι X:Type*}[NormedAddCommGroup X]{l:Filter ι}

theorem power (g:ι→ℝ)(v:ι→X)(zero:Tendsto g l (𝓝 0))(q:ℕ)(C:ℝ)
    (bill:∀ᶠr in l,‖v r‖≤C*|g r|^(2*(q+1))):v=o[l] (fun r=>g r^q):=by
  have loss:Tendsto (fun r=>|g r|^(q+2)) l (𝓝 0):=by
    simpa only [abs_zero,zero_pow (by omega:q+2≠0)] using zero.abs.pow (q+2)
  have desc:Tendsto (fun r=>C*|g r|^(q+2)) l (𝓝 0):=by simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul loss
  apply isLittleO_iff.mpr;intro ε hε
  filter_upwards [bill,(tendsto_order.mp desc).2 ε hε] with r input small
  calc
    _≤C*|g r|^(2*(q+1)):=input
    _=(C*|g r|^(q+2))*|g r|^q:=by rw [show 2*(q+1)=q+2+q by omega,pow_add];ring
    _≤_:=by rw [Real.norm_eq_abs,abs_pow];exact mul_le_mul_of_nonneg_right small.le (pow_nonneg (abs_nonneg _) _)

theorem finite {I:Type*}[DecidableEq I](s:Finset I)(v:I→ι→X)(g:ι→ℝ)(small:∀i∈s,v i=o[l] g):
    (fun r=>∑i∈s,v i r)=o[l] g:=by
  induction s using Finset.induction_on with
  | empty=>
    apply isLittleO_iff.mpr;intro ε hε
    exact .of_forall fun r=>by simpa only [Finset.sum_empty,norm_zero] using mul_nonneg hε.le (norm_nonneg (g r))
  | @insert i s outside ih=>
    have base:=small i (Finset.mem_insert_self ..)
    have rest:=ih (fun j hj=>small j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert outside] using base.add rest

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:∀q,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q)
include H funded law in
theorem row (i:Fin (d+1))(lower:i.val<d)(q:ℕ)(O:S.Field d):
    (fun r=>grade R.family i (physical F J Z d r O))=o[trail] (fun r=>gθ r^q):=by
  obtain ⟨ρ,hρ,fields⟩:=WilsonPositionScaleLawGuardGradeClock.original Z M H ν F J d funded law i lower (q+1)
  obtain ⟨C,_,paid⟩:=fields O
  apply power gθ _ (funded.conforms hG) q C
  exact mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨ρ,hρ,fun u hu=>paid u hu.1 hu.2⟩

include H funded law in
theorem original (q:ℕ)(O:S.Field d):
    (fun r=>physical F J Z d r O-grade R.family (Fin.last d) (physical F J Z d r O))=o[trail] (fun r=>gθ r^q):=by
  let v(r:ℝ):=physical F J Z d r O
  let s:=Finset.univ.erase (Fin.last d)
  have lower (i:Fin (d+1))(hi:i∈s):i.val<d:=by
    have ne:=Finset.ne_of_mem_erase hi
    have lim:=i.isLt
    by_contra! neg;apply ne;apply Fin.ext;change i.val=d;omega
  have priced:=finite s (fun i r=>grade R.family i (v r)) (fun r=>gθ r^q) (fun i hi=>row Z M H ν F J d funded law i (lower i hi) q O)
  apply priced.congr _ (fun _=>rfl)
  intro r
  apply eq_sub_of_add_eq
  rw [Finset.sum_erase_add _ _ (Finset.mem_univ _),WilsonPositionScaleLawWhole.sumAll]

end YM.Integration.WilsonPositionScaleLawGuardOffGrade
