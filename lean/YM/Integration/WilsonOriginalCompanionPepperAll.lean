import YM.Integration.WilsonThermometerCorridorTwoShifts

/-! Extract every proper face on one true gathered Wilson shelf at its own restored toll. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionPepperAll
open Finset Function Filter MeasureTheory Lattice Wilson RG Ac Marker Push GridApprox.Nil
open MergeProof MergeProof.Accent MergeProof.Ribbons Extra.Histories Extra.Trajectories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerPepperFace WilsonThermometerPepperTwice
open scoped BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]
local notation "J" => Stock.census I
def remaining (T:Finset I):(J).Mode:=⟨univ\T,mem_univ _⟩

private theorem gain (d:I→ℂ)(a:I)(c:ℂ)(s:(J).Mode)(inside:a∈s.val)(F:Poly (J)):
    (Poly.pass (Mach (J) (fun i=>d i+scalar a c i))*F).part s=
      (Poly.pass (Mach (J) d)*F).part s+c*(Poly.pass (Mach (J) d)*F).part (stripped s a):=by
  have shift:Mach (J) (fun i=>d i+scalar a c i)=Mach (J) (scalar a c)+Mach (J) d:=by
    unfold Mach
    simp only [send_add,sum_add_distrib,add_comm]
  rw [shift,pass_add (mute (J) _) (mute (J) _),mul_assoc,at_mask _ _ _ inside]

private def tested (d:I→ℂ)(s:(J).Mode):Poly (J) →L[ℂ] ℂ:=
  (Poly.get s).comp (LinearMap.toContinuousLinearMap ({
    toFun:=fun q=>Poly.pass (Mach (J) d)*q
    map_add':=by intros;rw [mul_add]
    map_smul':=by intros;rw [mul_smul_comm];rfl
  }:Poly (J) →ₗ[ℂ] Poly (J)))

variable {G:Gauge}(R:Run G){N p j u:ℕ}(uj:u≤j)
def pay (f:Config G (R.family.side (j+1) p)→ℂ):ℂ:=
  WilsonThermometerUnitFilingCoarse.reading R (N:=N) (p:=p)
    ((R.family.path.levels.clock.op j p).push (R.family.path.rep N p (j+1)).beta f) u uj

theorem original (w:I→ℝ)(positive:∀i,0<w i)(B:ℝ)
    (X:Config G (R.family.side (j+1) p)→Poly (J))(actual:Integrable X (prior G _))
    (full:∀d:I→ℂ,(∀i,w i*‖d i‖≤1/2) →
      ‖pay R (N:=N) uj (fun U=>(Poly.pass (Mach (J) d)*X U).part (whole I))‖≤B):
    ∀s:(J).Mode,‖pay R (N:=N) uj (fun U=>(X U).part s)‖≤(∏i∈univ\s.val,4*w i)*B:=by
  have lift (s:(J).Mode)(d:I→ℂ):Integrable
      (fun U=>(Poly.pass (Mach (J) d)*X U).part s) (prior G _):=
    (tested d s).integrable_comp actual
  have step (T:Finset I):∀d:I→ℂ,(∀i,w i*‖d i‖≤1/2) → (∀i∈T,d i=0) →
      ‖pay R (N:=N) uj (fun U=>(Poly.pass (Mach (J) d)*X U).part (remaining T))‖≤
        (∏i∈T,4*w i)*B:=by
    induction T using Finset.induction with
    | empty =>
      intro d ok _
      simpa [remaining,whole] using full d ok
    | @insert a T apart prior =>
      intro d ok blank
      let c:ℂ:=((2*w a)⁻¹:ℝ)
      let d':I→ℂ:=fun i=>d i+scalar a c i
      have empty_at:d a=0:=blank a (mem_insert_self ..)
      have affordable' (i):w i*‖d' i‖≤1/2:=by
        by_cases hi:i=a
        · subst i
          simpa only [d',empty_at,zero_add,c] using affordable w positive a a
        · simpa [d',scalar,hi] using ok i
      have stay (i)(hi:i∈T):d' i=0:=by
        have h:i≠a:=fun t=>apart (t ▸ hi)
        simp [d',scalar,h,blank i (mem_insert_of_mem hi)]
      have before:=prior d ok (fun i h=>blank i (mem_insert_of_mem h))
      have after:=prior d' affordable' stay
      have fits:a∈(remaining T).val:=mem_sdiff.mpr ⟨mem_univ _,apart⟩
      have removed:stripped (remaining T) a=remaining (insert a T):=by
        apply Subtype.ext
        ext i
        simp [stripped,remaining]
      have same (U): (Poly.pass (Mach (J) d')*X U).part (remaining T)=
          (Poly.pass (Mach (J) d)*X U).part (remaining T)+c*(Poly.pass (Mach (J) d)*X U).part
             (remaining (insert a T)):=by
        rw [←removed];exact gain d a c _ fits _
      simp_rw [same] at after
      have paid:=WilsonThermometerPepperDifference.pair R (N:=N) uj (w a) ((∏i∈T,4*w i)*B)
        (positive a) _ _ (lift (remaining T) d) (lift (remaining (insert a T)) d) before after
      simpa only [pay,prod_insert apart,mul_assoc] using paid
  intro s
  have h:=step (univ\s.val) (fun _=>0) (by simp) (by simp)
  have right:remaining (univ\s.val)=s:=by apply Subtype.ext;ext i;simp [remaining]
  have zero:Mach (J) (fun _=>0)=0:=by simp [Mach]
  simpa only [right,zero,Extra.Trajectories.pass_zero,one_mul] using h

end YM.Integration.WilsonOriginalCompanionPepperAll
end
