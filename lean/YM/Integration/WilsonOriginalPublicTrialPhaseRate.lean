import YM.Integration.WilsonOriginalPublicTrialPhaseTiles

/-! A native admissible radius for each replicated fitted source. The
multiplicity depends on the original number of actor names and never on the number of cells. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseRate
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Cells Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons MergeProof.Ribbons.ManyCopies MergeProof.Ribbon MergeProof.Float
open Push Local Marker Motion PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign Extra.Multi OPE.Therm
open WilsonOriginalPublicTrialPhaseFiling WilsonOriginalPublicTrialPhaseTiles
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){K N per:ℕ}{I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per K

def volume (B:ℕ):ℝ:=((B+B+1:ℕ):ℝ)^4
def room (B load:ℕ):ℝ:=Real.log 2/(2*volume B*(1+load)*(1+|siteFactor B|))
def wage (B load:ℕ)(χ:ℝ):ℝ:=room B load/(1+|χ|)

theorem rents (B load:ℕ)(κ:ℝ)(small:volume B*κ≤Real.log 2/2):
    0<room B load ∧ (∀χ:ℝ,0<wage B load χ ∧ wage B load χ*χ≤room B load) ∧
      volume B*(κ+load*siteFactor B*room B load)≤3 ∧
      Real.exp (κ+load*siteFactor B*room B load)-1≤1:=by
  have V:0<volume B:=by unfold volume;positivity
  have one:1≤volume B:=by unfold volume;norm_cast;exact Nat.one_le_pow _ _ (by omega)
  have q:0<Real.log 2:=Real.log_pos (by norm_num)
  have pos:0<room B load:=by unfold room;positivity
  refine ⟨pos,fun χ=>⟨by unfold wage;positivity,?_⟩,?_⟩
  · have bound:χ≤1+|χ|:=by linarith [le_abs_self χ]
    calc
      wage B load χ*χ≤wage B load χ*(1+|χ|):=mul_le_mul_of_nonneg_left bound (by unfold wage;positivity)
      _=room B load:=div_mul_cancel₀ _ (by positivity)
  · have gross:(load:ℝ)*siteFactor B≤(1+load)*(1+|siteFactor B|):=by
      calc
        _≤(load:ℝ)*|siteFactor B|:=mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _≤_:=by nlinarith [abs_nonneg (siteFactor B),Nat.cast_nonneg (α:=ℝ) load]
    have h:volume B*(κ+load*siteFactor B*room B load)≤Real.log 2:=by
      rw [mul_add]
      calc
        _≤Real.log 2/2+volume B*((1+load)*(1+|siteFactor B|)*room B load):=by
          gcongr
        _=Real.log 2:=by unfold room;field_simp;ring
    have upper:κ+load*siteFactor B*room B load≤Real.log 2:=by
      apply (le_div_iff₀' V).2 at h
      exact h.trans ((div_le_iff₀ V).2 (le_mul_of_one_le_right q.le one))
    exact ⟨h.trans (by have:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num);linarith),
      by have:=Real.exp_monotone upper;rw [Real.exp_log (by norm_num)] at this;linarith⟩

theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(live:K≤N)
    (tiles:Tiling ((C).side K per))(d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i))
    (small:∀j,((((C).localSection (d j)).footprint (z j)).card:ℝ)*(H).levels.clock.forcedAllowance K≤1)
    (opening:volume (P).p.B*(H).levels.clock.forcedAllowance K≤Real.log 2/2)(ex:0≤(P).p.supportExponent-3):
    let F:=fun i:tiles.Cell×I=>tiles.copy i.1 (WilsonPositionProgramBlockedTrialAddBack.uncut R
      (d i.2) N per K (z i.2) (v i.2))
    let o:=fun i:tiles.Cell×I=>tiles.copyMap i.1 (z i.2)
    let w:=fun i=>wage (P).p.B (Fintype.card I*Fintype.card Signed) (reserve R (N:=N) (d i) (z i) (v i))
    (∀i,0<w i) ∧
      ∃ f:tiles.Cell×I→ Config G ((C).side K per)→ℂ,∃ k:tiles.Cell×I→ℕ→ Config G ((C).side K per)→ℂ,
      (∀i,Dominated (k i)) ∧ (∀i U,((P).eval U:ℂ)*F i U=coin (P) (f i) (k i) U) ∧
      Serves (P) f (fun i=>profile (P).activities (k i)) (birth (Names tiles.Cell I) (P) F)
        0 (motion tiles) tiles.translateBy (fun i=>Equiv.swap 0 i) o (fun i=>w i.2) ((P).p.supportExponent-3) 1:=by
  intro _ _ w
  let load:=Fintype.card I*Fintype.card Signed
  obtain ⟨t,radius,h,x⟩:=rents (P).p.B load _ opening
  have pos i:0<w i:=(radius _).1
  exact ⟨pos,WilsonOriginalPublicTrialPhaseTiles.original R book live tiles d z v small w pos
    (fun i=>(radius _).2) t.le ex ⟨h,x⟩⟩
end YM.Integration.WilsonOriginalPublicTrialPhaseRate
