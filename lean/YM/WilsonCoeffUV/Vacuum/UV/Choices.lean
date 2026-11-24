import YM.WilsonCoeffUV.Vacuum.UV.Budget
import YM.Next.FOUNDATIONS.Primary
/-!
Not empty, no vacuous Fk/A schedule hypotheses. But ONLY for this purchase,
physics prices and additional actual Ortho, RG witness etc *never inferred*.
Add the floor, entrance enlargement stamps to the constructor. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Ticket
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries Supply Next.Foundations
open scoped ContDiff Topology BigOperators
variable {G:Gauge}
lemma cap_st : Nonempty Stage := by
   let clip : Clip:= ⟨32,1,1,by norm_num,zero_lt_one,by norm_num,zero_lt_one⟩
   exact ⟨clip,6,2,1,12,1,1,1,le_rfl,le_rfl,zero_lt_one,by norm_num,zero_lt_one,by simp [clip],le_rfl,zero_le_one⟩

theorem choices (g:G.Simple)(u:ℝ)(h:0<u)(X:ℕ→ℕ)(b:ℕ→ℕ): ∃ p:Sheet G,p.kernel.penalty=u ∧ p.floorL≥floors G p.kernel X ∧ p.floorL≥ b ∧ Nonempty (Rolls p) ∧ p.first=5:= by
    obtain ⟨T⟩:= cap_st
    let K:= kernel G u h
    let a:= floors G K X
    let p:Sheet G:= ⟨K,branches G u h,fun _=>T,5,by omega,monotone_const,monotone_const,monotone_const,b ⊔ a⟩
    have hp: p.kernel.penalty=u:= (Axial.viable G u h).choose_spec.1
    exact ⟨p,hp,le_sup_right,le_sup_left,Rolls.exists_rolls p g,rfl⟩

theorem inception (g:G.Simple)(u:ℝ)(h:0<u): ∃ p:Sheet G, p.kernel.penalty=u ∧ Nonempty (Rolls p) ∧ ∀ W:Rolls p,∃ T:Protection W,∃ Y:Delays T,∃ o: Bar Y,Nonempty (Wait o) ∧ ∀ B:Wait o, (∃A:Levels G,Paid B A) ∧ ∀ A:Levels G,Paid B A→∀ i,∀ᶠ ℓ in atTop,∃ R: Realm G i Credit.leanC, R.draws=A ∧ R.paid=chart G ∧ R.y=zz A ∧ R.anchor=ℓ:=by
   obtain ⟨p,hp,ha,_,hL,_⟩:= choices g u h id 0
   refine ⟨p,hp,hL,fun W=>?_⟩; obtain ⟨T,hT⟩:= Protection.exists_margin W (fun _=>1) (fun _=>one_pos)
   let Y:Delays T := ⟨voucher W id (chart G),0,0,0⟩
   obtain ⟨o,ho⟩:= Bar.exists_above Y 1
   exact ⟨T,Y,o,⟨0,fun _ _=>0,fun _=>by simp,0⟩,fun B=> ⟨Wait.ready B g,fun A h=> feasible_awards g (chart_ok G) ha h (show _≤ Y.betaEntry from le_rfl) tendsto_id⟩⟩
end YM.WilsonCoeffUV.Bank.Ticket
