import YM.Integration.WilsonMeasuredOriginalColumnTransition
import YM.Extra.SOURCE_HISTORIES.Beside

/-! Rejoin the compensated physical push and the separately funded lower group-field change on its original gauge carrier. -/
noncomputable section
namespace YM.Integration.WilsonMeasuredOriginalColumnSigned
open Labels Lattice Wilson RG Source Extra.Histories Extra.Histories.Relay Trace.Physical
open PhysicalNext Repeat Legato Graces Roost Org WilsonTrueProjectedDualHistory
open scoped Classical

variable {G:Gauge} (R:Run G) {d N per i:ℕ} (Ψ:∀ j,Rep G (R.family.side j per))
local notation "lev" => R.family.labels.level d
local notation "hi" => R.family.side (i+1) per
local notation "lo" => R.family.side i per
local notation "sec" => R.family.localSection d

theorem original (live:i≤N)
    (fineEq:(Ψ (i+1)).eval=(R.family.path.rep N per (i+1)).eval)
    (coarseEq:(Ψ i).eval=(R.family.path.rep N per i).eval)
    {σ C Λ δ w:ℝ} (law:(Ψ i).Lawful σ C Λ δ w)
    (F:Spaces R per) (upper:Config G hi→ℂ) (emitted prescribed:Config G lo→ℂ)
    (fine:F (i+1)=WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) upper)
    (coarse:∀ U,F i U=((Ψ i).eval U:ℂ)*prescribed U)
    (x z:Coefficient lev lo) {u v:ℝ}
    (actual:WilsonTrueProjectedDualHistory.Admitted R (d:=d) Ψ i x u) (read:(lev).coeffSize x.x≤u)
    (earned:WilsonTrueProjectedDualHistory.Admitted R (d:=d) Ψ i z v) (compare:(lev).coeffSize z.x≤v)
    (pushed:∀ U,(((Ψ i).eval U:ℂ))⁻¹*x.density 0 sec (Ψ i) U=
      actualAverage R.family (N:=N) upper U-emitted U)
    (rows:∀ U,z.density 0 sec (Ψ i) U=((Ψ i).eval U:ℂ)*(emitted U-prescribed U)) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i (u+v) :=by
  refine ⟨beside x z,presentation actual.1 actual.2 earned.1 earned.2,?_,?_⟩
  · rw [reckon]
    exact (Size.add lev x.x z.x).trans (add_le_add read compare)
  · rw [fine,WilsonMeasuredOriginalColumnTransition.original R live (Ψ (i+1)) (Ψ i) fineEq coarseEq]
    funext U
    rw [Pi.add_apply,coarse U,plus law actual.2 earned.2 sec,Pi.add_apply,rows U]
    have nz:(((Ψ i).eval U:ℝ):ℂ)≠0:=by
      rw [coarseEq];exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    let cash:ℂ:=(Ψ i).eval U
    have cost:=pushed U
    change cash⁻¹*x.density 0 sec (Ψ i) U=_ at cost
    have pos:cash≠0:=nz
    have invoice:=congrArg (fun z:ℂ=> cash*z) cost
    simp only [←mul_assoc,mul_inv_cancel₀ pos,one_mul] at invoice
    rw [invoice]
    dsimp [cash]
    ring

end YM.Integration.WilsonMeasuredOriginalColumnSigned
end
