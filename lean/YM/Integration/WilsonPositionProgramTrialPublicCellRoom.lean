import YM.Integration.WilsonPositionProgramTrialPublicReflectedProduct

/-! One price for all continuously translated profiles inside the actual K cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellRoom
open Function Filter Set Lattice WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider
open WilsonIndependentFittedExteriorProfile (home)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}

private theorem separation {D E:ℕ}(T:Rarity D)(V:Rarity E)(σ x δ:ℝ)(sp:0<σ)(xp:0≤x)
    (small:4*x≤σ*δ)(gap:ClearDay T V δ)(c u v:Point4)(pu:‖u‖≤1)(pv:‖v‖≤1):
    ClearDay (home T σ sp (c-x•u)) (home V σ sp (c-x•v)) (σ*δ/2):=by
  intro a ha b hb
  let p:=σ⁻¹ • (-(c-x•u)+a)
  let q:=σ⁻¹ • (-(c-x•v)+b)
  have left:p∈tsupport T.ψ.val:=WilsonIndependentMovingRosterOuterSupport.membership T σ sp (c-x•u) ha
  have right:q∈tsupport V.ψ.val:=WilsonIndependentMovingRosterOuterSupport.membership V σ sp (c-x•v) hb
  have d:=mul_le_mul_of_nonneg_left (gap p left q right) sp.le
  have scaled:dist (σ•p) (σ•q)=σ*dist p q:=by rw [dist_smul₀,Real.norm_of_nonneg sp.le]
  rw [←scaled] at d
  have restored:σ•p-σ•q=(a-b)+x•(u-v):=by
    dsimp only [p,q]
    rw [smul_smul,smul_smul,mul_inv_cancel₀ sp.ne',one_smul,one_smul,smul_sub]
    abel
  rw [dist_eq_norm,restored] at d
  have width:‖x•(u-v)‖≤x*2:=by
    rw [norm_smul,Real.norm_of_nonneg xp]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le u v).trans (by linarith only [pu,pv])) xp
  rw [dist_eq_norm]
  linarith only [d,norm_add_le (a-b) (x•(u-v)),width,small]

def room (y Z x σ:ℝ)(o:CellR):ℝ:=
  max (max 1 (|y|+|y| *‖o.val‖+x+Z*σ)) (2*Z/σ)

theorem original (Q:Fin (n+1)→SealR G)(T:Wilt Q)(y Z x σ:ℝ)(o:CellR)(M:Fin (n+1)→ℝ)
    (paid:Bough Q T y Z M)(xp:0≤x)(sp:0<σ)(fine:4*x≤σ*Z⁻¹)
    (ξ:Fin (n+1)→Point4)(cube:∀i,‖ξ i‖≤1):
    Bough Q (fun i=>placed (T i) x y σ sp o (ξ i)) y (room y Z x σ o)
      (fun i=>σ⁻¹^4*((max 1 σ⁻¹)^(Q i).D*M i)):=by
  let H:=room y Z x σ o
  have zp:0<Z:=zero_lt_one.trans_le paid.pos
  have h₁:1≤H:=(le_max_left 1 _).trans (le_max_left ..)
  have h₂:|y|+|y| *‖o.val‖+x+Z*σ≤H:=(le_max_right 1 _).trans (le_max_left ..)
  have h₃:2*Z/σ≤H:=le_max_right ..
  have plus:0≤|y| *‖o.val‖:=mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have size:0≤Z*σ:=mul_nonneg zp.le sp.le
  refine ⟨h₁,fun i=>WilsonIndependentFittedExteriorProfile.paid _ σ sp _ _ (paid.lanes i),?_,by linarith only [h₂,plus,size,xp],?_⟩
  · intro i
    change max 1 (‖-(y•o.val)-x•ξ i‖+(T i).radius*σ)≤H
    have length:=norm_sub_le (-(y•o.val)) (x•ξ i)
    rw [norm_neg,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_of_nonneg xp] at length
    have step:=mul_le_mul_of_nonneg_left (cube i) xp
    have tube:=mul_le_mul_of_nonneg_right (paid.rents i) sp.le
    exact max_le h₁ (by linarith only [length,abs_nonneg y,step,tube,h₂])
  · intro i j neq a ha b hb
    have gap:=separation (T i) (T j) σ x Z⁻¹ sp xp fine (paid.seats i j neq)
      (-(y•o.val)) (ξ i) (ξ j) (cube i) (cube j)
    apply le_trans _ (gap a ha b hb)
    change H⁻¹≤σ*Z⁻¹/2
    have hp:0<2*Z/σ:=by positivity
    calc H⁻¹≤(2*Z/σ)⁻¹:=(inv_le_inv₀ (zero_lt_one.trans_le h₁) hp).2 h₃
         _=σ*Z⁻¹/2:=by field_simp

end YM.Integration.WilsonPositionProgramTrialPublicCellRoom
end
