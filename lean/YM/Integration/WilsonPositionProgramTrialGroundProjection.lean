import YM.Integration.WilsonMaxwellThermometerGroundInversion

/-! A size bound for the authentic finite curvature covariance, including
each diagonal and reflected contribution on the chosen inversion tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialGroundProjection
open Next.Rank Beamer Finset Lattice PertExtension PertExtension.Orb PertExtension.LatticePT
open PertExtension.LatticePT.Projection
open WilsonMaxwellThermometerGroundInversion
open scoped BigOperators Classical
variable {G:Gauge} {n:Side}

private theorem disk_re (y p:Face (Per n)):
    disk (fun e=>((shining y e).re:ℂ)) p=((disk (shining y) p).re:ℂ):=by
  simp only [disk,Orb.Curl,Complex.add_re,Complex.sub_re,Complex.ofReal_add,Complex.ofReal_sub]

theorem single (y p:Face (Per n)) : |(disk (shining y) p).re|≤1:=by
  let a(x:Face (Per n)):ℝ:=(disk (shining y) x).re
  have forms:=scalar_law (fun e=>((shining y e).re:ℂ)) y
  simp_rw [disk_re y] at forms
  have mass : (∑x:Face (Per n),(a x)^2)=a y := by
    have h:=congrArg Complex.re forms
    simpa only [a,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,pow_two] using h
  have charged(x:Face (Per n)) : (a x)^2≤a y := mass ▸ single_le_sum
    (fun (i:Face (Per n)) _=>sq_nonneg (a i)) (mem_univ x)
  have hy:=charged y
  have hp:=charged p
  change |a p|≤1
  have bounded : a y≤1 := by
    by_contra! larger
    have h:=mul_pos (sub_pos.mpr larger) (lt_trans zero_lt_one larger)
    nlinarith
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  rw [sq_abs,one_pow]
  exact hp.trans bounded

theorem echo_price (u v:Cover)(x y:Address G):|echo n u v x y|≤2:=by
  change |direct G n u v x y+reflected G n u v x y|≤2
  apply (abs_add_le ..).trans
  by_cases colors:x.2.2=y.2.2
  · simp only [direct,reflected,if_pos colors]
    exact (add_le_add (single _ _) (single _ _)).trans_eq (by norm_num)
  · simp [direct,reflected,colors]

theorem original (ev:Even n.val)(sites:Fin 3 → Cover)(a b:Entry G):
    ‖(earned ev sites).cov a b‖≤2:=by
  rw [cross,Complex.norm_real,Real.norm_eq_abs]
  exact echo_price .. 

end YM.Integration.WilsonPositionProgramTrialGroundProjection
end
