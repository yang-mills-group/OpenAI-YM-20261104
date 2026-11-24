import YM.OPE.Compatible.Kiosk.Ter
/-!
# Recurrence currency persistent
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G}{H:Seasons B}{V:ChartRatio G}{p:Clip}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes
abbrev Wcap (H:Seasons B)(P:Patch) (p:Clip)(V:ChartRatio G)(C:ℝ) (m:ℕ)(X:TileC H P p V C→ Script I r) :Prop:= Loan m X downK upperX
lemma fillsL {U V:M×ℕ→Script I r}{x:M→ℝ}(hx:1 ≤ x)(h:Loan m (fun i:M=> U (i,0)) 1 x)(hp:Loan m ((U∘fallsF) - V) downK (x∘Prod.fst))(he:∀ i c,soot m (U i) c→soot m (V i) (1/4*c)) : Loan m U downK (x∘Prod.fst):=by
   obtain ⟨c,hc,u,h⟩:=h; obtain ⟨d,hd,n,H⟩:=hp; let y:=c+4*d; let N:=max n u; have hz:0≤y:=by unfold y; positivity
   refine ⟨y,hz,N,?_⟩; rintro ⟨i,j⟩; induction j with
   | zero=>
      have hx := show 1 ≤ x i from hx i; apply (h i).tips; change c*x i^u*1≤ y*x i^N*downK (i,0)
      simp only [downK,pow_zero,mul_one]; gcongr; · unfold y; linarith -- choose linarith
      simp [N]
   | succ j ih=>
      have hx := show 1 ≤ x i from hx i; let p:=downK (i,j); have ht:= he _ _ ih; have ha:0 ≤ p:= by unfold p downK; positivity
      have hh:= Sack.splits (H (i,j)) ht (fun i=>zero_le_one.trans (payer m _)); have hu : U (i,j+1)=((U∘fallsF)-V) (i,j)+V (i,j):=(sub_add_cancel ..).symm; change soot m (U (i,j+1)) _; rw [hu]; apply hh.tips; change d*x i^n*p+(1/4)*(y*x i^N*p)≤ y*x i^N*downK (i,j+1); rw [show downK (i,j+1)=p*(1/2:ℝ) from pow_succ ..]; have hh:x i^n ≤ x i^N:= pow_le_pow_right₀ hx (le_max_left ..); have he : d*x i^n*p≤d*x i^N*p:= by gcongr
      have hg:0≤ x i^N := by positivity
      unfold y; linarith only [he,mul_nonneg (mul_nonneg hc hg) ha]
variable (H P p V C)
lemma onWheels (U W: TileC H P p V C→ Script I r)(m:ℕ)(hx: Loan m U 1 upperX)(h:Wcap H P p V C m ((U ∘ fallsF)-W))(hf:∀ i c, soot m (U i) c→ soot m (W i) (1/4*c)): Wcap H P p V C m U :=by
   let k(z:Crew H P p V C):= max z.1.cost z.2.cost; have hm: Loan m U downK (k ∘ Prod.fst):= by
       refine fillsL (x:=k) (fun i=> i.1.fits.trans (le_max_left ..)) ?_ h hf; obtain ⟨c,hc,n,H⟩:=hx; exact ⟨_,hc,n,fun i=> H (i,0)⟩
   exact hm
lemma max_cap : (1:TileC H P p V C→ℝ) ≤ upperX:= fun i=> i.1.1.fits.trans (le_max_left ..)
lemma LeafLoan : Loan m (fun i : TileC H P p V C=> (UA i).liftZ r) 1 upperX ∧ Loan m (fun i:TileC H P p V C=> (VA i).liftZ r) 1 upperX:=by exact ⟨leaf_loan _ (fun i=>zero_le_one.trans i.1.1.fits) (fun i=>le_max_left ..),leaf_loan _ (fun i=>zero_le_one.trans i.1.2.fits) (fun i=>le_max_right ..)⟩
end Alps
end YM.OPE.Votive
