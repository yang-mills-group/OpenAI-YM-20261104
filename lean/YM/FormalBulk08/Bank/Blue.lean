import YM.FormalBulk08.Bank.Furl

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {G : Gauge} {n f : Side} (S : StepData n f) {P : Patch} (ρ : ChartRatio G)

def wages (x : Jets.Rays G.ColorIndex) := ρ.J (WithLp.toLp 2 x)
lemma wages_diff (h : LocalRatio ρ) : ContDiffAt ℝ ∞ (wages ρ) 0 := by
   let f : Jets.Rays G.ColorIndex→L[ℝ] G.Color := LinearMap.toContinuousLinearMap { toFun:= fun x=>WithLp.toLp 2 x,map_add':= fun _ _=>rfl,map_smul':=fun _ _=>rfl }
   exact (show ContDiffAt ℝ ∞ ρ.J (f 0) from (by rw [map_zero]; exact (h.germ _ (Metric.mem_ball_self h.patch)).of_le le_top)).comp 0 f.contDiff.contDiffAt
lemma wage_hot (h : LocalRatio ρ) : coeff 0 (paste (wages ρ))=1:=by rw [paste_first,show wages ρ 0=1 from h.anchored,map_one]

def wageP := covelog (paste (wages ρ))
def thick (T:Lodge P) (v : Bud P T) (i : G.ColorIndex) : Biglot (BoardL G P T):=(0,Sum.inl (shrub T v i))
lemma sap_rooted (T : Lodge S.patch) (h : LocalRatio ρ) :
    let F:= T.forest (S:=S)
    covelog (paste (sap F ρ))=∑ i:F.Free,PowerSeries.map (MvPolynomial.rename (fun j=> pines F (i,j))).toRingHom (wageP ρ):= by
   intro F;let A (i : F.Free) := fun x:Jets.Rays (Pine G _ F)=> wages ρ (x ∘ fun j=> pines F (i,j));
   have he : sap F ρ=∏ i,A i:= by funext x; rw [Finset.prod_apply];rfl
   rw [he, shaving A _ (fun j _=>ContDiffAt.comp (g:=wages ρ) (f:=fun x:Jets.Rays (Pine G _ F)=> x ∘ fun i=>pines F (j,i)) 0 (wages_diff ρ h) (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..))];
   have hp i : paste (A i)=PowerSeries.map (MvPolynomial.rename fun j=> pines F (i,j)).toRingHom (paste (wages ρ)):= folds_byte _ _ (wages_diff _ h)
   rw [covelog_savings _ _ (fun j=> by rw [hp j,coeff_map,wage_hot ρ h,map_one])]; simp_rw [hp,← map_covelog _ (wage_hot ρ h)]; rfl

-- rename twice
lemma wage_tray (T : Lodge S.patch) (w : (T.forest (S:=S)).Free) (i : G.ColorIndex) :
    Lotus.tint (botanic S T w).1 (drip n (thick T (botanic S T w).2 i))= saddleP G S T (Sum.inl (pines (T.forest (S:=S)) (w,i))) := by
   unfold saddleP; rw [Equiv.trans_apply,Equiv.sumCongr_apply, Sum.map_inl,shrub_pin]; simp [thick, Lotus.drip, Lotus.tint,bifid]

lemma wage_draw (T : Lodge S.patch) (h : LocalRatio ρ) :
    let F:=T.forest (S:=S)
    joust (saddleP G S T) (halo (sap F ρ) (wire G n)) = ∑ v : Bud S.patch T, schedules (wageP ρ) (thick T v) n := by
   intro F; unfold joust Jets.halo;rw [sap_rooted S ρ T h,map_sum,map_sum]; simp_rw [schedules]; rw [Finset.sum_comm,←Fintype.sum_prod_type']; refine Fintype.sum_equiv (botanic S T) _ _ fun w=>?_
   ext1 e; simp_rw [coeff_map]; simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,MvPolynomial.rename_rename]
   have ht : (Lotus.tint _ ∘ drip n ∘ thick T (botanic S T w).2) = ((saddleP G S T) ∘ Sum.inl ∘ fun j:G.ColorIndex=> pines F (w,j)) := funext (wage_tray S T w)
   rw [ht]
lemma wage_unit (h : LocalRatio ρ) : coeff 0 (wageP ρ)=0:=covelog_rank (wage_hot ρ h)
lemma wage_rank (h : LocalRatio ρ) (n:ℕ) : MvPolynomial.IsHomogeneous (coeff n (wageP ρ)) n := log_grade (wage_hot ρ h) (paste_grade (wages ρ)) n
end YM.FormalBulk08.Bank
