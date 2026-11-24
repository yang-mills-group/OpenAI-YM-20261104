import YM.FormalBulk08.Bank.Incense

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open AnalyticNext.QuarticMatch.Radius.Model
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n f : Side} (S : StepData n f) {P : Patch} {K : KernelChoices}

lemma chop (W : S.Choices) (h : S.patch.Branches S.kernel G) : paste (clack S (G:=G) W) = ∑ i:Edge (Site n),PowerSeries.map (MvPolynomial.rename (drill S G i.1 i.2)).toRingHom (paste (azure S.patch S.kernel i.2)) := by
   let u (i:Edge (Site n)) := fun z:Jets.Rays (Glob G n f)=> azure S.patch S.kernel i.2 (z ∘ drill S G i.1 i.2)
   have he : clack (G:=G) S W=ᶠ[𝓝 0] ∑ i,u i := by
       filter_upwards [eventually_all.mpr (fun i=>azure_predict S i h W)] with z hz; simp only [clack,noiseTaylor,Finset.mul_sum,Finset.sum_apply];exact Finset.sum_congr rfl fun _ _=>hz _
   rw [paste_replace he,garter u _ (fun i _=> ContDiffAt.comp (g:=azure S.patch S.kernel (G:=G) i.2) (f:=fun z=> z ∘ drill S G i.1 i.2) _ ((azure_diff _ S.kernel h _).of_le le_top) (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..))];exact Finset.sum_congr rfl fun i _=> folds_byte _ _ ((azure_diff _ S.kernel h _).of_le le_top)

def sparkle (P : Patch) (K : KernelChoices) (G : Gauge) (i : Axis) := afterX (paste (@azure G P K i)) 2
lemma incense (k : S.Choices) (h : S.patch.Branches S.kernel G):
    joust (staging G S) (noisePin S k)=∑ i: Axis, schedules (sparkle S.patch S.kernel G i) (feet G S.patch i) n := by
   ext1 e; rw [joust,noisePin,coeff_map,after_one,chop S k h]; simp_rw [schedules, map_sum,coeff_map]; change (∑ i : Site n × Axis,_) = _; rw [Fintype.sum_prod_type, Finset.sum_comm]; simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe, MvPolynomial.rename_rename,tess,sparkle,after_one]

-- packets at stage before and after activity restriction
variable {S} (G)
def TO (G : Gauge) (P : Patch) (K : KernelChoices) : OrbitV (Biglot (Board G P)) := fun e r=> ∑ i:Axis,deploy (feet G P i) (rancho (sparkle P K G i) e r)
def WO {G : Gauge} (P : Patch) (T:Lodge P) (ρ:ChartRatio G) : OrbitV (Biglot (BoardL G P T)):= fun e r=>∑ i: Bud P T, deploy (thick T i) (rancho (wageP ρ) e r)
lemma TO_bail (e r : ℕ) (σ : ℝ) (P : Patch) (K : KernelChoices) : ∃ C,Bail (fame _) σ (TO G P K e r) C:=⟨_,bail_many _ _ _ (fun _ _=>obeys _ _ _)⟩
lemma WO_bail (e r : ℕ) (σ : ℝ) (T : Lodge P) (ρ : ChartRatio G): ∃ C,Bail (fame _) σ (WO P T ρ e r) C:=⟨_,bail_many _ _ _ (fun _ _=>obeys _ _ _)⟩
lemma TO_vanish (P : Patch) (K : KernelChoices) (e r : ℕ) (h : 2+e≠r) : TO G P K e r=0 := by
   have he i: rancho (sparkle P K G i) e r=0:= by rw [sparkle,rancho,after_one,marble_eq_zero_iff, MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _),if_neg (Ne.symm h)]
   unfold TO;simp_rw [he,deploy_void, Finset.sum_const_zero]
lemma WO_vanish (ρ : ChartRatio G) (h : LocalRatio ρ) (T : Lodge P) (e r) (he : e≠r ∨ e=0): WO P T ρ e r=0 := by
    unfold WO; have hz : rancho (wageP ρ) e r=0:=by
       unfold rancho; obtain he|he:=he
       · rw [marble_eq_zero_iff, MvPolynomial.homogeneousComponent_of_mem (wage_rank ρ h e),if_neg (Ne.symm he)]
       rw [he,wage_unit ρ h,marble_zero]
    simp_rw [hz,deploy_void,Finset.sum_const_zero]
lemma TO_up (P : Patch)(K : KernelChoices) (e r): Up (TO G P K e r) := up_sums _ _ (fun _ _=>parade _ _)
lemma WO_up (T:Lodge P) (ρ:ChartRatio G) (e r): Up (WO P T ρ e r):= up_sums _ _ (fun _ _=>parade _ _)
lemma TO_tor (S : StepData n f) (k : S.Choices) (h : S.patch.Branches S.kernel G) (e r) (i:Fin r) : cum i n (TO G S.patch S.kernel e r)=rancho (joust (staging G S) (noisePin S k)) e r := by
    unfold TO; rw [incense S k h, rancho,map_sum,←canyon_eq,map_sum,cum_sums _ _ _ _ (C:=fun i=>_) (fun _ _=>obeys _ _ 0) le_rfl]; exact Finset.sum_congr rfl fun j _=> (packet_schedules _ _ _ i e).symm
lemma WO_tor (S : StepData n f) (ρ : ChartRatio G) (T:Lodge S.patch) (h : LocalRatio ρ) (e r) (i:Fin r) : cum i n (WO S.patch T ρ e r)= rancho (joust (saddleP G S T) (halo (sap T.forest ρ) (wire G n))) e r := by
   rw [wage_draw S ρ T h]; unfold WO; rw [cum_sums _ _ _ _ (C:=fun _=>_) (fun _ _=>obeys _ _ 0) le_rfl]; simp only [rancho,←canyon_eq,map_sum]; exact Finset.sum_congr rfl fun j _=> (packet_schedules _ _ _ i e).symm
end YM.FormalBulk08.Bank
