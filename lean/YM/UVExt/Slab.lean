import YM.UVExt.GaugeField

/-! One fixed side pair, all leading comparisons in true incidence and rooted slice notation. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Bid Exterior Laurent Filter Set Matrix Bloch Tree Tensor
open Work.F03 Work.F04
open scoped Topology ContDiff Classical
set_option linter.unusedSectionVars false
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

def polish (K : Matrix (Body 1 f) (Body 1 c) ℝ) (v : Dir G c) : Dir G f := fun x=>WithLp.toLp 2 (fun i=>(K *ᵥ parts G 1 v i) x)
lemma polish_eval (K : Matrix (Body 1 f) (Body 1 c) ℝ) (v : Dir G c) : polish K v = fun x=> ∑ j,K x j • v j := by
  funext i; apply (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).injective; rw [map_sum]; simp_rw [map_smul]; exact funext fun z=> by rw [Finset.sum_apply]; rfl
lemma polish_tends (v : Dir G c) {K K'} (ht : Tendsto (K : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ) atTop (𝓝 K')) :
    Tendsto (fun i=>polish (K i) v) atTop (𝓝 (polish K' v)) := by
   simp_rw [polish_eval]; exact tendsto_pi_nhds.mpr fun z => tendsto_finsetSum _ fun i _ => (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht z) i).smul_const (v i)

lemma relativeGauge (K : Matrix (Body 1 f) (Body 1 c) ℝ) (v : Dir G c) : ∃ z, stretch F (v,relative F K v) = polish K v + tilt z := by
  refine ⟨fun z=> -(WithLp.toLp 2 (fun i:G.ColorIndex => (straighten S F K *ᵥ parts G 1 v i) (z,vac))),?_⟩
  funext i; apply (Equiv.injective (WithLp.equiv 2 _)); funext k
  have ht := congr_fun (parts_stretch F K v k) i
  unfold extracted at ht; rw [add_mulVec, ← mulVec_mulVec, Pi.add_apply, show i=(i.1,coord (axisEquiv.symm i.2)) from Prod.ext rfl (axisEquiv.apply_symm_apply _).symm] at ht
  simp_rw [d_sites] at ht
  change parts G 1 (stretch F (v,relative F K v)) k i = (polish K v i + ((-(WithLp.toLp 2 fun z:G.ColorIndex=> (straighten S F K *ᵥ parts G 1 v z) (i.1,vac))) - (-(WithLp.toLp 2 fun z:G.ColorIndex=> (straighten S F K *ᵥ parts G 1 v z) (i.1+step (axisEquiv.symm i.2),vac))))) k
  rw [polish, PiLp.add_apply, PiLp.sub_apply,PiLp.neg_apply,PiLp.neg_apply]; simp only [←coord_map,axisEquiv.apply_symm_apply,Prod.mk.eta] at ht
  exact ht.trans (by simp only [WithLp.toLp_ofLp]; rw [sub_neg_eq_add,sub_eq_neg_add])

variable {U R : ℕ→PathData G} {p r : Clip} {t : S.Choices} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} {η : ℝ}

structure Slab (U R : ℕ→PathData G) (p r : Clip) (t : S.Choices) (ρ : ℕ→fieldDir G c 1 → AxisChart G F)
    (η : ℝ) (Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ) : Prop where
   critical : ∀ᶠ i in atTop, Critical F p (U i) (ρ i)
   curvature : ∀ᶠ i in atTop, PriceGap F p (U i) η
   classic : ∀ᶠ i in atTop, ClassicalMatch F p r (U i) (R i) (ρ i)
   tangent : ∀ᶠ i in atTop, Guessed F (Y i) (ρ i)

namespace Slab
variable {F} {U' R' η' ρ' Y'} (L : Slab F U R p r t ρ η Y)

def inFT (_L : Slab F U R p r t ρ η Y) : ℕ→ChartVars F G→ℝ := fun i=> uncurry (tested (S:=S) F t p (U i))
def inFine (_L : Slab F U R p r t ρ η Y) : ℕ→Dir G f→ℝ := fun i=> knotted f p (U i)
def inBase (_L : Slab F U R p r t ρ η Y) : ℕ→Dir G c→ℝ := fun i=> knotted c r (R i)
def axis (_L : Slab F U R p r t ρ η Y) : ChartVars F G→Dir G f := Work.F03.axisLog F (G:=G)
def tail (_L : Slab F U R p r t ρ η Y) : ChartVars F G → ℝ := fun i=> noiseTaylor S (represent i.1) (lifting F (represent i.1) i.2) t -- arity check
lemma restored (i) : (inFT L i) =ᶠ[𝓝 0] (fun x=> inFine L i (axis L x) + tail L x) := (inclusion_works F).mono fun x hx=> Eq.trans rfl (congr_arg (fun V=> mainTerm p (U i) V + tail L x) hx.symm)

protected lemma first_flow : lucid (inFT L) := L.critical.mono fun i hx => ((hx.2.2 t).1).of_le le_top
lemma tail_flow (h : lucid (inFine L)) : ContDiffAt ℝ ∞ (tail L) 0 := by
  obtain ⟨y,hy,hg⟩ := (h.and L.first_flow).exists
  have ha := (show Work.F03.inclusion F (G:=G) 0=0 from inclusion_zero F); have hp : axis L 0=0 := congr_arg Prod.snd ha
  have ht : ContDiffAt ℝ ω (axis L) 0 := contDiffAt_snd.comp (f:=Work.F03.inclusion F) 0 (inclusion_smooth F)
  have hd : ContDiffAt ℝ ∞ (inFine L y ∘ axis L) 0 := ContDiffAt.comp (f:=axis L) 0 (hp ▸ hy) (ht.of_le le_top)
  exact (hg.sub hd).congr_of_eventuallyEq ((restored L y).mono fun j hx=>by change tail _ _= _-_ ; rw [hx]; exact (add_sub_cancel_left _ _).symm)

protected lemma track {L' : Slab F U' R' p r t ρ' η' Y'} {k : ℕ} (h : Junction (inFine L) (inFine L') k) (hL : lucid (inFine L)) (hL' : lucid (inFine L')) : Junction (inFT L) (inFT L') k := by
   let a := axis L
   have h0 : Pinned (fun v:ℕ=>a) := Eventually.of_forall fun _=> congr_arg Prod.snd (inclusion_zero _)
   have ha : lucid (fun v:ℕ=> a) := Eventually.of_forall fun _=> ((show ContDiffAt ℝ ω ((ContinuousLinearMap.snd ℝ (Dir G c) (Dir G f)) ∘ Work.F03.inclusion (G:=G) F) 0 from ((ContinuousLinearMap.snd ℝ (Dir G c) (Dir G f)).contDiff.contDiffAt.comp 0 (inclusion_smooth _))).of_le le_top)
   have hi := Junction.compose h (p:=fun _=>_) junction_self hL hL' ha ha h0 h0
   exact Junction.plus hi (junction_self (f:=tail L) (k:=k)) (lucid_comp hL ha h0) (lucid_comp hL' ha h0) (Eventually.of_forall fun _=>tail_flow L hL) (Eventually.of_forall fun _=>tail_flow L hL) |>.congruent (Eventually.of_forall fun i=> (L.restored i).symm) (Eventually.of_forall fun i=> (L'.restored i).symm) -- parenthesis
lemma vertical_gap (hη : 0<η) : clampedGap (inFT L) η := (L.curvature.and L.first_flow).mono fun i ⟨hi,hj⟩ z=> by
  let A := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G F)
  have ht : (∑ i:F.Free, ‖z i‖^2) ≥ 0 := by positivity -- wrong Forest name and syntax
  have hB : ‖z‖ ≤ Real.sqrt (∑ i:F.Free,‖z i‖^2) := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i=> (Real.le_sqrt (norm_nonneg _) ht).mpr (Finset.single_le_sum (s:=Finset.univ) (fun j _=>sq_nonneg ‖z j‖) (Finset.mem_univ i))
  have hc := (mul_le_mul_of_nonneg_left (show ‖z‖^2≤ _ from (pow_le_pow_left₀ (norm_nonneg _) hB 2).trans_eq (Real.sq_sqrt ht)) hη.le).trans (hi t z)
  rw [show tested (S:=S) F t p (U i) (0 : Dir G c)=inFT L i ∘ A from rfl, Next.Foundations.jets_linear A (hj.of_le (finite_cap 2))] at hc
  change η*‖z‖^2 ≤ iteratedFDeriv ℝ 2 _ 0 ![(0,z),(0,z)]; refine hc.trans_eq ?_
  exact show (iteratedFDeriv ℝ 2 (L.inFT i) 0) (fun x=>A (![z,z] x)) = _ from congr_arg (iteratedFDeriv ℝ 2 (L.inFT i) 0) (show (fun x=>A (![z,z] x)) = (![ (0,z),(0,z)] : Fin 2→ChartVars F G) from funext (fun x=>by fin_cases x <;> rfl))
end Slab
end YM.UVExt.Paths
