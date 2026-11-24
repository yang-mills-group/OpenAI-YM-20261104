import YM.XSpace.Compat.Growth
import YM.Further.FREE_COVARIANCE_KP.KP.Ride
import YM.Further.FREE_COVARIANCE_KP.KP.Alloy
import YM.Maxwell.PotentialKernel
import YM.Analysis.SmoothJets

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Maxwell
open scoped Topology ContDiff BigOperators InnerProductSpace
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f g : E4→F} {x : E4}

lemma cyclists_at (A : List Axis) (i : Fin A.length) : cyclists A i=basis (A.get i) := by
  induction A with
  | nil => exact i.elim0
  | cons a A ih => cases i using Fin.cases <;> simp [cyclists, ih]

lemma reports (A) (h : ContDiffAt ℝ ∞ f x) : ride A f x=iteratedFDeriv ℝ A.length f x (cyclists A) := by
  induction A generalizing f with
  | nil => simp [ride]
  | cons a A ih =>
    rw [ride,ih (grad_smooth a h (by simp))]
    rw [cyclists]
    symm
    exact Analysis.cons_inner (h.of_le (show (↑(A.length+1):ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)) _ _

lemma ride_smooth A (h : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (ride A f) x := by induction A generalizing f with | nil => exact h | cons a A ih => exact ih (grad_smooth a h (by simp))

lemma ride_germ (A) (h : f =ᶠ[𝓝 x] g) : ride A f =ᶠ[𝓝 x] ride A g := by
  induction A generalizing f g with
  | nil => exact h
  | cons a A ih =>
    refine ih ?_; filter_upwards [EventuallyEq.fderiv (𝕜:=ℝ) h] with i hi; change fderiv ℝ _ _ _ = fderiv ℝ _ _ _; rw [hi]

lemma ride_sub A (h : ContDiffAt ℝ ∞ f x) (he : ContDiffAt ℝ ∞ g x) : ride A (f-g) x=ride A f x-ride A g x := by
  rw [reports _ (f:=f-g) (h.sub he),reports _ h, reports _ he]
  rw [iteratedFDeriv_sub_apply (h.of_le (WithTop.coe_le_coe.mpr le_top)) (he.of_le (WithTop.coe_le_coe.mpr le_top))]
  rfl

lemma ride_join (A B : List Axis) : ride B (ride A f)=ride (A++B) f := by induction A generalizing f with | nil => rfl | cons a A ih => exact ih

lemma ride_nil (A : List Axis) : ride A (0:E4→F)=0 := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [ride,show grad a (0 : E4→F)=0 by ext; simp [grad,Analysis.D],ih]
end

def skim (x : E4) : ℂ := ↑(Green x)

def paste (x : E4) := skim x * breeze (1/4) x

lemma skim_hd {x:E4} (h : x≠0) : ContDiffAt ℝ ∞ skim x := Complex.ofRealCLM.contDiff.contDiffAt.comp _ (freeSmooth h)

lemma paste_hd {x:E4} (h : x≠0) : ContDiffAt ℝ ∞ paste x := (skim_hd h).mul (breeze_smooth _).contDiffAt

lemma skim_strength {ι : Type*} : Weight whole (-2) (fun (_:ι)=>skim) := by
  have hh := (reciprocal_high (ι:=ι)).scale (↑Maxwell.normal)
  apply hh.stay; intro i p _; simp [spine,skim,Green]

lemma past_strength {ι : Type*} (k : ℤ) : Weight (rim 1 zero_lt_one) k (fun (_:ι) => paste) := by
  have h := ((skim_strength (ι:=ι)).use (show (rim 1 zero_lt_one).look⊆whole.look from fun p hp=> (rim 1 zero_lt_one).out hp)).times (far_fee (k+2) (le_refl 1) zero_lt_one (by norm_num : (0:ℝ)<1/4))
  rw [show (-2:ℤ)+(k+2)=k by ring] at h
  exact h

lemma rides_skim (f : E4→ℝ) (A : List Axis) {x:E4} (h : ContDiffAt ℝ ∞ f x) : ride A (fun p=> (↑(f p):ℂ)) x=(↑(ride A f x):ℂ) := by
  let L := Complex.ofRealCLM
  change ride A (L ∘ f) x = _
  rw [reports _ (L.contDiff.contDiffAt.comp x h),reports _ h,L.iteratedFDeriv_comp_left h (WithTop.coe_le_coe.mpr le_top)]
  rfl

lemma riding_funds (A) (k : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ x:E4,1 ≤ ‖x‖ → ‖ride A paste x‖≤ C*(‖x‖^k)⁻¹ := by
  obtain ⟨C,hC,H⟩ := (past_strength (ι:=Unit) ((-k:ℤ) + A.length)).quotes A.length
  let S := sphere (0:E4) 1
  have hS : ContinuousOn (fun x=> ‖ride A paste x‖) S := by
    intro x hx; exact ((ride_smooth _ (paste_hd (by intro he; rw [he] at hx; simp [S] at hx))).continuousAt.norm.continuousWithinAt)
  obtain ⟨B,hB⟩ := (isCompact_sphere (0:E4) 1).bddAbove_image hS
  refine ⟨max C B,hC.trans (le_max_left ..),fun x hx => ?_⟩; have hx' : 0<‖x‖ := zero_lt_one.trans_le hx
  rcases lt_or_eq_of_le hx with he|he
  · specialize H () x he
    simp only [add_sub_cancel_right,zpow_neg,zpow_natCast] at H
    rw [reports _ (paste_hd (norm_pos_iff.mp hx'))]
    apply le_trans (ContinuousMultilinearMap.le_opNorm ..)
    simp_rw [cyclists_at, basis_norm,Finset.prod_const_one,mul_one]
    apply H.trans
    gcongr
    exact le_max_left ..
  rw [← he]; simp only [one_pow,inv_one,mul_one]; apply (hB (mem_image_of_mem _ (show x∈S from ?_))).trans (le_max_right ..); simpa [S] using he.symm

lemma skin_story (A : List Axis) :
    Profit (fun p=> bill turned A p * water p) ∧ retract (fun p=>bill turned A p * water p)=ride A (retract water) := by
  have hh (f:E4→ℂ) (hf:Profit f) (A : List Axis) : Profit (fun p=> bill turned A p * f p) ∧ retract (fun p=>bill turned A p*f p)=ride A (retract f) := by
    induction A generalizing f with
    | nil => simpa only [bill,List.map_nil,List.prod_nil,one_mul,ride] using And.intro hf (rfl: f=f)
    | cons a A ih =>
      have he := ih _ (hf.bill_one a); rw [ride,hf.timed a]
      rw [show (fun p:E4=> bill turned (a::A) p*f p)=(fun p:E4=>bill turned A p*(turned p a*f p)) from funext fun p => by simp only [bill,List.map_cons,List.prod_cons]; ring]
      exact he
  exact hh _ water_rich _

lemma retract_skin (A : List Axis) {x:E4} (hx : x≠0) : retract (fun p=>bill turned A p*water p) x=↑(ride A Green x)-ride A paste x := by
  rw [(skin_story A).2]
  have he : retract water =ᶠ[𝓝 x] skim-paste := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show x∈({0}ᶜ:Set E4) from hx)] with p hp
    rw [water_price hp]
    simp only [skim,paste,Pi.sub_apply,breeze]
    push_cast
    ring
  rw [(ride_germ _ he).eq_of_nhds, ride_sub _ (skim_hd hx) (paste_hd hx)]; exact congr_arg (· - ride A paste x) (rides_skim _ _ (freeSmooth hx))

end YM.XSpace.Compat.KP
end
