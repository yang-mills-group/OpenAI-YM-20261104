import YM.MSbar.Pole.Dimension.Advance
import YM.MSbar.Pole.Analysis.Scope

/-! # Definitional rule for one dimensional integral, entire parameter departure -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "ω" => volume.restrict (Ioi (0:ℝ))
private lemma roof (w : ℂ) : ∃ k : ℕ, 2 ≤ (w+2*k).re := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2 - w.re)
  refine ⟨k,?_⟩; simp; linarith

def shed (w : ℂ) := Nat.find (roof w)
def Jstep (k : ℕ) (f : ℝ×E→ℂ) (x : E) (w : ℂ) :=
  j (fun r => higher^[k] f (r,x)) (w+2*k)
/-- Implements DR in extra space dimensions perpendicular to an honest ambient plane. -/
def dimensional (f : ℝ×E→ℂ) (x : E) (w : ℂ) : ℂ := Jstep (shed w) f x w

variable {U : Set E} {p q : Price E} {f : ℝ×E→ℂ}
    (o : IsOpen U) (c : ContinuousOn p.val U)
    (h : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) f)
    (he : EvenOn U f)
include o c h he
lemma all_higher (k : ℕ) : EvenOn U (higher^[k] f) ∧ Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) (higher^[k] f) := by
  induction k with
  | zero => exact ⟨he,h⟩
  | succ k ih => rw [iterate_succ_apply']; exact ⟨higher_even ih.2 ih.1,smooth o c ih.2 ih.1⟩
lemma all_cr (k : ℕ) {v w : E} (hh : ∀ x∈univ ×ˢ U,CR ((0:ℝ),v) (0,w) f x) :
    ∀ x∈univ ×ˢ U,CR ((0:ℝ),v) (0,w) (higher^[k] f) x := by
  induction k with
  | zero => exact hh
  | succ k ih => rw [iterate_succ_apply']; exact keeps_cr o c (all_higher o c h he k).2 ih
lemma reached {x : E} (hx : x∈U) (w : ℂ) (k : ℕ) (hw : 2 ≤ (w+2*k).re) : dimensional f x w = Jstep k f x w := by
  have hk : shed w ≤ k := Nat.find_min' (roof w) hw
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hs : 2 ≤ (w+2*k).re := by
      refine le_trans (show 2 ≤ (w+2*(shed w:ℕ)).re from Nat.find_spec (roof w)) ?_; simp; gcongr
    rw [ih hs]; unfold Jstep; rw [iterate_succ_apply', show w+2*((k+1:ℕ):ℂ)=w+2*k+2 by push_cast; ring]
    symm; exact shift_j o c (all_higher o c h he k).2 hx (all_higher o c h he k).1 hs
lemma in_domain {x : E} (hx : x∈U) {w : ℂ} (hw : 2 ≤ w.re) : dimensional f x w = j (fun r => f (r,x)) w := by
  rw [reached o c h he hx w 0 (by simpa)]; simp [Jstep]
lemma ordinary {x : E} (hx : x∈U) : dimensional f x 0=f (0,x) := by
  rw [reached o c h he hx 0 1 (by simp)]; simpa only [Jstep,iterate_one,Nat.cast_one,mul_one,zero_add] using extractAtZero o c h hx he

def patch (f : ℝ×E→ℂ) (L : E→L[ℝ] ℂ) (w : ℂ) (x : E) := dimensional f x (w+ L x)

def Half (a : ℂ) := 2 * (Complex.Gamma (a/2))⁻¹
omit o c h he [FiniteDimensional ℝ E] in
lemma half_diff : Differentiable ℂ Half := by
  unfold Half; exact (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const _)).const_mul _

lemma finish (L : E→L[ℝ] ℂ) (w : ℂ) (R:ℝ) (hr : ∀ x∈U,‖w+L x‖ ≤ R) :
    Packet U p q (patch f L w) ∧ ∀ v v' : E, (L v'=Complex.I*L v) →
      (∀ x∈univ ×ˢ U,CR ((0:ℝ),v) (0,v') f x) → ∀ x∈U, CR v v' (patch f L w) x := by
  obtain ⟨k,hk⟩:= exists_nat_gt (R+2)
  let g:=higher^[k] f; have hg := (all_higher o c h he k).2
  let W := w+2*k; let P (x) := W+ L x; have hP (x) : P x= w+L x+2*k := by unfold P W; abel
  have he' : 0 ≤ (k:ℝ):= Nat.cast_nonneg _
  let D:=R+2*(k:ℝ)
  obtain ⟨M,hM⟩:= exists_nat_gt D
  have hb x (hx : x∈U) : ‖P x‖ ≤ D := by rw [hP]; apply le_trans (norm_add_le ..); simpa [D] using hr x hx
  have hh x (hx : x∈U) : 2 ≤ (P x).re := by
    have h := (Complex.abs_re_le_norm (w+L x)).trans (hr x hx); rw [hP]; simp
    rw [Complex.add_re] at h; linarith [(abs_le.mp h).1]
  have hr' : Barrel ω U p q (jKernel g L W) := jBarrel o c L W (hg.mono (Set.prod_mono (subset_univ _) fun _ h=>h)) M fun x hx => by
    change (P x-1).re ∈ _; simp; constructor
    · linarith [hh x hx]
    linarith [(le_trans (Complex.re_le_norm _) (hb _ hx))]
  let K (x:E) := ∫ u, jKernel g L W u x ∂ω
  let H (x:E) := Half (P x)
  have ha x (hx : x∈U) : patch f L w =ᶠ[𝓝 x] K * H := by
    filter_upwards [o.mem_nhds hx] with i hi
    have ht := hh i hi; simp only [hP] at ht
    unfold patch; rw [reached o c h he hi (w+L i) k ht,Pi.mul_apply,mul_comm]
    unfold H Half K jKernel Jstep j; rw [← hP,div_eq_mul_inv]
  have hK : Packet U p q K := hr'.integrates
  have hH : Packet U p 1 H := holWeights half_diff hb
  refine ⟨(hK.mul hH).congr ha,fun v v' hv hu x hx => ?_⟩
  have hc' : CR v v' K x := by
    apply integral_cr hr' hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hy: 0<u)
    let Z : E→L[ℝ] ℝ × E:= ContinuousLinearMap.inr ..
    have hl : HasFDerivAt (fun x:E=>(u,x)) Z x:=(hasFDerivAt_const _ _).prodMk (hasFDerivAt_id ..)
    have hD : DifferentiableAt ℝ g (u,x) := (hg.smooth (u,x) ⟨mem_univ _,hx⟩).differentiableAt (by simp)
    let e : E→ℂ := fun y=>(W-1)+L y
    have hu' : DifferentiableAt ℂ (fun z => (u:ℂ)^z) (e x) := by
      simp_rw [Complex.cpow_def_of_ne_zero (x:=(u:ℂ)) (by exact_mod_cast hy.ne')]; fun_prop
    have hA : DifferentiableAt ℝ e x := ((L.differentiableAt).const_add _)
    have hL := CR.pull g hl hD (all_cr o c h he k hu (u,x) ⟨mem_univ _,hx⟩)
    refine (CR.mul (show CR v v' (fun x => g (u,x)) x from hL) ((CR.affine hv (W-1)).comp hA hu') (hD.comp _ hl.differentiableAt)
      ((hu'.restrictScalars ℝ).comp x hA)).germ (Eventually.of_forall fun i=>?_)
    unfold jKernel; exact congr_arg _ (congr_arg ((u:ℂ)^·) (show W+L i-1=(W-1)+L i by abel)) -- orientation?
  exact (CR.mul hc' ((CR.affine hv W).comp (L.differentiableAt.const_add W) (half_diff _))
    ((hK.smooth _ hx).differentiableAt (by simp)) ((hH.smooth _ hx).differentiableAt (by simp))).germ (ha _ hx)
end YM.MSbar.Pole.Radial
