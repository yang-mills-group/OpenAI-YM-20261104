import YM.Trace.Physicalv2.GermSplit
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Move
import YM.Extra.SOURCE_HISTORIES.Song

/-! A new canonical source on a genuinely nonbare vacuum is an admissible
linear field cohort for the original cone recurrence. Its unit has the
native mesh weight. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.BlockedTrialVoice
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Motion ProjectorNext.Equivariance
open scoped Classical BigOperators Topology
variable {G:Gauge} {d:ℕ} {F:Frame G d} {B:SectionData F} {H:History G} {P:Hol G}

private theorem rotated (h:B.Sound P) {n:Side} (rep:Rep G n) (v:F.Coeff) (s:Signed) (U:Config G n) :
    part B 0 rep (pull s 0 U) v=part B 0 rep U (F.act s.ortho v):=by
  have foot:B.footprint (affine s (0:Site n) 0)=(B.footprint (0:Site n)).image (affine s 0):=by
    unfold SectionData.footprint
    nth_rw 1 [←h.stable s]
    simp only [Finset.image_image,Function.comp_def,wrap_signed,affine,Signed.act_add,add_assoc]
  have root:affine s (0:Site n) 0=0:=by simp [affine]
  have mask:Healthy rep.p.threshold (B.footprint (0:Site n)) U ↔ Healthy rep.p.threshold (B.footprint 0) (pull s 0 U):=by
    nth_rw 1 [←root,foot];exact (healthy_pull ..).symm
  change v 0+masked _ _ _ _ = _+masked _ _ _ _
  by_cases good:Healthy rep.p.threshold (B.footprint 0) U
  · rw [masked_eq _ _ _ _ (mask.mp good),masked_eq _ _ _ _ good,atCore B h,atCore B h,F.scaling]
    simpa only [root] using B.placed_signed h s (0:Site n) 0 (F.scaled rep.p.threshold⁻¹ v) U
  rw [masked_ne _ _ _ _ (fun q=>good (mask.mpr q)),masked_ne _ _ _ _ good,add_zero,add_zero]
  exact (turn_scalar F s v).symm

private theorem conjugated (h:B.Sound P) {n:Side} (rep:Rep G n) (v:F.Coeff) (U:Config G n):
    part B 0 rep U (star v)=star (part B 0 rep U v):=by
  change (star v) 0+masked _ _ _ _ =star (v 0+masked _ _ _ _)
  by_cases good:Healthy rep.p.threshold (B.footprint 0) U
  · rw [masked_eq _ _ _ _ good,masked_eq _ _ _ _ good,atCore B h,atCore B h]
    rw [show F.scaled rep.p.threshold⁻¹ (star v)=star (F.scaled rep.p.threshold⁻¹ v) from funext fun j => by simp]
    exact h.ordinary_real ..
  rw [masked_ne _ _ _ _ good,masked_ne _ _ _ _ good,add_zero,add_zero];rfl

def currency (H:History G) (d N K:ℕ):ℝ := (H.S.a K / H.S.a N)^d
private theorem currency_pos (H:History G) (d N K:ℕ):0<currency H d N K :=
  pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _

def denomination (F:Frame G d) (H:History G) (N K:ℕ):F.Coeff ≃ₗ[ℂ] F.Coeff where
  toFun x := ((currency H d N K:ℝ):ℂ) • x
  invFun x:= (((currency H d N K:ℝ):ℂ)⁻¹) • x
  left_inv x:=by dsimp only;rw [smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (currency_pos H d N K).ne'),one_smul]
  right_inv x:=by dsimp only;rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (currency_pos H d N K).ne'),one_smul]
  map_add' _ _:=smul_add ..
  map_smul' _ _:=smul_comm ..

def trial (F:Frame G d) (H:History G) (N p K:ℕ):Voice F H p K where
  plays x:=primary 0 (denomination F H N K x)
  charge _:=0
  index:=denomination F H N K

theorem submitted (N p K:ℕ) (x:F.Coeff):
    (trial F H N p K).plays ((denomination F H N K).symm x)= (primary 0 x:Coefficient F (H.S.side K p)):=by
  change primary _ ((denomination F H N K) _)=_;rw [LinearEquiv.apply_symm_apply]

theorem enrolled (h:H.Selected) (hs:B.Sound P) {N p K:ℕ} (live:K≤N):
    Heard B H N p P K (trial F H N p K):=by
  let V:=trial F H N p K
  let rep:=H.rep N p K
  let A:=denomination F H N K
  have align (s:Motion) (x:F.Coeff):Motion.patch F s (A x)=A (Motion.patch F s x):=by
    change Motion.patch F s (((currency H d N K:ℝ):ℂ) • x)=((currency H d N K:ℝ):ℂ) • _
    rw [Motion.patch_smul,Motion.scalar_real]
  have value (x:F.Coeff) (U): (V.plays x).density 0 B rep U=(liftVac H N p K U)*part B 0 rep U (A x):=
    primary_density _ _ _ _
  refine ⟨?_,?_,fun _=>rfl,?_,fun _ _=>by simp [trial],fun x s=>align s x,?_,?_,?_⟩
  · refine ⟨⟨A.map_add,A.map_smul⟩,⟨?_,?_⟩,⟨?_,?_⟩,fun _=>rfl⟩ <;> intros <;> simp [trial,primary]
  · intro x; exact ⟨primary_format _,primary_rem _ (Real.sqrt_pos.mpr (Real.exp_pos _))⟩
  · intro x; exact mul_nonneg (zero_le_one.trans (H.levels.params K).columns_ge) (Work.G08.size_nonneg ..)
  · change (((currency H d N K):ℝ):ℂ) • (((H.S.a N:ℂ)^d)•F.e0)=((H.S.a K:ℂ)^d)•F.e0
    rw [smul_smul];congr 1
    simp only [currency,Complex.ofReal_pow,Complex.ofReal_div,div_pow]
    field_simp [Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne']
  · constructor
    · intro x y;funext U;rw [show (V.plays (x+y)).density 0 B rep U=_ from value _ _]
      change _ = (V.plays x).density 0 B rep U+(V.plays y).density 0 B rep U;rw [value,value,A.map_add,map_add,mul_add]
    intro a x;funext U;change (V.plays (a•x)).density 0 B rep U=a*(V.plays x).density 0 B rep U
    rw [value,value,A.map_smul,map_smul,smul_eq_mul];ring
  · intro x s;funext U
    change scalar s ((V.plays x).density 0 B rep (pull s.1 0 U))=(V.plays (Motion.patch F s x)).density 0 B rep U
    rw [value,value,Motion.scalar_mul,vac_pull H N p K h live,show scalar s (liftVac H N p K U)=liftVac H N p K U from Motion.scalar_real ..,←align,rotated hs rep]
    unfold Motion.scalar Motion.patch
    split
    · rw [conjugated hs rep]
    rfl

end YM.SignedWilsonExpansion.Purchases.BlockedTrialVoice
end
