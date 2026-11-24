import YM.FormalOPE.RG10.Horizon.Survey
import YM.Extra.MULTISOURCE_TRAJECTORIES.Smooth

/-!
# Far arrangements for perturbative tests

Used for arbitrary fixed arity (including empty representations). Here both Profile-sensitive
applications are **absolute** smears (of a declared origin translated against a real test); no
replacing smeared fields by values on a grid. Permit the standard *real* compact-support inner
inputs with separated relative geometry (joint OK at the continuum-definition level).
Centered-testing implementation is by convolved kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Arrangements
open Position Grade Maxwell Labels MeasureTheory Topology Metric Function WithLp
open scoped Topology BigOperators ContDiff Classical
variable {m n : ℕ}

-- ancillary, align WITHOUT reversing or reflecting word slots

def paste : WithLp 2 (Points m × Points n) ≃ₗᵢ[ℝ] Points (m+n) where
  toFun w:= points (Fin.append w.fst.ofLp w.snd.ofLp)
  invFun y:= WithLp.toLp 2 (points (fun i=>y (Fin.castAdd n i)), points (fun i=>y (Fin.natAdd m i)))
  left_inv p:= by apply ofLp_injective 2; apply Prod.ext<;> (apply PiLp.ext; intro i; simp)
  right_inv p:= by apply PiLp.ext; intro i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  map_add' p q:=by apply PiLp.ext;intro i; refine Fin.addCases ?_ ?_ i<;>intro j<;> simp
  map_smul' t p:=by apply PiLp.ext; intro i; refine Fin.addCases ?_ ?_ i<;>intro j<;>simp
  norm_map' p:=by rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2 _ p.fst, PiLp.norm_sq_eq_of_L2 _ p.snd, Fin.sum_univ_add]; simp

def align : (Points m × Points n) ≃L[ℝ] Points (m+n) := (prodContinuousLinearEquiv 2 ℝ (Points m) (Points n)).symm.trans paste.toContinuousLinearEquiv
@[simp] lemma align_left (p:Points m) (q:Points n) (i) : align (p,q) (Fin.castAdd n i)=p i:= Fin.append_left ..
@[simp] lemma align_right (p:Points m) (q:Points n) (i) : align (p,q) (Fin.natAdd m i)=q i:= Fin.append_right ..
lemma align_conf {p:Points m}{q:Points n}(hp : p∈conf _)(hq:q∈conf _)(he:∀ i j,p i≠q j): align (p,q)∈conf _ := by
 intro i j h; revert h; refine Fin.addCases ?_ ?_ i <;> intro a <;> refine Fin.addCases ?_ ?_ j<;> intro b <;> simp only [align_left, align_right]
 · exact fun h=>congr_arg _ (hp h)
 · exact fun h=>False.elim (he a b h)
 · exact fun h=>False.elim (he b a h.symm)
 exact fun h=>congr_arg _ (hq h)
lemma aligned : MeasurePreserving (align (m:=m) (n:=n)) := (paste (n:=n) (m:=m)).measurePreserving.comp (WithLp.volume_preserving_toLp (Points m) (Points n))
def slide (z:E4) : Points n := YM.points fun _=>z
local instance : IsBoundedSMul ℝ (Points n) := .of_norm_smul_le NormedSpace.norm_smul_le
local instance : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
lemma slide_smooth : ContDiff ℝ ∞ (slide (n:=n)):= LinearMap.toContinuousLinearMap ( {
  toFun := slide
  map_add' := fun _ _=>rfl
  map_smul' := fun _ _=> rfl } : E4 →ₗ[ℝ] Points n) |>.contDiff

structure Rear (n:ℕ) where
  ext : RealTest n
  center : E4→ℝ
  narrow : ContDiff ℝ ∞ center
  compact : HasCompactSupport center
  gap : ℝ
  amount : 0 < gap
  stable : ∀ z∈ tsupport center, ∀ y∈tsupport ext,∀ i, gap ≤ dist z (y i)

structure Fore (m:ℕ) where
  core : RealTest m
  budget : ℝ
  sized : ∀ y ∈ tsupport core,∀ i, ‖y i‖ ≤ budget

-- absolute-coordinate definition (Wilson $check G_s(t)$). Scaling by 4n, capital lengths in the ``t'' parameter.
variable (F:Fore m)(B:Rear n)(t : ℝ)
local notation "Y" => Real.exp t

-- after converting center at length T to unscaled profile variable.
def draft (x : Points (m+n) × E4) := let v:= (@align m n).symm x.1;
   F.core (v.1-Y • slide x.2) * B.center x.2 * B.ext (Y⁻¹ • v.2) * (Y ^ (4*n))⁻¹

def pool (p:Points (m+n)):= ∫ x:E4,draft F B t (p,x)

def draw (p : E4 × Points m × Points n) := align (p.2.1+Real.exp t • slide p.1,Real.exp t • p.2.2)
lemma drawing : Continuous (draw (m:=m) (n:=n) t) :=
  align.continuous.comp (((continuous_fst.comp continuous_snd).add ((continuous_const (y:=Y)).smul (slide_smooth.continuous.comp continuous_fst))).prodMk ((continuous_const (y:=Y)).smul (continuous_snd.comp continuous_snd)))

def home : Set (Points (m+n)) := Set.image (draw (m:=m) (n:=n) t) ((tsupport B.center) ×ˢ ((tsupport F.core) ×ˢ tsupport B.ext))
lemma home_compact : IsCompact (home F B t) := IsCompact.image (IsCompact.prod B.compact (IsCompact.prod F.core.hasCompactSupport B.ext.hasCompactSupport)) (drawing ..)
lemma draft_support {x : Points (m+n)} {p:E4} (hp:draft F B t (x,p) ≠0) : x ∈ home F B t := by
 let u:= (@align m n).symm x; unfold draft at hp; dsimp only at hp; have H:= left_ne_zero_of_mul hp; have hs:= left_ne_zero_of_mul H; refine ⟨(p,u.1-Y • slide p,Y⁻¹ • u.2),⟨subset_closure (right_ne_zero_of_mul hs), subset_closure (left_ne_zero_of_mul hs), subset_closure (right_ne_zero_of_mul H)⟩,?_⟩
 unfold draw; dsimp only; rw [sub_add_cancel,smul_inv_smul₀ (Real.exp_pos t).ne']; exact align.apply_symm_apply _
lemma pool_lives : tsupport (pool F B t) ⊆ home F B t := by
 apply closure_minimal _ (home_compact F B t |>.isClosed)
 intro p ht; contrapose! ht;  apply notMem_support.mpr; unfold pool; simp_rw [show ∀ x:E4, draft F B t (p,x)=0 from fun x=>not_not.mp (fun hv=>ht (draft_support _ _ _ hv))]; simp

lemma draft_smooth : ContDiff ℝ ∞ (draft F B t):= by
 let f:= align (m:=m) (n:=n); unfold draft
 refine (((F.core.contDiff.comp ?_).mul (B.narrow.comp contDiff_snd)).mul (B.ext.contDiff.comp ?_)).mul contDiff_const
 · apply ContDiff.sub (contDiff_fst.comp (f.symm.contDiff.comp contDiff_fst)); exact (ContDiff.const_smul Y (slide_smooth.comp contDiff_snd)) -- (slide_smooth.comp contDiff_snd)
 exact ((contDiff_snd.comp (f.symm.contDiff.comp contDiff_fst))).const_smul (Y⁻¹)

lemma pool_smooth : ContDiff ℝ ∞ (pool F B t) := by
 let U:= tsupport B.center ∪ ({(0:E4)}:Set E4); have hc : IsCompact U:= IsCompact.union B.compact isCompact_singleton; let μ:= (volume :Measure E4).restrict U
 letI : IsFiniteMeasure μ:=by unfold μ; constructor; rw [Measure.restrict_apply MeasurableSet.univ]; simpa only [Set.univ_inter] using hc.measure_lt_top
 let p:= U.piecewise id (fun _=> (0:E4)); have hp x: p x∈U:=by
   by_cases h:x∈U; simp [p,h]
   rw [show p x=0 from Set.piecewise_eq_of_notMem _ _ _ h]; simp [U]
 have he(p':Points (m+n)) : pool F B t p'= ∫ a:E4,draft F B t (p',p a) ∂μ:= by
   calc
    _ = ∫ a:E4,draft F B t (p',a) ∂μ:= Eq.symm (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy=> by unfold draft; rw [image_eq_zero_of_notMem_tsupport (show y∉ tsupport B.center from fun h=>hy (Or.inl h))]; simp))
    _ = _:=by apply integral_congr_ae; filter_upwards [ae_restrict_mem (μ:=volume) hc.measurableSet] with a h; simp [p,h]
 rw [funext he]; exact Extra.Trajectories.integral_smooth (measurable_id.piecewise hc.measurableSet measurable_const |>.aestronglyMeasurable) hc hp (draft_smooth ..)

lemma safe (hx:F.budget < Y * B.gap) : home F B t ⊆ conf _ := by
 rintro p ⟨⟨x,y,z⟩,⟨hp,hy,hz⟩,rfl⟩
 have ht:= Real.exp_pos t; have hK : y∈conf m:= F.core.tsupport_subset hy
 refine align_conf ?_ ((Next.UVStress.enlarged ht z).1 (B.ext.tsupport_subset hz)) ?_
 · intro i j h; apply hK; change _+Y • x=_ + Y • x at h; exact add_right_cancel h
 intro i j he; have hl:= B.stable _ hp z hz j; have hi:= F.sized _ hy i; change y i+Y • x= Y • z j at he; rw [dist_eq_norm,norm_sub_rev] at hl;
 rw [← eq_sub_iff_add_eq,← smul_sub] at he; rw [he,norm_smul,Real.norm_of_nonneg ht.le] at hi; nlinarith

-- Communication as a Test used in the finite and continuum Gram estimates. No collision on any fixed t application.
def test (hx:F.budget < Y * B.gap): Test (m+n):=by
 have he : tsupport (fun x=>(↑(pool F B t x):ℂ)) ⊆ home F B t:=by
   have hi:=pool_lives F B t; rw [tsupport] at hi ⊢; simp only [support,Complex.ofReal_eq_zero,ne_eq] at *; exact hi
 exact ⟨fun x=>(↑(pool F B t x):ℂ), Complex.ofRealCLM.contDiff.comp (pool_smooth ..), IsCompact.of_isClosed_subset (home_compact ..) (isClosed_tsupport _) he,he.trans (safe F B t hx)⟩
end YM.FormalOPE.RG10.Arrangements
