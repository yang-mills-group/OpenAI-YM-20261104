import YM.XSpace.LiftCyl
import YM.XSpace.Curled

/-!
# Signed-coordinate group and color group on the unconditioned finite unit-step periodic curls

No appeal to translational invariance of an inversion quotient. Only the spaces used for the
Wick-jet *initialization* of top columns. Covariance degeneracy included. Elegant shortcut:
perform signed comparison ON Curled only, using the actual invariance of the plaquette action
and differentiate the exact unscaled sampled-coordinate identity in the flat chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Top
open Function Filter Set Lattice Exterior Wilson Labels Source Source.Drops
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators

section
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Descend on finite-dimensional spaces, without any price on the quotient identifications. -/
lemma leaves (p : E →ₗ[ℝ] F) (hp : Surjective p) (b : E→ₗ[ℝ]E) (he : ∀ x, ‖p (b x)‖=‖p x‖):
    ∃ L : F ≃ₗᵢ[ℝ] F, ∀ x, L (p x)=p (b x) := by
  obtain ⟨r,hr⟩ := hp.hasRightInverse
  have h (x y : E) (h : p x=p y) : p (b x)=p (b y):= sub_eq_zero.mp (norm_eq_zero.mp (show ‖p (b x)-p (b y)‖=0 by rw [← map_sub,← map_sub,he,map_sub,h,sub_self,norm_zero]))
  let f x:=p (b (r x))
  have ht x:f (p x)=p (b x):= h _ _ (hr (p x))
  let L:F →ₗ[ℝ] F:=
    { toFun:= f
      map_add':= by intro x y; obtain ⟨x,rfl⟩:=hp x; obtain ⟨y,rfl⟩:=hp y; rw [← map_add,ht,ht,ht,map_add,map_add]
      map_smul':= by intro c x; obtain ⟨x,rfl⟩:=hp x; rw [← map_smul,ht,ht,map_smul,map_smul]; rfl }
  let M:F →ₗᵢ[ℝ] F:={toLinearMap:=L,norm_map':= fun x=> (he (r x)).trans (congr_arg _ (hr x))}
  exact ⟨LinearIsometryEquiv.ofSurjective M ((LinearMap.injective_iff_surjective (f:=L)).1 M.injective),ht⟩
end

variable (G : Gauge) (n : Side)
def selectCurl := (curl G n).rangeRestrict
lemma sector_range : Surjective (selectCurl G n) := LinearMap.surjective_rangeRestrict _

def turning (s : Signed) : Input G n→ₗ[ℝ]Input G n where
  toFun x:= Bid.pulled x s
  map_add' x y:= by
    funext i; simp only [Bid.pulled,Pi.add_apply]; split <;> abel
  map_smul' t x:= by
    funext i; simp only [Bid.pulled,RingHom.id_apply,Pi.smul_apply]; split_ifs <;> simp

lemma norm_curl (x : Input G n) : ‖selectCurl G n x‖^2=∑ i, ‖curl G n x i‖^2 := PiLp.norm_sq_eq_of_L2 _ _
lemma action_priced (x : Input G n) :
    Tendsto (fun t:ℝ => Wilson.energy (Precision.represent (t • x))/t^2) (𝓝[≠] 0) (𝓝 (‖selectCurl G n x‖^2/2)):=by
  rw [norm_curl]; simp_rw [Wilson.energy,Finset.sum_div]; exact tendsto_finsetSum _ fun i _ => Work.F03.price_limit (V:=fun t : ℝ => faceValue (Precision.represent (t • x)) i)
    (by rw [zero_smul]; exact Push.stroll_zero ..) (Work.F03.face_deriv i x)
lemma norm_turning (s : Signed) (x : Input G n): ‖selectCurl G n (turning G n s x)‖=‖selectCurl G n x‖:=by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  refine (div_left_inj' two_ne_zero).1 (tendsto_nhds_unique ?_ (action_priced G n x))
  have ht:= action_priced G n (Bid.pulled x s)
  simp_rw [← Work.F03.represent_pulled,Wilson.energy_pull] at ht
  exact ht

def tint (a : G.El) : Input G n→ₗ[ℝ]Input G n:= LinearMap.pi fun i=> G.adjoint a ∘ₗ LinearMap.proj i
lemma tint_action (x : Input G n) (i : Faces n) (a) : curl G n (tint G n a x) i=G.adjoint a (curl G n x i):= by
  have he (b : Input G n) (w : Walk) (x : Site n) : linkSum (collect G (tint G n a b)) x w=
      G.adjoint a (linkSum (collect G b) x w):=by
    induction w generalizing x with
    | nil => rw [linkSum,linkSum,map_zero]
    | cons d w ih=> rw [linkSum,linkSum,map_add,ih]; split; rw [map_neg]; rfl; rfl
  rw [curl_val, curl_val,Work.F03.faceCurl, Work.F03.faceCurl,← fundamental,← fundamental]; exact he ..
lemma norm_tint (a : G.El) (x : Input G n): ‖selectCurl G n (tint G n a x)‖=‖selectCurl G n x‖:=by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [norm_curl,norm_curl]; simp [tint_action]

-- Detector at the origin. Use all stencil positions (including after orientation change).
variable {G} {H : Hol G} {d : ℕ} (A : Survey G H d)

def readPanel : Forms G n →ₗ[ℝ] GaugePanel G A.size := LinearMap.pi (fun i=> (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Faces n=> G.Color) (Work.F03.slotFace (A.looks i) (0:Site n))).toLinearMap)

def detector := A.extract.toLinearMap ∘ₗ readPanel n A ∘ₗ (Curled G n).subtype
lemma detects (u : Curled G n) : detector n A u=A.extract (readPanel n A u.val):=rfl
lemma measures (x : Input G n) (w : Site n):
    HasDerivAt (fun t : ℝ => Bid.mapped A.looks (expandAt w (Precision.represent (t • x))))
      (fun i=> curl G n x (Work.F03.slotFace (A.looks i) w)) 0 := hasDerivAt_pi.mpr fun _=> Work.F03.slot_deriv ..

lemma circled (s : Signed) (u : Input G n) : readPanel n A (curl G n (turning G n s u)) = A.roll s (readPanel n A (curl G n u)):=by
  apply (measures n A (Bid.pulled u s) 0).unique
  have ht := (A.roll s).hasFDerivAt.comp_hasDerivAt (0:ℝ) (measures n A u 0)
  apply ht.congr_of_eventuallyEq
  filter_upwards with t
  rw [← Work.F03.represent_pulled,expandAt_pull]; simp only [affine,Signed.act_zero,add_zero,A.takes]; rfl

lemma bridges_signed (s : Signed) : ∃ L : Curled G n ≃ₗᵢ[ℝ] Curled G n, ∀ x : Curled G n, detector n A (L x) = snapTurn s.ortho⁻¹ (detector n A x) :=by
  obtain ⟨L,hL⟩:= leaves _ (sector_range G n) (turning G n s) (norm_turning G n s)
  refine ⟨L,fun x=>?_⟩; obtain ⟨x,rfl⟩:=(sector_range G n x); rw [hL,detects]
  change A.extract (readPanel n A (curl G n _))=_; rw [circled,A.extract_signed]; rfl
lemma bridges_color (a : G.El) : ∃ L : Curled G n ≃ₗᵢ[ℝ] Curled G n, ∀ x : Curled G n, detector n A (L x)=snapColor a (detector n A x) := by
  obtain ⟨L,hL⟩:= leaves _ (sector_range G n) (tint G n a) (norm_tint G n a)
  refine ⟨L,fun x=>?_⟩; obtain ⟨x,rfl⟩:=sector_range G n x; rw [hL, detects]
  rw [show readPanel n A (selectCurl G n (tint G n a x))=rotates a (readPanel n A (curl G n x)) from funext fun _=> tint_action .., A.extract_color]; rfl
end YM.XSpace.Top
