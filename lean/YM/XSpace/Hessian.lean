import YM.XSpace.FlatLinks
import YM.Work.F03.Flat
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The flat saddle used by the bare Wilson diagrams in X space

Physical color normalization and lattice step conventions are **the same** as the
Wilson theory. At the prescribed IR regulator with no zero modes include a factor of a
half on the plaquette sum. Differentiate the actual analytic germ in native/color link
coordinates, with `g` factored **out** of the tangent vector. No external masses or
hand-picked free precision. This is not a saddle approximation or statement of convenience
of using the tree gauge for estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Period.Tree
open Function Set Filter Lattice Wilson Exterior Precision
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {R : Period} (T : R.Tree)

abbrev Field (G : Gauge) := T.Free → G.Color
abbrev Key (G : Gauge) := (_ : T.Free) × G.ColorIndex
instance keyFintype (G : Gauge) : Fintype (T.Key G) := inferInstance
instance keyDecidableEq (G : Gauge) : DecidableEq (T.Key G) := inferInstance

def basis (G : Gauge) : Module.Basis (T.Key G) ℝ (T.Field G) :=
  Pi.basis fun _ : T.Free => (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis

/-- Include both eliminated tree links and inversion-orbit identification on links. -/
def links (v : T.Field G) : Config G R.side := R.restore (T.drape (G.lieExp ∘ v))
lemma links_apply (v : T.Field G) (e : R.Bonds) : T.links v e = G.lieExp (T.covering v e) := by
  have h (e : R.Link) : T.drape (G.lieExp ∘ v) e = G.lieExp (T.prolong v e) := by
    unfold prolong; split
    next he => rw [G.mat_lieExp_zero]; exact T.drape_tree _ ⟨e,he⟩
    next he => exact T.drape_free _ ⟨e,he⟩
  simp only [links, restore, covering, Period.extend,LinearMap.coe_mk,AddHom.coe_mk,h]; split_ifs
  · rfl
  rw [Work.F03.exp_neg_color]
lemma links_zero : T.links (0 : T.Field G)=1 := funext fun e=> by simp [links_apply]

def action (v : T.Field G) : ℝ := R.energy (T.drape (G.lieExp ∘ v))

/-- For comparison to orientation/curl conventions of the baseline. -/
def logdir : T.Field G →ₗ[ℝ] fieldDir G R.side 1 where
  toFun u e:= T.covering u (e.1,axisEquiv.symm e.2)
  map_add' _ _:= funext fun e=> by rw [map_add]; rfl
  map_smul' _ _:= funext fun e=> by rw [map_smul]; rfl
lemma collected (u : T.Field G) : collect G (T.logdir u) = T.covering u := by
  ext1 e; simp only [collect,logdir,LinearMap.coe_mk,AddHom.coe_mk,show ∀ i, axisEquiv.symm (coord i)=i from fun i=> axisEquiv.symm_apply_apply i]
lemma represent_eq (u : T.Field G) : represent (T.logdir u)=T.links u:=by
  funext e; rw [links_apply,Work.F03.represent_link]; rw [← collected]; rfl
lemma curl_eq (u : T.Field G) (p : Face (Per R.side)) : Work.F03.faceCurl p (T.logdir u)=R.curl (T.covering u) p:=by
  ext i
  rw [curl_at]; change Matrix.mulVec (d 1 R.side) _ _ = _
  rw [Exterior.d_plaquettes]; unfold Period.curlIJ
  rw [← collected]; unfold collect parts; simp only [PiLp.sub_apply,PiLp.add_apply]; abel
lemma face_tangent (u : T.Field G) (p : Face (Per R.side)) :
    HasDerivAt (fun t : ℝ=> G.mat (faceValue (T.links (t • u)) p)) (G.colorMat (R.curl (T.covering u) p)) 0 := by
  simp_rw [← represent_eq,← curl_eq T u p, map_smul]; exact Work.F03.face_deriv p _

lemma continuousJet (G : Gauge) : ContDiffAt ℝ ω (T.action (G:=G)) 0 := by
  change ContDiffAt ℝ ω (fun v => Wilson.energy (T.links v)/2) 0
  have hp {e : R.Bonds} : ContDiffAt ℝ ω (fun v:T.Field G => G.mat (T.links v e)) 0 := by
    simp_rw [← represent_eq]
    exact (Work.F03.represent_smooth ..).contDiffAt.comp _ (LinearMap.toContinuousLinearMap (T.logdir (G:=G))).contDiff.contDiffAt
  have ht (w : Walk) (x : R.Sites) : ContDiffAt ℝ ω (fun v:T.Field G=> G.mat (travel (T.links v) x w)) 0 := by
    induction w generalizing x with
    | nil => exact contDiffAt_const
    | cons d w ih => simp only [travel,G.mat_mul]; apply ContDiffAt.mul _ (ih _); unfold Step.read; split
                     · simp_rw [G.mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ hp
                     exact hp
  exact (ContDiffAt.sum fun p _=> Work.F03.price_smooth (A:=fun v=>faceValue (T.links v) p) (ht _ _)).div_const _

def linearCurl : T.Field G →ₗ[ℝ] (Face (Per R.side) → G.Color) := R.curl ∘ₗ T.covering

def quadratic (G : Gauge) : LinearMap.BilinForm ℝ (T.Field G) :=
  (2:ℝ)⁻¹ • ∑ p : Face (Per R.side),
    (innerₗ G.Color).compl₁₂ (LinearMap.proj p ∘ₗ T.linearCurl) (LinearMap.proj p ∘ₗ T.linearCurl)
lemma quadratic_val (v w : T.Field G) : T.quadratic G v w = (∑ p, inner ℝ (T.linearCurl v p) (T.linearCurl w p))/2 := by
  unfold quadratic; simp only [LinearMap.smul_apply, LinearMap.sum_apply]; rw [div_eq_inv_mul]; rfl
lemma symmetric (u v : T.Field G) : T.quadratic G u v=T.quadratic G v u := by
  rw [quadratic_val,quadratic_val]; exact congr_arg (·/2) (Finset.sum_congr rfl fun _ _=> real_inner_comm ..)
lemma ray (v : T.Field G) :
    Tendsto (fun t : ℝ => T.action (t • v)/t^2) (𝓝[≠] 0) (𝓝 (T.quadratic G v v/2)) := by
  have ht (p : Face (Per R.side)) := Work.F03.price_limit (V:=fun t : ℝ => faceValue (T.links (t • v)) p)
    (by simp_rw [← represent_eq,zero_smul,map_zero]; exact Push.stroll_zero ..) (T.face_tangent v p)
  change Tendsto (fun t:ℝ => Wilson.energy (T.links (t • v))/2/t^2) _ _
  rw [quadratic_val]; simp_rw [real_inner_self_eq_norm_sq,linearCurl, LinearMap.comp_apply]
  unfold Wilson.energy
  conv => arg 1; ext t; rw [div_right_comm _ (2:ℝ) (t^2)]
  simp_rw [Finset.sum_div]; exact tendsto_finsetSum _ (fun p _ => (ht p).div_const 2)

theorem action_jets (G : Gauge) : T.action (G:=G) 0 = 0 ∧ fderiv ℝ T.action (0:T.Field G) = 0 ∧
    ∀ x y : T.Field G, iteratedFDeriv ℝ 2 T.action 0 ![x,y] = T.quadratic G x y :=
  Work.F03.hessian_of_limit ((T.continuousJet G).of_le le_top) T.ray
    (by intros; simp) T.symmetric

def hessian (G : Gauge) := (T.quadratic G).toMatrix (T.basis G)
lemma hessian_entries (G : Gauge) (i j : T.Key G) : T.hessian G i j = iteratedFDeriv ℝ 2 T.action 0 ![T.basis G i,T.basis G j] := by
  rw [(T.action_jets G).2.2]; simp [Tree.hessian]
lemma quadratic_pos {x : T.Field G} (hx : x≠0) : 0 < T.quadratic G x x := by
  have he : T.linearCurl x≠0:= fun h=> hx (T.no_modes _ h)
  obtain ⟨p,hp⟩:=(Function.ne_iff.mp he)
  rw [quadratic_val]; simp_rw [real_inner_self_eq_norm_sq]
  exact div_pos (Finset.sum_pos' (fun _ _=>sq_nonneg _) ⟨p,Finset.mem_univ _,pow_pos (norm_pos_iff.mpr hp) _⟩) two_pos

theorem hessian_posDef (G : Gauge) : (T.hessian G).PosDef :=
  (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (T.basis G) (T.quadratic G) ⟨T.symmetric⟩).1
    (fun _ h=>T.quadratic_pos h)

def covariance (G : Gauge) : Matrix (T.Key G) (T.Key G) ℝ := (T.hessian G)⁻¹
lemma covariance_posDef (G : Gauge) : (T.covariance G).PosDef := (T.hessian_posDef G).inv
@[simp] lemma covariance_val (G : Gauge) : T.hessian G*T.covariance G=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (T.hessian_posDef G).isUnit)
end YM.XSpace.Period.Tree
