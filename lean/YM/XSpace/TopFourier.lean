import YM.XSpace.Compat.Native
import YM.Planned.RECIPE_STARTUP_PORT.FreeEdge
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Scalar

/-!
# Bare Wilson massless lattice curl covariance

On the ordinary (NOT inversion quotient) grid. At the stationary top, unconditioned. On the
infinite unit-step lattice use the limit of this Fourier formula; in particular the self Wick
subtractions of bare operator columns will use neither a finite inversion regulator nor a
continuum free covariance. Include all arguments including at distance zero. Reuse the
substantial bounds from Further.FreeCovariance.KP for this *specific* symbol.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Top
open Filter Function Set Lattice Laurent Bloch Exterior Matrix Precision Next.Free Complex PhysicalNext.RankCovariance
open Further.FreeCovariance.KP WilsonStartup
open scoped Topology BigOperators ComplexConjugate
variable (n : Side)

/-- Body(r, n) in the baseline exterior derivative convention. -/
def projector := scalarCov 1 (.top 4) n
lemma projection :
    (projector n)ᵀ=projector n ∧ (∃ X:Matrix (Body 1 n) (Body 2 n) ℝ, projector n= Exterior.d 1 n*X) ∧
    projector n * Exterior.d 1 n=Exterior.d 1 n :=by
  let p:RG.Clip:=⟨1,1/32,1,by norm_num,by norm_num,by norm_num,by norm_num⟩
  have H:= Design.level p (le_refl 1) n (le_refl 1) (le_refl 1)
  have hc : Defined 1 0 (Train.top 4) (Design.bed p):=Planned.Port.Edge.express 1 one_pos 4 le_rfl p
  let D := Exterior.d 1 n
  let X:= Further.CorrectedLift.Resolve.field H one_pos
  have hp : projector n=D*X:= scalar_eq_screen H one_pos hc le_rfl one_pos
  have he : (Dᵀ*D)*X=Dᵀ := by
    apply Eq.trans _ (Further.CorrectedLift.Resolve.hinge H one_pos); congr 1
    simp [Precision.K,Further.CorrectedLift.Resolve.charge,Design.bed,Design.spike_acts,D]
  have ht : (projector n)ᵀ=projector n:=scalar_symm one_pos ..
  refine ⟨ht,⟨X,hp⟩,?_⟩; change projector n * D=D
  apply_fun Matrix.transpose using transpose_injective
  rw [transpose_mul,ht,hp,← Matrix.mul_assoc,he]

lemma naked_metric (p : Momentum) : fieldD 1 1 (.top 4) p=(divisor 1 p)⁻¹ • 1 := by
  have h : scaleD 1 1 (.top 4) p=fun _=> (divisor 1 p)⁻¹ := by
    funext i; unfold scaleD Train.levelD; rw [feed_top]; simp [Train.levelNoise,Train.nozzle,Train.stream]
  unfold fieldD; rw [h]; simpa only [mul_one,pow_one,mask_one] using mask_scale 1 (fun _ => 1) (divisor 1 p)⁻¹

def delta (p : Momentum) := ∑ i, Exterior.q p i * Exterior.q (-p) i
lemma naked_divisor (p : Momentum) : divisor 1 p = delta p := by simp [divisor,delta,seedQ,chip,Exterior.q,narrow_apply]

/-- Full discrete torus Fourier kernel. `momentum=0` term is zero. -/
def symbol (p : Momentum) : Matrix (TypeFace 2) (TypeFace 2) ℂ := (delta p)⁻¹ • (Exterior.symbol 1 p*(Exterior.symbol 1 p)ᴴ)
lemma arc_symbol (p : Momentum) : Episode.arc 1 (.top 4) p = symbol p:= by rw [Episode.arc,naked_metric,naked_divisor,symbol,Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
@[simp] lemma symbol_zero : symbol 0=0 := by rw [← arc_symbol,Episode.zero_harmonic]

def fourier (i j : PlaqAxes) (x : Cover) : ℂ := ((n.val:ℂ)^4)⁻¹ * ∑ k:Site n, mode (mon k) x * symbol (mon k) (plaquette i) (plaquette j)
lemma from_episode (i j : PlaqAxes) : fourier n i j=Episode.found 1 (.top 4) n (plaquette i) (plaquette j) := by
  funext; unfold fourier Episode.found; simp_rw [← arc_symbol]; rfl
lemma fourier_entry (x y : Site n) (i j : PlaqAxes) {u : Cover} (h : wrap n u=x-y) :
    ((projector n (x,plaquette i) (y,plaquette j):ℝ):ℂ)=fourier n i j u := by
  rw [projector,scalar_entry one_pos,from_episode]; apply Episode.wraps; rw [map_sub,wrap_lift,wrap_lift,h]
lemma entry_real (i j : PlaqAxes) (u : Cover) : ((fourier n i j u).re:ℂ)=fourier n i j u := by
  rw [← fourier_entry n (wrap _ u) 0 i j (by simp)]; simp

-- a convenient regular choice of period (native).
def side (k : ℕ) : Side:=⟨4+k,by omega⟩
lemma grows : Tendsto (fun i=>(side i).val) atTop atTop := tendsto_atTop_mono (fun i : ℕ=> (Nat.le_add_left i 4)) tendsto_id

private lemma cover_exists (i j : PlaqAxes) : ∃ g:Cover→ℂ,∃ C:ℝ,0≤C∧∀ n : Side, ∀ x:Cover,
    ‖fourier n i j x-g x‖≤ C*(1+‖rcast x‖)/n.val := by
  obtain ⟨a,Ω,v,ha,hv,h⟩:=Episode.paid 1 one_pos (j:=4) le_rfl
  obtain ⟨f,hf⟩:= h (.top 4); obtain ⟨C,hC,H⟩:=YM.XSpace.Compat.KP.lift_mesh [] [] (Ω:=Ω) ha hv (plaquette i) (plaquette j)
  refine ⟨(fun x=> retract (fun p=>rebus [] [] f p (plaquette i) (plaquette j)) (rcast x)), C,hC, fun n x=>?_⟩
  rw [from_episode,← Episode.bridge 1 one_pos (hj:=le_rfl) ha hv (.top 4) f hf]; exact H f n x

def coverLine (i j : PlaqAxes) : Cover → ℂ:= (cover_exists i j).choose
lemma cover_price (i j : PlaqAxes) : ∃ C:ℝ,0≤C∧∀ n : Side, ∀ x:Cover, ‖fourier n i j x-coverLine i j x‖ ≤ C*(1+‖rcast x‖)/n.val:= (cover_exists i j).choose_spec
lemma fourier_limit {ι : Type*} {L : Filter ι} {n : ι→Side} (h : Tendsto (fun i=>(n i).val) L atTop) (i j : PlaqAxes) (x : Cover) :
    Tendsto (fun p=>fourier (n p) i j x) L (𝓝 (coverLine i j x)):=by
  obtain ⟨C,-,H⟩ := cover_price i j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _=> norm_nonneg _) (fun _=> H _ x) (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h))

lemma cover_real (i j : PlaqAxes) (x : Cover) : ((coverLine i j x).re:ℂ)=coverLine i j x:=by
  have ht:= fourier_limit (n:=side) grows i j x
  apply tendsto_nhds_unique _ ht; apply ((continuous_ofReal.tendsto _).comp ((continuous_re.tendsto _).comp ht)).congr (fun n=> entry_real ..)
lemma cover_symm (i j : PlaqAxes) (x : Cover) : coverLine i j x=coverLine j i (-x) := by
  apply tendsto_nhds_unique (fourier_limit (n:=side) grows i j x) _
  refine (fourier_limit (n:=side) grows j i (-x)).congr fun p=>?_
  rw [← fourier_entry _ (wrap _ x) 0 i j (by simp), ← fourier_entry _ 0 (wrap _ x) j i (by simp)]
  congr 1
  exact congr_fun (congr_fun (projection _).1 _) _
end YM.XSpace.Top
