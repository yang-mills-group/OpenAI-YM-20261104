import YM.XSpace.Garment
import YM.XSpace.WickOperator
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color

/-!
# Gluing local gauge identities through the invariant fields

Uses actual analytic section W^-1 (comes in via Bare.column operator bridge next).
Gauge propagates to every formal label up to this order as a polynomial identity
in the **actual coordinates**, no antisymmetric-generator assumptions needed.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.XSpace.Chart2
open CubicMatch Function Lattice RG Next.Rank.Normal Labels Wilson Source Source.Drops Bid Work.G05 MvPolynomial
open scoped BigOperators Pointwise Topology ContDiff
variable {G : Gauge} {d : ℕ} {H : Hol G} {R : Type*} [AddCommGroup R] [One R] (S: Survey G H d) (x: Four R)
def spectra : LogLinks R G→ₗ[ℝ] GaugePanel G S.size :=LinearMap.pi fun i=>take1 (S.looks i) x
def accent (A:LogLinks R G): GaugePanel G S.size:= fun i=> take2 (S.looks i) x A

def primary := S.extract.toLinearMap.comp (spectra S x)
def curvature2 (A:GaugePanel G S.size):= (2:ℝ)⁻¹ • iteratedFDeriv ℝ 2 S.recover 0 (fun _=>A)
def secondary (A:LogLinks R G):= curvature2 S (spectra S x A)+ S.extract (accent S x A)

lemma primary_pol : Record G fun A=> primary S x A := by
  refine Record.move S.extract.toLinearMap (Record.pi (fun A=> spectra S x A) fun i=> ?_); exact slope_polynomial G (slotPoint x (S.looks i))
private lemma record2 {Z E F :Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : (Z→G.Color)→E} {b:E→F} (p : Record G v) : Record G (fun A=> (2:ℝ)⁻¹ • iteratedFDeriv ℝ 2 b 0 (fun _=> v A)):=by
  let M:= fderiv ℝ (fderiv ℝ b) 0; let L : (E →L[ℝ] F) →ₗ[ℝ] E →ₗ[ℝ] F:= ContinuousLinearMap.coeLM ℝ
  simp_rw [iteratedFDeriv_two_apply]; exact (Record.pairing (L.comp M.toLinearMap) p p).smul _
lemma secondary_pol : Record G (secondary S x):= by
  have he : Record G (fun A=> accent S x A):= Record.pi _ (fun i=> second_slot G (S.looks i) x)
  have hh : Record G (fun A=> spectra S x A):= Record.pi _ (fun i=> slope_polynomial G (slotPoint x (S.looks i)))
  unfold secondary; exact (record2 (b:=S.recover) hh).add (Record.move S.extract.toLinearMap he)

def leftKey (i:Labels.Key G) := (primary_pol S x (Survey.component i)).pol
def rightKey (i:Labels.Key G) := (secondary_pol S x (Survey.component i)).pol
lemma pit_left (k: Labels.Key G) (A:LogLinks R G): pit A (leftKey S x k)= snapCoord d k (primary S x A):= Reads.value ..
lemma pit_right (k: Labels.Key G) (A:LogLinks R G): pit A (rightKey S x k)= snapCoord d k (secondary S x A):= Reads.value ..

def knit (k: Labels.Key G): PowerSeries (St R G):= PowerSeries.mk fun i=> if i=0 then leftKey S x k else if i=1 then rightKey S x k else 0
@[simp] lemma constant_knit (k:Labels.Key G): PowerSeries.constantCoeff (knit S x k) = leftKey S x k:= by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [knit]
@[simp] lemma coefficient_knit (k:Labels.Key G): PowerSeries.coeff 1 (knit S x k)= rightKey S x k:= by simp [knit]

def toy : Labels.Pol G →ₐ[ℂ] PowerSeries (St R G) := aeval (knit S x)
def p0 (K: Labels.Pol G) := PowerSeries.constantCoeff (toy S x K)
def p1 (K: Labels.Pol G) := PowerSeries.coeff 1 (toy S x K)

def awaken (d:ℕ) (K:Labels.Pol G) (A:Snap G d):= read (expand d A) K
lemma awake0 (K: Labels.Pol G) (A : LogLinks R G): pit A (p0 S x K)=awaken d K (primary S x A):=by
  unfold p0 toy awaken; induction K using MvPolynomial.induction_on with
  | C a=> rw [aeval_C,PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]; simp [Labels.read,pit]
  | add p q h1 h2=> simp only [map_add,h1,h2]
  | mul_X p i hp=> simp only [map_mul,hp]; rw [aeval_X]; simp only [constant_knit,pit_left,snapCoord_eq,Labels.read,aeval_X]
lemma awake1 (K: Labels.Pol G) (A : LogLinks R G): pit A (p1 S x K)= fderiv ℝ (awaken d K) (primary S x A) (secondary S x A):=by
  set a:=primary S x A; set c:=secondary S x A
  let V t:= read (expand d (a+(t:ℝ) • c)); have he : HasDerivAt (fun t:ℝ=>a+t • c) c 0:=by simpa only [zero_add,one_smul] using! (hasDerivAt_const (0:ℝ) a).add ((hasDerivAt_id' 0).smul_const c)
  have ht : ∀ k : Labels.Pol G, HasDerivAt (fun t:ℝ=> V t k) (pit A (p1 S x k)) 0:=by
    intro k; induction k using MvPolynomial.induction_on with
    | C u=> simp only [V,p1,toy,Labels.read,aeval_C,PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]; simp; exact hasDerivAt_const _ _
    | add j k h1 h2=> rw [show p1 S x (j+k)=p1 S x j+p1 S x k by simp only [p1,map_add]]; simp only [map_add]; exact h1.add h2
    | mul_X p i hp=>
      set g:=snapCoord d i
      have hh : ∀ t, V t (MvPolynomial.X i)= g (a+t • c):=by intro t; simp only [V,Labels.read,aeval_X]; rfl
      have h0 (k): V 0 k=read (expand d a) k:=by unfold V; rw [zero_smul,add_zero]
      have hx := hp.mul (show HasDerivAt (fun t=> V t (MvPolynomial.X i)) (g c) 0 by simp_rw [hh]; exact g.hasFDerivAt.comp_hasDerivAt 0 he)
      simp only [map_mul,p1,toy, PowerSeries.coeff_one_mul,aeval_X,coefficient_knit,constant_knit,map_add]
      rw [pit_right,pit_left, ← show p0 S x p= PowerSeries.constantCoeff ((aeval (knit S x)) p) from rfl,awake0]; unfold awaken; rw [h0 p, hh,zero_smul,add_zero,mul_comm (read _ p)] at hx; exact hx
  have hp : DifferentiableAt ℝ (awaken d K) (a+(0:ℝ) • c):= (snap_read_smooth d K ω).differentiable (by simp) _
  apply (ht K).unique; simpa only [zero_smul,add_zero] using! hp.hasFDerivAt.comp_hasDerivAt 0 he
lemma spectra_grad (v:Four R→G.Color): spectra S x (grad v)=0:= funext fun i=>face_grad (slotPoint x (S.looks i)) _
lemma primary_at (A: LogLinks R G): primary S x A=S.extract (spectra S x A):=rfl

lemma primary_gradient (v:Four R→G.Color): primary S x (grad v)=0:=by rw [primary_at,spectra_grad,map_zero]
lemma awake_work (K: Labels.Pol G) (A Y : LogLinks R G): pit A (D Y (p0 S x K))= fderiv ℝ (awaken d K) (primary S x A) (primary S x Y):=by
  have h:= directional A Y (p0 S x K); simp_rw [awake0,map_add,map_smul] at h
  let a:=primary S x A; let c:=primary S x Y
  have he : HasDerivAt (fun t:ℝ=>a+t • c) c 0:=by simpa only [zero_add,one_smul] using! (hasDerivAt_const (0:ℝ) a).add ((hasDerivAt_id' 0).smul_const c)
  have hp : DifferentiableAt ℝ (awaken d K) (a+(0:ℝ) • c):= (snap_read_smooth d K ω).differentiable (by simp) _
  apply h.unique; simpa only [zero_smul,add_zero] using! hp.hasFDerivAt.comp_hasDerivAt 0 he
lemma quench (K:Labels.Pol G) (v : Four R→G.Color): D (grad v) (p0 S x K)=0:=same (fun A=>by rw [awake_work,primary_gradient,map_zero,map_zero])

def pushing (v:G.Color) (M:GaugePanel G S.size):GaugePanel G S.size:=fun i=>G.ad v (M i)
-- Global inversion/color-invariant sector. Offset anchors can differ for arbitrary
-- product inputs. No need to set a gauge parameter to zero at any of those sites!
lemma unfold_color (g: G.El) (u : Snap G d) : expand d (snapColor g u) = colored g (expand d u):=by
  funext i; by_cases h:i<d-1 <;> simp only [expand,colored,h,↓reduceDIte, map_zero] ; rfl
lemma fight (v:G.Color) (M:GaugePanel G S.size) (K:Label G d): fderiv ℝ (awaken d K.val) (S.extract M) (S.extract (pushing S v M))=0:=by
  let L (t:ℝ) := rotates (G.lieExp (t • v)) M
  have he : L 0=M:=by funext i; simp [L,rotates]
  have ht : HasDerivAt (fun t:ℝ=> S.extract (L t)) (S.extract (pushing S v M)) 0 := S.extract.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.mpr fun i=> UVNext.FreeStress.adjoint_derivative ..)
  let F:=awaken d K.val
  have h : ∀ t:ℝ,F (S.extract (L t))= F (S.extract M):=by
    intro t; unfold F awaken L; rw [S.extract_color,unfold_color]; exact K.property.2 ..
  rw [← he]; have hh := ((show DifferentiableAt ℝ F (S.extract (L 0)) from (snap_read_smooth d K.val ω).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 ht)
  have hx : HasDerivAt (fun t:ℝ=> F (S.extract (L t))) 0 0:=by simp_rw [h]; exact hasDerivAt_const _ _
  rw [he,← he]; simpa only [he] using (hh.unique hx)

lemma pit_ward (K: Label G d) (A : LogLinks R G) (v : Four R → G.Color): pit A (D (grad v) (p1 S x K.val))= -pit A (D (rLink v A) (p0 S x K.val)):=by
  set a:=primary S x A; set L:=spectra S x A
  let f:= fderiv ℝ (awaken d K.val) a
  have h (t:ℝ): pit (A+t • grad v) (p1 S x K.val)=pit A (p1 S x K.val)- t • f (primary S x (rLink v A))- t^2 • f (primary S x (extra v)):=by
    have he : accent S x (A+t • grad v)= accent S x A - t • spectra S x (rLink v A)- t^2 • spectra S x (extra v) - t • pushing S (v x) L:=by
      funext i; rw [accent, second_gauge]; simp only [Pi.sub_apply,Pi.smul_apply, map_smul,map_neg,LinearMap.smul_apply, LinearMap.neg_apply,map_add]; unfold accent L pushing spectra; simp only [LinearMap.pi_apply]; abel
    rw [awake1,awake1,map_add,map_smul,primary_gradient]; simp only [secondary,map_add,map_smul,spectra_grad,he,map_sub,smul_zero, add_zero]
    have hh:= fight S (v x) (spectra S x A) K; simp only [f, a,L, hh,smul_zero,primary_at]; abel
  rw [awake_work]; have he:= directional A (grad v) (p1 S x K.val); simp_rw [h] at he
  let X:=f (primary S x (rLink v A)); let Y:= f (primary S x (extra v)); let Z:=pit A (p1 S x K.val)
  apply he.unique; exact (show HasDerivAt (fun t:ℝ=> Z-t • X - t^2 • Y) (-X) 0 from (by simpa only [one_smul,sub_zero,zero_sub,pow_one, Nat.reduceSub,zero_mul,mul_zero,zero_smul] using! ((hasDerivAt_const (0:ℝ) Z).sub ((hasDerivAt_id' (0:ℝ)).smul_const X) |>.sub (((hasDerivAt_id' (0:ℝ)).pow 2).smul_const Y))))

end YM.XSpace.Chart2
