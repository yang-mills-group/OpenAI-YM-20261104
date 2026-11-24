import YM.X.Rank.Shore
/-!
Limits of the tangible skew tangents. Not assuming a closed-subgroup theorem for
all internal symmetries. `Drop` uses *any* real direction with near-identity rays.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Maxwell Wick Maxwell.Free
open Screen Next.Rank.Normal MvPolynomial NormedSpace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius RealInnerProductSpace ContDiff
variable {G : Gauge} {P : Mat G} {I Y: Type*} {Q : WickPol G} (q:I→ WickPol G)(h:G.Simple)
abbrev snap (p:WickPol G)(X:Mat G)(A:Sample G):ℂ:= helps (coatV X A) p
def Keeps (X:Mat G) := ∀ i:I,∀ u : G.El,∀ A:Sample G,snap (q i) X (coatV (Sk u) A)=snap (q i) X A
def Same (X Y:Mat G) := ∀ i:I,∀ A:Sample G,snap (q i) X A=snap (q i) Y A
abbrev Drop {E : Type*}[NormedAddCommGroup E] [NormedSpace ℝ E](x: E)(X : Y→ E)(i:Y):= ‖X i-x‖⁻¹ • (X i-x)
abbrev vel (p:WickPol G)(A:Sample G):= fderiv ℝ (fun (Q:Mat G)=> snap p Q A) 1
variable {s:Filter Y}
lemma motion {E F Y:Type*}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F] (f:E→F){s:Filter Y}{x m:E} {X:Y→E} (hx:DifferentiableAt ℝ f x)(ht:Tendsto X s (𝓝 x))(he:Tendsto (Drop x X) s (𝓝 m)) :
    Tendsto (fun t=> ‖X t-x‖⁻¹ • (f (X t)-f x)) s (𝓝 (fderiv ℝ f x m)) := by
  let g:=fderiv ℝ f x; have h:= (hasFDerivAt_iff_tendsto.mp hx.hasFDerivAt).comp ht; let p t:= ‖X t-x‖⁻¹ • (f (X t)-f x-g (X t-x))
  have hT : Tendsto p s (𝓝 0) := by rw [tendsto_zero_iff_norm_tendsto_zero]; simpa only [p,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),Function.comp_def] using h
  have hh := hT.add (g.continuous.continuousAt.tendsto.comp he); rw [zero_add] at hh; refine hh.congr (fun t=> ?_); dsimp only [p,Function.comp_apply]; rw [Drop,map_smul,← smul_add,sub_add_cancel]

private lemma conj_deriv (Q:WickPol G)(X:Mat G)(hp:Painted Q)(u:G.El)(A:Sample G) : vel Q (coatV (Sk u) A) X=vel Q A (adjX X u) := by
  let v:= coatV (Sk u) A; let f(t:Mat G):= snap Q (adjX t u) A
  let g(t:Mat G):= snap Q t v
  have H (w:Sample G): helps (coatV (Sk u).transpose w) Q=helps w Q:= by
    let W:=coatV (Sk u).transpose w; rw [← hp u, helps_invariant, hp u] -- edit
    rw [← Sk_ap, coat_mul, show Sk u*(Sk u).transpose=1 from mul_eq_one_comm.mpr (Sk_member u),coat_one]
  have hf: f=g:= by funext t; unfold f g snap adjX; rw [Matrix.mul_assoc, ← coat_mul,H,← coat_mul]
  let z(t:ℝ):Mat G:= 1+t • X; let k:=adjX X u
  have hm t: adjX (z t) u=1+t • k:=by unfold z adjX k; simp [add_mul,mul_add,show (Sk u).transpose * Sk u=1 from Sk_member u]; rfl
  have hh (A:Sample G)(X:Mat G) : HasDerivAt (fun t:ℝ=> snap Q (1+t • X) A) (vel Q A X) 0:=by
    let x(t:ℝ):=1+t • X
    have hz:HasDerivAt x X 0:= by unfold x; simpa only [one_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const X).const_add (1:Mat G)
    have he:x 0=1:=by simp [x]
    exact (show HasFDerivAt (fun X=>snap Q X A) (vel Q A) (x 0) from he.symm ▸ ((regularity A Q).differentiable (by simp) (1:Mat G)).hasFDerivAt).comp_hasDerivAt 0 hz
  apply (hh v X).unique
  change HasDerivAt (fun t:ℝ=>g (z t)) _ _; rw [← hf]; unfold f; simp_rw [hm]; exact hh A k

variable (hp:∀ i,Painted (q i)) {X : Y→Mat G}(hx:Tendsto X s (𝓝 1))(hT:Tendsto (Drop 1 X) s (𝓝 P))
include hx hT
lemma tiltO [s.NeBot](he:∀ᶠ i in s,X i∈ O G): P.transpose= -P:= by
    let v i:=‖X i-(1:Mat G)‖; let z:= Drop 1 X
    have ht : Tendsto v s (𝓝 0):= by simpa using! (hx.sub (tendsto_const_nhds (x:=(1:Mat G)))|>.norm)
    have hv:Tendsto (fun i=>(z i).transpose) s (𝓝 P.transpose) := (Continuous.matrix_transpose (A:=(id:Mat G →Mat G)) continuous_id).continuousAt.tendsto.comp hT
    have h:= hT.add hv|>.add (ht.smul (hv.mul hT))
    have he' : P+P.transpose=0:= by
      apply tendsto_nhds_unique  (by rw [zero_smul,add_zero] at h; exact h)
            (tendsto_const_nhds.congr' ?_)
      filter_upwards [he] with i hi
      change 0=z i + (z i).transpose+ v i • ((z i).transpose*z i)
      have hu: X i=1+v i • z i:=by
        unfold z Drop v; by_cases ht:X i=1
        · simp [ht]
        rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ht)),one_smul]; abel
      change (X i).transpose* (X i)=1 at hi; by_cases h:X i=1
      · simp [z,v,Drop,h]
      let a:=v i; let b:=z i; have ha:0<a:=norm_pos_iff.mpr (sub_ne_zero.mpr h)
      rw [hu] at hi; simp only [transpose_add,transpose_one,transpose_smul,add_mul,mul_add,one_mul,mul_one,mul_smul_comm,smul_mul_assoc] at hi
      apply smul_right_injective (Mat G) ha.ne'; dsimp only; change v i • (0:Mat G)=_; erw [smul_zero]; change 0 = v i • _; rw [add_assoc, ← smul_add] at hi; exact (add_left_cancel (a:=(1:Mat G)) (by rw [add_zero]; convert hi.symm using 3; abel))
    rw [add_comm] at he'; exact eq_neg_of_add_eq_zero_left he'
include hp h
lemma still [s.NeBot](he:∀ᶠ i in s,X i∈ O G ∧ Keeps q (X i)) (i : I) (A:Sample G): vel (q i) A P=0:= by
    let p:= q i; let L:= vel p A; have ht (A:Sample G):= motion (fun Q=>snap (q i) Q A) ((regularity A p).differentiable (by simp) _) hx hT
    have hv (u:G.El): L (adjX P u)= L P:= by
      rw [← conj_deriv p P (hp i)]; apply tendsto_nhds_unique (ht _) ((ht A).congr' ?_)
      filter_upwards [he] with i' hi; rw [hi.2 i u A]; congr 2; rw [snap,snap,coat_one,coat_one,Sk_ap,← helps_invariant,hp i] -- orientation
    have hl:= L.integral_comp_comm (adjFin (adjX P) (adjX_cont _)); rw [Sk_mean h (tiltO hx hT (he.mono fun i h=>h.1)),map_zero] at hl -- orientation
    change L P=0; rw [← hl]
    exact (show L P= ∫ _:G.El,L P ∂G.probHaar from by simp).trans (integral_congr_ae (Eventually.of_forall fun x=> (hv x).symm))
end YM.PositionX.Rank
