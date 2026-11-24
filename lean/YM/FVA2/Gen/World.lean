import YM.FVA2.Gen.AnyT
/-!
 # Color-form smooth gauge covariance (continuum) at classical connection level

 Used for the R2 nonlinear jet comparison. Real parameters. Fixed `G.Color` and
 $d_0$ scaling as in `MS.Landau`. Plane-sign convention + and transforms A as
 $gAg^* - ∂g g^*$ (same as finite oriented Wilson links) with coupling =1 (unrescaled).
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Finset Set Filter Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision
variable {E F R : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedRing R][NormedAlgebra ℝ R] {f g:E4→F}
-- calculus convenience for partials (noncommutative)
def par (a:E)(f:E→F) (x:E): F:= fderiv ℝ f x a
section
variable {a b x:E}{f g:E→F}
theorem sway (hf:ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (par a f):=(hf.fderiv_right le_rfl).clm_apply contDiff_const
lemma par_sum (hf:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ g x): par a (f+g) x=par a f x+par a g x:= by rw [par,fderiv_add hf hg]; rfl
lemma par_sub (hf:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ g x): par a (f-g) x=par a f x-par a g x:= by rw [par,fderiv_sub hf hg]; rfl
lemma par_mul {f g:E→R}(hf:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ g x): par a (f*g) x= f x*par a g x+par a f x*g x:=by rw [ par,( hf.hasFDerivAt.mul' hg.hasFDerivAt ).fderiv ]; rfl
lemma par_swap (h:ContDiff ℝ ∞ f): par a (par b f) x=par b (par a f) x:=by
    have ht:= h.fderiv_right (m:=∞) le_rfl; let X:=fderiv ℝ f; have he(a b:E): par a (par b f) x=fderiv ℝ X x a b:= by let L:= ContinuousLinearMap.apply ℝ F b; change fderiv ℝ (L ∘ X) x a = _; rw [fderiv_comp _ L.differentiableAt (ht.differentiable (by simp) _), L.fderiv ]; rfl
    rw [he,he]; exact h.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast) _ _
lemma par_L {F':Type*}[NormedAddCommGroup F'][NormedSpace ℝ F'](L:F→L[ℝ]F')(h:DifferentiableAt ℝ f x): par a (L ∘ f) x= L (par a f x):= by rw [par,fderiv_comp x L.differentiableAt h,L.fderiv]; rfl
lemma par_line (h:Differentiable ℝ f)(v x:E)(t:ℝ): HasDerivAt (fun t:ℝ=> f (x+t • v)) (par v f ( x+t • v )) t:=
    ( h _ ).hasFDerivAt.comp_hasDerivAt t ( show HasDerivAt (fun t:ℝ=>x+t • v) v t by simpa using! ( ( hasDerivAt_id' t ).smul_const v ).const_add x )
end
variable {G:Gauge}
local notation "Cℓ"=>G.Color
local notation "M"=> G.Mat
local notation "Γ"=> G.colorMat
local notation "U"=> G.mat
local notation "T"=> E4
local notation "L"=>G.El
-- Color matrices convenient rail
abbrev Mist (G:Gauge):= E4→G.Color
abbrev Sky (G:Gauge):= Axis→ Mist G
local notation "C'"=> Mist G
local notation "P"=> Sky G
local notation "T'"=> E4→G.Mat
variable {A:Sky G}{u:E4→G.El}{x:E4}{v i j:Axis}
abbrev Lived (u:T→L) := ContDiff ℝ ∞ (U ∘ u)
abbrev Fluid (A:P) := ∀ i:Axis,ContDiff ℝ ∞ (A i)
local notation "l'"=> G.colorMat.toContinuousLinearMap
abbrev hat (G:Gauge) (g:Mist G) : E4→G.Mat:= G.colorMat ∘ g
local notation "δ"=> par
local notation "Y"=> hat G
-- actual derivatives use log and chart; realizes Lie projection
private lemma tangible (x b:T)(h:Lived u): δ b (U ∘ u) x * star (U (u x))∈ G.lie:=by
    let Q(t:T):= u t*(u x)⁻¹; let V(t:T):= U (Q t); have he:Lived Q:= show ContDiff ℝ ∞ _ from h.mul contDiff_const; let F:=G.plog ∘ V; have hv:V x=1:=by simp [V,Q]
    have ht: ContinuousAt Q x:= ( G.continuous_mat.isClosedEmbedding G.mat_injective ).isEmbedding.tendsto_nhds_iff.mpr he.continuous.continuousAt.tendsto; have hx:Tendsto Q (𝓝 x) (𝓝 1):= by simpa [ContinuousAt,Q,mul_inv_cancel] using ht
    have hp := hx.eventually G.plog_right; have hk: ContDiffAt ℝ ∞ F x:= ((show ContDiffAt ℝ ∞ G.plog (V x) from by rw [hv]; exact G.plog_diff.of_le le_top).comp x he.contDiffAt)
    have h₁:V=ᶠ[𝓝 x]( U ∘ G.lieExp ) ∘ F:= hp.mono (fun y hy=> congrArg U hy.symm)
    have h₀: F x=0:= by unfold F; rw [ comp_apply,hv,G.plog_one] -- unfold
    have hD: par b V x= Γ ( par b F x ):= by
       have hd : HasFDerivAt V (l' ∘L fderiv ℝ F x) x:=by refine HasFDerivAt.congr_of_eventuallyEq ?_ h₁; refine HasFDerivAt.comp x ?_ ( hk.differentiableAt (by simp)|>.hasFDerivAt ); rw [h₀]; exact G.expDiff_zero -- diamond
       exact DFunLike.congr_fun hd.fderiv b
    rw [ ← show par b V x=δ b (U ∘ u) x * star (U (u x)) from ?_,hD ]; apply G.colorMat_mem
    change par b (( U ∘ u ) * (fun _:T=> star (U (u x)))) x=_; rw [ par_mul ( h.differentiable (by simp ) _) (differentiableAt_const _) ]; simp [par]
lemma wiggle (h:Lived u): ContDiff ℝ ∞ (U ∘ (fun x:T=>(u x)⁻¹)):= ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap.contDiff.comp h )
-- right-multiplied relation
private lemma byR (g:G.El){A B:M}(h:A*U g=B*U g): A=B:= by rw [ ← mul_one A,← mul_one B, ← G.mat_mul_star g, ← mul_assoc, ← mul_assoc, h ]

def skyturn (u:T→ G.El)(A:P) : P:= fun i x=>G.projectColor ( (U (u x)* Γ (A i x) - δ (basis i) (U ∘ u) x) * star (U (u x)) )
def fantasy (u:T→ G.El)(f:C'): C':= fun x=> G.adjoint (u x) ( f x )
lemma skyline (h:Lived u): Y (skyturn u A i) x * U (u x)= U (u x) * Y (A i) x - δ (basis i) (U ∘ u) x:=by
    let g:= U (u x); let v:= Y ( A i ) x; let a:= δ (basis i) (U∘ u) x; change Γ (G.projectColor ((g*v-a)*star g)) * g=g*v-a; have hp:(g*v-a)*star g∈ G.lie:= by rw [sub_mul]; exact G.lie.sub_mem ( G.conjugate_mem _ ( G.colorMat_mem _ ) ) ( tangible x _ h )
    rw [ G.colorMat_project_self hp,mul_assoc,show star g*g=1 from G.mat_star_mul _,mul_one ] -- g def
lemma imagined (u:T→G.El)(f:C') : Y (fantasy u f) x = ( U (u x)* Y f x ) * star (U (u x)):=G.mat_adjoint ..
lemma skyline_sm (h:Lived u)(hp:Fluid A): Fluid (skyturn u A):=fun i=> G.projectColor.toContinuousLinearMap.contDiff.comp ( (h.mul ( (l').contDiff.comp ( hp i ) )|>.sub ( sway h ) ).mul ( wiggle h ) )
lemma imagineC (h:Lived u){f:C'}(hp:ContDiff ℝ ∞ f): ContDiff ℝ ∞ ( fantasy u f ):=by refine G.projectColor.toContinuousLinearMap.contDiff.comp ((h.mul ((l').contDiff.comp hp)).mul ( wiggle h ) ) -- defeq project? 
lemma umbrella (u:T→ L)(f:C'): Y (fantasy u f) x * U (u x)= U (u x) * Y f x:=by rw [ imagined, mul_assoc ( _ *_ ),G.mat_star_mul,mul_one ]
def deriveN (A:P)(f:C')(i:Axis)(x:T): Cℓ:= δ (basis i) f x + G.ad ( A i x ) (f x)
def surf (A:P)(i j:Axis)(x:T): Cℓ:= deriveN A ( A j ) i x - δ (basis j) (A i) x
lemma cDer {f:C'}(h:Fluid A)(hp:ContDiff ℝ ∞ f)(i:Axis): ContDiff ℝ ∞ (deriveN A f i):= by
    -- clm nested
    let X:Cℓ→L[ℝ]Cℓ→L[ℝ]Cℓ:= LinearMap.toContinuousLinearMap ( LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad )
    exact (sway hp).add ( ( (X.contDiff.comp (h i)).clm_apply hp ) )
lemma cSurf (h:Fluid A)(i j:Axis): ContDiff ℝ ∞ (surf A i j):= ( cDer h (h j) i ).sub (sway (h i))
lemma matPar {f:C'}{b:T}(h:ContDiff ℝ ∞ f): Y (δ b f) x = δ b (Y f) x:= ( par_L l' (h.differentiable (by simp) x)).symm
lemma matD {f:C'} (hf:ContDiff ℝ ∞ f): Y (deriveN A f i) x=δ (basis i) (Y f) x + ( Y (A i) x * Y f x - Y f x * Y ( A i ) x ):= by unfold hat deriveN; dsimp only [Function.comp_apply]; rw [map_add,G.colorMat_ad]; congr 1; exact matPar hf
lemma matS (h:Fluid A): Y (surf A i j) x= δ (basis i) (Y (A j)) x- δ (basis j) ( Y (A i)) x+( Y (A i) x*Y (A j) x-Y (A j) x*Y (A i) x ):= by
    change Γ ( _-_)=_; rw [map_sub,show Γ (deriveN A (A j) i x)=_ from matD ( h j ) , show Γ (par (basis j) (A i) x)=_ from matPar ( h i ) ]; abel
end YM.FVA2.Gen
