import YM.Primitives.HAAR_LOG_JETS.Symmetry
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Link logarithm fields

Act on the right by `(s,t)` gauge parameters (near local units after
 conjugation as needed). Keep eventually statements; no global dexp formula
 assumed on the chart. Applies to the actual compact representation. These
 proofs are about exact real fields of Taylor germs independent of cutoff size.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare.Maurer
open Function Set Filter Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}
variable (G)
abbrev C := G.Color
abbrev Ends := C G × C G
def lie (a:C G): G.Mat:= G.mat (G.lieExp a)
variable {G}
local notation "E" => lie G
variable (x y : Ends G)
-- linear on gauge links; coat from lift of actual left-right Lie march.
def mx (x:Ends G) : G.Mat →ₗ[ℝ] G.Mat where
   toFun S:= S*G.colorMat x.2 - G.colorMat x.1*S
   map_add' S T:= by simp [mul_add,add_mul]; abel
   map_smul' t S:= by simp [smul_sub]
def box (a:C G): Ends G→ₗ[ℝ] G.Mat where
   toFun x:= mx x (E a)
   map_add' x y := by simp [mx,mul_add,add_mul]; abel
   map_smul' t x:= by simp [mx,smul_sub]
def voltage (a:C G): Ends G→ₗ[ℝ] C G:= (fderiv ℝ G.plog (E a)).toLinearMap.comp (box a)
def volts (x:Ends G) (a:C G):= voltage a x

section
variable {U:Set G.El}{s:Set (C G)}(H:LocalH.Geom G U s)
include H
variable {x}
lemma snap_on {a:C G}(h:a∈s): G.plog (E a)=a:= H.2.2.1 h
lemma analytic_here {a:C G}(h:a∈s): ContDiffAt ℝ ω G.plog (E a):= H.2.2.2.2.2.2 _ (H.2.2.2.2.2.1 h)
-- inverse derivative formulas
lemma ambient {a:C G}(h:a∈s)(v:C G) : fderiv ℝ G.plog (E a) (fderiv ℝ E a v)=v:=by
    let A := fderiv ℝ G.plog (E a); let V := fderiv ℝ E a
    have hA : HasFDerivAt (G.plog ∘ E) (A ∘L V) a:= ((analytic_here H h).differentiableAt (by simp)).hasFDerivAt.comp a ((G.exp_jet.differentiable (by simp) a).hasFDerivAt)
    have ht := hA.congr_of_eventuallyEq (f₁:=id) (Eventually.mono (H.2.1.mem_nhds h) (fun x hx=> (snap_on H hx).symm))
    have hh := ht.unique (hasFDerivAt_id _); change (A ∘L V) v=v; rw [hh]; rfl
lemma identifies {a:C G}(h:a∈s): Injective (fderiv ℝ E a):= Function.LeftInverse.injective (ambient H h)
end

def step (x:Ends G)(a:C G)(t:ℝ): G.El:= G.lieExp (-(t • x.1))* G.lieExp a * G.lieExp (t • x.2)
@[simp] lemma step_start (a:C G): step x a 0=G.lieExp a:= by simp [step]
lemma colorDerivative (x:C G) : HasDerivAt (fun t:ℝ=>E (t • x)) (G.colorMat x) 0:= by
    have he : HasDerivAt (fun t:ℝ=> t • x) x 0:= by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
    exact HasFDerivAt.comp_hasDerivAt_of_eq (f:=fun t:ℝ=>t • x) (l:= E) 0 G.expDiff_zero he (by simp) -- check
lemma step_tan (a:C G) : HasDerivAt (fun t:ℝ=> G.mat (step x a t)) (mx x (E a)) 0:= by
    have he := ((colorDerivative (-x.1)).mul_const (E a)).mul (colorDerivative x.2)
    simp_rw [smul_neg] at he
    convert! he using 1
    simp [lie,mx,sub_eq_add_neg,add_comm]
section
variable {U:Set G.El}{s:Set (C G)}(H:LocalH.Geom G U s){a:C G}
include H
lemma amp (h:a∈s) : HasDerivAt (fun t:ℝ=> G.plog (G.mat (step x a t))) (volts x a) 0 := by
    have hh : ContDiffAt ℝ ω G.plog (G.mat (step x a 0)):= by rw [step_start]; exact analytic_here H h
    convert! ((hh.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 (step_tan x a)) using 1
    unfold volts voltage; simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,step_start]; rfl
lemma walk_on (h:a∈s): ∀ᶠ t in 𝓝 0, step x a t∈U:= by
    have he : Continuous (step x a):= Continuous.mul ((Continuous.mul (G.lieExp_cont.comp (continuous_id.smul continuous_const|>.neg)) continuous_const)) (G.lieExp_cont.comp (continuous_id.smul continuous_const))
    exact (he.tendsto 0).eventually (H.1.mem_nhds (by rw [step_start]; exact H.2.2.2.2.2.1 h))
lemma voltf (h:a∈s): fderiv ℝ E a (volts x a)=mx x (E a):= by
    let F (t:ℝ):= G.plog (G.mat (step x a t)); have he : F 0=a:= by rw [show F 0=G.plog (E a) by rw [show F 0=G.plog (G.mat (step x a 0)) from rfl,step_start]; rfl]; exact snap_on H h
    have hh := (G.exp_jet.differentiable (by simp) (F 0)).hasFDerivAt.comp_hasDerivAt (f:=F) 0 (amp x H h)
    have hp : HasDerivAt (fun t=> G.mat (step x a t)) (fderiv ℝ E a (volts x a)) 0 := by
        rw [he] at hh; refine hh.congr_of_eventuallyEq ?_
        filter_upwards [walk_on x H h] with t hx; exact congr_arg G.mat (H.2.2.2.1 hx).symm
    exact hp.unique (step_tan x a)
lemma analytic_volts (h:a∈s) : ContDiffAt ℝ ω (volts x) a:= by
    have hA:= (analytic_here H h).fderiv_right (m:=ω) (by simp); have ht : ContDiffAt ℝ ω E a:= G.exp_jet.contDiffAt; exact (hA.comp a ht).clm_apply ((mx x).toContinuousLinearMap.contDiff.contDiffAt.comp a ht)
end
lemma home : ContDiffAt ℝ ω (volts x) 0:= by obtain ⟨s,hs,h⟩:= LocalH.geom_patch G; exact analytic_volts x (h s (le_refl s)) (mem_ball_self hs)
lemma volt_zero : volts x 0=x.2-x.1:= by
    obtain ⟨s,hs,h⟩:=LocalH.geom_patch G; apply identifies (h s (le_refl s)) (mem_ball_self hs); rw [voltf x (h s (le_refl s)) (mem_ball_self hs)]; rw [show fderiv ℝ E 0= G.colorMat.toContinuousLinearMap from G.expDiff_zero.fderiv]; simp [mx,lie]
/-! stable commutator of germ vector. -/
def braid (x y:Ends G): Ends G:= (G.ad x.1 y.1,G.ad x.2 y.2)
lemma stemp (a:G.Mat): mx y (mx x a)-mx x (mx y a)=mx (braid x y) a:= by dsimp only [mx,braid,LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [G.colorMat_ad]; noncomm_ring
section
variable {U:Set G.El}{s:Set (C G)}(H:LocalH.Geom G U s){a:C G}(h:a∈s)
include H h
lemma wind_tan (v:C G): fderiv ℝ E a ((fderiv ℝ (volts x) a) v)+ (fderiv ℝ (fderiv ℝ E) a) v (volts x a)=mx x (fderiv ℝ E a v):= by
    have he : DifferentiableAt ℝ (fderiv ℝ E) a:= ((G.exp_jet.contDiffAt (x:=a)).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp); have hv: DifferentiableAt ℝ (volts x) a:= (analytic_volts x H h).differentiableAt (by simp)
    let V := fderiv ℝ E; have hh := ((mx x).toContinuousLinearMap.hasFDerivAt.comp a (G.exp_jet.differentiable (by simp) a).hasFDerivAt)
    have h' : (mx x ∘ E) =ᶠ[𝓝 a] fun z=> V z (volts x z):= Eventually.mono (H.2.1.mem_nhds h) (fun z hz=> (voltf x H hz).symm)
    have hp := ((he.hasFDerivAt.clm_apply hv.hasFDerivAt).congr_of_eventuallyEq h').unique hh
    exact DFunLike.congr_fun hp v
lemma storm : fderiv ℝ (volts y) a (volts x a)-fderiv ℝ (volts x) a (volts y a)=volts (braid x y) a:= by
    apply identifies H h; rw [map_sub,voltf (braid x y) H h,← stemp]
    have he := wind_tan x H h (volts y a); have hh:=wind_tan y H h (volts x a); have hu:IsSymmSndFDerivAt ℝ E a:= G.exp_jet.contDiffAt (x:=a)|>.isSymmSndFDerivAt_of_omega
    rw [voltf x H h] at hh; rw [voltf y H h] at he; rw [← he,← hh, show fderiv ℝ (fderiv ℝ E) a (volts y a) (volts x a)=_ from hu (volts y a) (volts x a)]; exact (add_sub_add_right_eq_sub ..).symm
end
end YM.MS.Bare.Maurer
