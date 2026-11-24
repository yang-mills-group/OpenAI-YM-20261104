import YM.FVA2.Orbit.Screen
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
/-!
# A nonlinear gauge change from Landau to arbitrary rooted complementary gauge
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit.Screen
open Function Set Filter Finset Topology Lattice LocalH
open scoped ContDiff Topology Classical BigOperators Matrix
variable {G:Gauge} {n:Side}
set_option linter.unusedSectionVars false -- require both FD gauges for changes here
variable (E F:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
local notation "R" => Root G n
local notation "θ" => R × E
local notation "η" => R × F
variable {E F} (s:Screen G n E)(u:Screen G n F)
lemma strict : HasStrictFDerivAt s.tilt s.hurdle.toContinuousLinearMap 0:= by rw [hurdle_eq]; exact s.smooth.hasStrictFDerivAt (by simp)
local instance cFS : CompleteSpace θ:= FiniteDimensional.complete ℝ _
def ancestry : Rep G n → Root G n × E := s.strict.localInverse s.tilt s.hurdle 0
lemma ancestry_germ : ContDiffAt ℝ ω s.ancestry 0:= by
 have he:= s.smooth.to_localInverse (f':=s.hurdle) s.strict.hasFDerivAt (by simp); rw [s.resting] at he; exact he
lemma ancestry_zero : s.ancestry 0=0:= by nth_rw 1 [← s.resting]; exact s.strict.localInverse_apply_image
lemma emerging : s.tilt ∘ s.ancestry =ᶠ[𝓝 0] id := by have he := HasStrictFDerivAt.eventually_right_inverse (f':=s.hurdle) (s.strict); rw [s.resting] at he; exact he

def ψ (x:E) : Root G n × F:= u.ancestry (s.σ x)
def Δ : E→Root G n:= Prod.fst ∘ s.ψ u
def reform : E→F:= Prod.snd ∘ s.ψ u
lemma psi_analytic : ContDiffAt ℝ ω (s.ψ u) 0:= (s.origin.symm ▸ u.ancestry_germ : ContDiffAt ℝ ω u.ancestry (s.σ 0)).comp (f:=s.σ) 0 s.germ
@[simp] lemma Δ_zero : s.Δ u 0=0:= by rw [Δ,comp_apply, ψ,s.origin,u.ancestry_zero]; rfl
@[simp] lemma reform_zero : s.reform u 0=0:= by rw [reform,comp_apply, ψ,s.origin,u.ancestry_zero]; rfl
lemma Δ_hot : ContDiffAt ℝ ω (s.Δ u) 0 := (s.psi_analytic u).fst
lemma reform_hot : ContDiffAt ℝ ω (s.reform u) 0:=(s.psi_analytic u).snd
/-- The exact gauge change holds eventually. -/
lemma gauge_change : ∀ᶠ x:E in 𝓝 0,s.σ x = angle (s.Δ u x) (u.σ (s.reform u x)):= EventuallyEq.symm (s.σ_tends.eventually u.emerging : u.tilt ∘ s.ψ u =ᶠ[𝓝 0] s.σ)

def trans (x:Root G n × E): Root G n × F:= (circle (s.Δ u x.2) x.1,s.reform u x.2)
@[simp] lemma trans0 : s.trans u 0=0:= by simp [trans]
lemma trans_hot : ContDiffAt ℝ ω (s.trans u) 0:= by
    let f:=fun x:θ => (s.Δ u x.2,x.1); have h:f 0=0:= by simp [f]
    exact ( (h.symm ▸ join_germ : ContDiffAt ℝ ω (uncurry circle) (f 0)).comp (f:=f) 0 (((s.Δ_hot u).comp (f:=(@Prod.snd R E)) 0 contDiffAt_snd : ContDiffAt ℝ ω (s.Δ u ∘ (@Prod.snd R E)) 0).prodMk contDiffAt_fst)).prodMk (show ContDiffAt ℝ ω (s.reform u ∘ (@Prod.snd R E)) 0 from (s.reform_hot u).comp (f:=Prod.snd) 0 contDiffAt_snd)
lemma trans_eq : s.tilt =ᶠ[𝓝 0] u.tilt ∘ s.trans u:= by
    have h:= continuous_fst.tendsto (0:θ); have k:= continuous_snd.tendsto (0:θ); have hu:= aimed (s.Δ_hot u).continuousAt (s.Δ_zero u); have hv:= u.σ_tends.comp (aimed (s.reform_hot u).continuousAt (s.reform_zero u))
    filter_upwards [k.eventually (s.gauge_change u), (tup (hu.comp k) (tup h (hv.comp k))).eventually group_joins] with x hx hv
    change angle x.1 (s.σ x.2)=_; rw [hx]; exact hv.symm
lemma trans_jac : ∀ᶠ x in 𝓝 0, fderiv ℝ s.tilt x= fderiv ℝ u.tilt (s.trans u x) ∘L fderiv ℝ (s.trans u) x:= by
    filter_upwards [(s.trans_eq u).eventuallyEq_nhds,(s.trans_hot u).eventually (by simp), (aimed (s.trans_hot u).continuousAt (s.trans0 u)).eventually (u.smooth.eventually (by simp))] with x hx hv h
    rw [hx.fderiv_eq]; exact fderiv_comp x (h.differentiableAt (by simp)) (hv.differentiableAt (by simp))
def leanE : θ≃L[ℝ]η := s.hurdle.trans u.hurdle.symm  -- notation check
lemma leanE_eq : (s.leanE u).toContinuousLinearMap=fderiv ℝ (s.trans u) 0:= by
 let A:=fderiv ℝ s.tilt 0; let B:=fderiv ℝ u.tilt 0; have h : A=B ∘L fderiv ℝ (s.trans u) 0:= by simpa only [trans0] using (s.trans_jac u).self_of_nhds
 apply ContinuousLinearMap.ext; intro x; change u.hurdle.symm (A x)=_
 rw [h,ContinuousLinearMap.comp_apply]; exact u.hurdle.symm_apply_apply _

-- reform free tangent invertible follows from block upper
local notation "V" => s.trans u
local notation "Λ" => fderiv ℝ (s.reform u)
private def rate (x:θ) := fderiv ℝ (circle (s.Δ u x.2)) x.1
private lemma stair : ∀ᶠ x : θ in 𝓝 0, (∀ z:R,fderiv ℝ V x (z,0)=(s.rate u x z,0)) ∧ ∀ y:E,(fderiv ℝ V x (0,y)).2=Λ x.2 y:= by
    have h:= continuous_fst.tendsto (0:θ); have k:= continuous_snd.tendsto (0:θ); have u':= aimed (s.Δ_hot u).continuousAt (s.Δ_zero u)
    filter_upwards [(s.trans_hot u).eventually (by simp),(tup (u'.comp k) h).eventually diff_circle,k.eventually ((s.reform_hot u).eventually (by simp))] with q ha hh hψ
    rcases q with ⟨x,y⟩; let v: η→L[ℝ] F:= ContinuousLinearMap.snd ℝ _ _; let f:=s.reform u; let L:=fun z:R=>circle (s.Δ u y) z; let K:=fderiv ℝ L x; let p:θ:=(x,y); have ht: HasFDerivAt L K x:= (show DifferentiableAt ℝ L x from hh.1).hasFDerivAt; have hb: DifferentiableAt ℝ V (x,y):= ha.differentiableAt (by simp)
    constructor
    · intro z; have he:= (pri hb).trans (show _ = K.prod (0:R→L[ℝ]F) from (ht.prodMk (f₂:=fun _:R=> f y) (hasFDerivAt_const ..)).fderiv); exact DFunLike.congr_fun he z
    intro z; have hs := hb.hasFDerivAt.snd; have hv : f ∘ Prod.snd= v ∘ V := rfl; have he : HasFDerivAt (v ∘ V) _ p:= hs; have hp : DifferentiableAt ℝ f y:= hψ.differentiableAt (by simp)
    rw [← hv] at he; exact DFunLike.congr_fun (he.unique (hp.hasFDerivAt.comp (x,y) hasFDerivAt_snd)) (0,z)
lemma pos_head : s.rate u 0=ContinuousLinearMap.id ℝ R:= by
    rw [rate,Prod.snd_zero,Δ_zero,Prod.fst_zero]; exact ((hasFDerivAt_id (𝕜:=ℝ) (0:R)).congr_of_eventuallyEq left_turn).fderiv
private lemma rank : Bijective (Λ 0) := by
    let L:=s.leanE u; let K:=Λ 0; have q:= (s.stair u).self_of_nhds; rw [←leanE_eq, pos_head] at q; have h (z:R) : L (z,0)=(z,0):= q.1 z; have hh (z:R)(x:E) : (L (z,x)).2=K x:= by
       calc
         _ = (L ((z,0)+(0,x))).2 := by simp only [Prod.mk_add_mk, add_zero,zero_add]
         _ = _:= by rw [map_add,h, Prod.snd_add, show (L (0,x)).2=K x from q.2 x]; simp
    refine ⟨show Injective (Λ 0).toLinearMap from LinearMap.ker_eq_bot.mp (bot_unique ?_), fun x=> ?_⟩
    · intro i hi; let z:= (L (0,i)).1; have ht : L (0,i)=(z,0):= Prod.ext rfl ((hh 0 i).trans ((LinearMap.mem_ker.mp hi) : K i=0)); exact congr_arg Prod.snd (L.injective (ht.trans (h z).symm))
    obtain ⟨⟨z,y⟩,hy⟩:= L.surjective (0,x); exact ⟨y,(hh z y).symm.trans (congr_arg Prod.snd hy)⟩
def rework : E≃L[ℝ] F:= (LinearEquiv.ofBijective (Λ 0).toLinearMap (s.rank u)).toContinuousLinearEquiv
lemma rework_eq : (s.rework u).toContinuousLinearMap=Λ 0:= rfl
lemma meter_change : ∀ᶠ x:E in 𝓝 0,s.weight x=u.weight (s.reform u x) * meter (s.rework u) (Λ x):= by
    let l:=𝓝 (0:E); let T:= u.hurdle; let L:= s.hurdle; let θ':=s.reform u; let Q:=s.leanE u; let f:=s.trans u; let K: θ≃L[ℝ] η := (ContinuousLinearEquiv.refl ℝ R).prodCongr (s.rework u)
    have hk : ∀ᶠ x:θ in 𝓝 0,meter K (fderiv ℝ f x)= (s.rate u x).det * meter (s.rework u) (Λ x.2) := by
      filter_upwards [s.stair u] with x hx; unfold meter; apply upper; intro p
      · change fderiv ℝ f x (p,(s.rework u).symm 0)=_; rw [map_zero]; exact hx.1 p
      intro y; exact hx.2 _
    have hQ : meter K Q.toContinuousLinearMap=1 := by
      have he := hk.self_of_nhds; rw [show (0:θ).2=(0:E) from rfl, ←show (s.rework u).toContinuousLinearMap=(Λ 0) from rfl, meter_self,pos_head] at he; exact (leanE_eq s u ▸ (he.trans (by rw [show (ContinuousLinearMap.id ℝ R).det=1 from map_one LinearMap.det, one_mul])) : meter K Q.toContinuousLinearMap=1)
    have hv : Tendsto (s.ψ u) l (𝓝 0):= tup (aimed (s.Δ_hot u).continuousAt (s.Δ_zero u)) (aimed (s.reform_hot u).continuousAt (s.reform_zero u))
    let A : θ→L[ℝ] η := K.toContinuousLinearMap; let p:=fun x:E=> ((0:R),x); have hp:Tendsto p l (𝓝 0):= tup tendsto_const_nhds tendsto_id
    filter_upwards [hp.eventually hk,hp.eventually (s.trans_eq u),hp.eventually (s.trans_jac u), hv.eventually u.orbit_density, (aimed (s.Δ_hot u).continuousAt (s.Δ_zero u)).eventually (right_turn.and gate_left), s.stop] with x hx he hJ hψ hu hs
    let w:=s.rate u (p x); let z:=s.ψ u x; let X:=s.σ x; let o:=p x; have hz:f o=z:= Prod.ext hu.1 rfl; let M:= fderiv ℝ f (p x); let d:=meter (s.rework u) (Λ x)
    have he:s.tilt o=u.tilt z:= he.trans (congr_arg u.tilt hz)
    have he': X=u.tilt z:= hs.symm.trans he
    have hj : fderiv ℝ s.tilt o= fderiv ℝ u.tilt z ∘L M:= by rw [←hz]; exact hJ
    have hT: Q.trans T=L:= ContinuousLinearEquiv.ext (funext fun x=> T.apply_symm_apply (L x))
    have hu': hair z.1 * w.det=1:= hu.2
    have hm : meter K M = meter Q M:= by
       calc
          _ = ((M ∘L Q.symm.toContinuousLinearMap) ∘L Q.toContinuousLinearMap ∘L K.symm.toContinuousLinearMap).det := congr_arg (ContinuousLinearMap.det ·) (ContinuousLinearMap.ext (fun x=> (congr_arg M (Q.symm_apply_apply (K.symm x))).symm))
          _ = _:= by rw [Orbit.det_comp, show (Q.toContinuousLinearMap ∘L K.symm.toContinuousLinearMap).det=1 from hQ, mul_one]; rfl
    have hR : s.relative o=u.relative z * (w.det*d):= by
      unfold relative; rw [hj,← show Q.trans T=s.hurdle from hT, transverse_cost];rw [←hm,show meter K M=w.det*d from hx]
    change hair X * s.relative o=_
    calc
      _ = (hair (u.tilt z)*u.relative z)*(w.det*d):=by rw [hR,he',mul_assoc]
      _ = _:= by
        rw [show hair (u.tilt z)*u.relative z=hair z.1 * u.weight (s.reform u x) from hψ]; rw [mul_comm (hair z.1),mul_assoc,←mul_assoc (hair z.1),hu',one_mul]

end YM.FVA2.Orbit.Screen
