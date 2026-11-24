import YM.FVA2.MixedStory
import YM.FVA2.Pinned
/-!
# View into the Bank. Endμ one-dimensional PS product
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Attend
open Filter Topology Set Function Complex
open MS MS.Koszul MS.Landau MS.Plane MS.Lifting MS.Book MS.Book.Program MS.Book.Convolve MS.Theater
open MS.Puff MS.Puff.Engine MS.Puff.Mom MS.Puff.SplitP MS.Puff.Actors
open MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Swirl MS.Logarithm MS.Plane.Flux
open FormalOPE.RG10.InversionTop PowerSeries
open Clock Based PairCoords Modes Paper Score
open scoped Topology Classical ContDiff
variable {A:Type} [Fintype A]{X:Cn}{p: Sector A} (M: Grain A) (V:Price p){v:ℝ}
-- split of constant term
lemma stre (s:T ℂ): Clock.out (mk s)=s:= funext fun _=> coeff_mk ..
lemma reserve : Injective Clock.out:= fun _ _ h=> PowerSeries.ext fun i=> congr_fun h i

def raiseW : T ℂ →ₗ[ℂ] Cn:= LinearEquiv.ofBijective Clock.out ⟨ reserve, fun s=>⟨_,stre s⟩ ⟩|>.symm.toLinearMap
lemma raised (s:T ℂ): raiseW s=PowerSeries.mk s:= by unfold raiseW; apply reserve; exact (LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective Clock.out ⟨ reserve, fun s=>⟨_,stre s⟩ ⟩) s).trans (Eq.symm (stre _)) -- placeholders proof
lemma saving (t:T ℂ): Clock.out (raiseW t)=t:= by rw [raised,stre]
 -- inference aliases init proofs
local notation "Tt"=> Paper.track p
-- quote.Diag.Built on trajectory with Rooted
variable (h: Paper.track p V 0=0)

def chartV (u:Price p) := (raiseW (ℶV M ( exp0 p ( Paper.track p V ))))⁻¹ * raiseW (ℶV M ( Paper.track p (Paper.exp V*u))) -- inverse precedence corrected?
include h
lemma bought (v:Price p) : Endμ M p (track p V) (track p v) (out (chartV M V v)) := by
   unfold Endμ chartV; rw [← exp_tracks,pair, exp_tracks V ]; -- heuristic
   let x:= exp0 p (track p V); let K := ℶV M x; let y: T ℂ:= ℶV M ((PermV p).core x (track p v)); let W:= raiseW K; let Z:= raiseW y; change y=Trunk.core K (out (W⁻¹ * Z)); have hk:W*W⁻¹=1:= PowerSeries.mul_inv_cancel W (show constantCoeff W≠0 by rw [ ← coeff_zero_eq_constantCoeff_apply, ← out_coeff, show out W= _ from saving K, show K 0=1 from yetB h ]; exact one_ne_zero); change y=Trunk.core K (out (W⁻¹ * Z)); nth_rw 1 [show K=out W from (saving K).symm]; rw [ ← out_prod,← mul_assoc,hk,one_mul,saving ] -- maybe let
   

def guide : Price p→ₗ[ℂ] Cn where
   toFun:= chartV M V
   map_smul' z x := by simp only [chartV, mul_smul_comm, map_smul,RingHom.id_apply] -- rew `[chartV]` inverse syntax
   map_add' a b:= by simp only [chartV,mul_add, map_add]
lemma guides (z: T ℂ){v:Price p}(hv:Endμ M p (track p V) (track p v) z): Clock.out (guide M V v)= z:= classicalμ h ( bought M V h v ) hv
lemma funding (v:Price p)(z:Cn): guide M V (currency p z*v)= z*guide M V v:= by apply reserve; rw [out_prod]; apply guides M V h; apply Clock.end_scalar; exact bought M V h v -- need disambigu h hidden
-- precomposition by clock with correct Bundle weight `bubble`
omit h
def stencil (S: Cn) : Cn →ₗ[ℂ] Cn:= raiseW.comp ((substitute S).comp Clock.out)
lemma gradeS (S P:Cn): Clock.out (stencil S P)= substitute S (Clock.out P):= saving _
lemma pillar {e:Cn}(he:Rooted e){K L:Cn}: stencil e (K*L)=stencil e K*stencil e L:= by apply reserve; rw [gradeS,out_prod,out_prod,gradeS,gradeS ]; exact Eq.symm (substitute_pair he _ _ _) -- argument pair
lemma alone (z:ℂ)(e:Cn): stencil e (PowerSeries.C z) = PowerSeries.C z:= by apply reserve; rw [gradeS ]; rw [show Clock.out (PowerSeries.C z) =useN.refineV z from funext fun i=> by rw [out_coeff, coeff_C]; unfold refineV; split; rw [if_pos (by assumption)]; rw [if_neg (by assumption)]]; exact Clock.substitute_unit e z
include h
lemma commuting {e:Cn}(he:Rooted e)(K:Price p) : guide M (Clock.warp p e he V) (Clock.warp p e he K)= stencil e (guide M V K):= by
   apply reserve; rw [gradeS ]; apply guides; rw [warp_acts, Program.pay0 ]; exact h; rw [warp_acts,warp_acts]; exact Clock.rotate M he (bought M V h K) h
omit h [Fintype A]
lemma currency_c {p:Sector A}(e:ℂ)(u:Price p): currency p (PowerSeries.C e)* u=e • u:= by
    apply Paper.rack; funext i; rw [Clock.currency,PowerSeries.map_C, Paper.trackC_mul,cash1,coin_product,map_smul ]; rfl
lemma warp_t {e:Cn}(he:Rooted e)(u:Price p)(x:ℂ): warp p e he (x • u)=x • warp p e he u:= by apply Paper.rack; rw [ warp_acts,map_smul,map_smul,map_smul,warp_acts ]
lemma out_C0 (X: Cn): out X 0=constantCoeff X:= by rw [out_coeff,coeff_zero_eq_constantCoeff_apply]
end YM.FVA2.Attend
