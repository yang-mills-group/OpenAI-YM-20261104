import YM.MSbar.Rolling.Actors
import YM.Work.F01
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set
open Lattice Wilson RG Precision Tree Push Push.Uniform Exterior
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S: StepData c f}(B:Forest S.ratio)(i:S.Choices)(R T: PathData G)(p q: Clip)(ρ:fieldDir G c 1→AxisChart G B)
open Work.F03
local notation "∆"=> fderiv ℝ
local notation "P"=> uncurry (tested B i p R)
local notation "C₀"=> priced B i p R
local notation "W"=> paint B G
local notation "V"=> fieldDir G c 1
local notation "X"=> Positions (Primary c G)
local notation "Y"=> Positions (Key B G)
local notation "N"=> Positions (Primary f G)
local notation "H"=> Positions (Joint B G)
local notation "K"=> Push.Uniform.block (priced B i p R) 0
local notation "Ψ"=> (tint G)
variable (h:S.patch.Branches S.kernel G) (hm: Premier (main f p R))
include h hm
lemma blueprint {η:ℝ}(he:0<η)(hv:PriceGap B p R η): Matrix.PosDef (Push.Uniform.block (priced B i p R) 0) := by
    have ht:=paysCore B i p R h hm; apply portrait (σ:=Key B G) ht.1 rfl; intro u hu
    let z:= Ψ B.Free u; let x₀:V×AxisChart G B:= W (meetVar (0:X) u); have ha:= hv i z; rw [Work.F01.vertical_hessian B i (fun t=>(legP B t p R h hm).1) z] at ha -- inspect
    have hx : 0 < ∑ j, ‖z j‖^2:= by
        rw [show _= _ from vertical_count B u]; refine Finset.sum_pos' (fun j _=> sq_nonneg (u j)) ?_; have he:∃ y,u y ≠0:=Function.ne_iff.mp hu; obtain ⟨y,he⟩:=he; exact ⟨y,Finset.mem_univ _,sq_pos_of_ne_zero he⟩
    have hk: x₀=((0:V),z):=by unfold x₀; rw [paint_meet,map_zero]
    apply ((mul_pos he hx).trans_le ha).trans_eq; have hg :rim C₀ (meetVar 0 u) (meetVar 0 u)=rim P x₀ x₀:= (legP B i p R h hm).carriage (paint B G).toContinuousLinearMap _ _
    rw [iteratedFDeriv_two_apply,hg,hk];rfl
variable (hp:Critical B p R ρ) (hq: ClassicalMatch B p q R T ρ)
def lyricP (ρ:fieldDir G c 1→AxisChart G B) : Positions (Primary c G) → Positions (Key B G):=fun x => (tint G _).symm (ρ ((tint G _) x))
local notation "ζ"=> lyricP B ρ
include hp
lemma tone : ContDiffAt ℝ ω (lyricP B ρ) 0:=by
    let Q:= (tint G B.Free).symm; let Vf:= tint G (Body 1 c); have hg:ContDiffAt ℝ ω ρ (Vf 0):=by rw [map_zero]; exact hp.2.1
    exact Q.contDiff.contDiffAt.comp _ (hg.comp _ Vf.contDiff.contDiffAt)
lemma veil : lyricP B ρ 0=0:=by unfold lyricP; rw [map_zero,hp.1,map_zero]
lemma rose : ∀ᶠ x in 𝓝 0,Slope (priced B i p R) (meetVar x (lyricP B ρ x))=0:=by
    let L:= tint G (Body 1 c); let A:= Ψ B.Free; have hz: Tendsto L (𝓝 0) (𝓝 0):=by simpa using L.continuous.tendsto (0:X)
    let s: X→H:=fun x=> meetVar x (ζ x); have h₀ : s 0 =0:=by unfold s; rw [veil B _ _ _ h hm hp]; exact map_zero (partSpace _ _).symm
    have ht : Tendsto s (𝓝 0) (𝓝 0):=by
        rw [←h₀]; exact ((partSpace _ _).symm.continuousAt.comp (continuousAt_id.prodMk (tone B R p ρ h hm hp).continuousAt)).tendsto
    have hv:= paysCore B i p R h hm; filter_upwards [ht.eventually (hv.1.eventually (by simp)), hz.eventually ((hp.2.2 i).2)] with x he ht; apply (slope_zero_test he).2; let Vf:= tested B i p R (L x); have hx:A (ζ x)=ρ (L x):= A.apply_symm_apply _; have hi:= (show HasFDerivAt Vf 0 (A (ζ x)) from hx.symm ▸ ht).comp _ A.hasFDerivAt; have he : (0: AxisChart G B→L[ℝ] ℝ).comp A.toContinuousLinearMap=0:=by simp
    rw [he] at hi; have hg(q:Y): priced B i p R (meetVar x q)=(Vf ∘ A) q:=by unfold priced; rw [Function.comp_apply,paint_meet]; rfl
    simp_rw [hg]; exact hi
noncomputable def center (ρ:fieldDir G c 1→AxisChart G B): Positions (Primary c G)→L[ℝ]Positions (Key B G):= (∆ (lyricP B ρ) 0)+ imageCopy B G
local notation "m!"=> center B ρ
lemma lovely (x:Positions (Primary c G))(he: Matrix.PosDef (Push.Uniform.block (priced B i p R) 0)): center B ρ x = vest (priced B i p R) x+imageCopy B G x :=by
    unfold center; rw [_root_.add_apply, pulseK (paysCore B i p R h hm).1 (veil B R p ρ h hm hp) (tone B R p ρ h hm hp) (rose B i R p ρ h hm hp) x he]
-- Hess horizontal relation.C.Output
include i hq
lemma pierce : Premier (main c q T) := ((legP B i p R h hm).make (hx:=contDiffAt_id.prodMk hp.2.1) (w:=fun x=> (x,ρ x)) (by simp [hp.1])).stitch (fun j hj=> hq j (by omega) i)
lemma posts (x:Positions (Primary c G)) : rim C₀ (meetVar x (∆ (lyricP B ρ) 0 x)) (meetVar x (∆ (lyricP B ρ) 0 x))=rim (main c q T) ((tint G _) x) ((tint G _) x):=by
    let L:= tint G (Body 1 c); let F(x:V):= (x,ρ x); let G':= P ∘ F; let u:= F ∘ L; let v (x:X):= meetVar x (ζ x)
    have W₀ : W ∘ v=u:=by funext x; change W (meetVar x (ζ x))=_; rw [paint_meet]; rw [show (tint G _) (ζ x)=_ from (tint G _).apply_symm_apply _];rfl
    have hP:F 0=0:=by simp [F,hp.1]
    have hv₀ : v 0=0:=by unfold v; rw [veil B R p ρ h hm hp]; exact map_zero (partSpace (Primary c G) (Key B G)).symm
    have hG:= (legP B i p R h hm).make (w:=F) (show ContDiffAt ℝ ω F 0 from contDiffAt_id.prodMk hp.2.1) hP
    let Q: X→L[ℝ] X × Positions (Key B G) := (ContinuousLinearMap.id ..).prod (∆ ζ 0)
    have he:HasFDerivAt v ((partSpace (Primary c G) (Key B G)).symm.toContinuousLinearMap.comp Q) 0:= (partSpace (Primary c G) (Key B G)).symm.hasFDerivAt.comp 0 ((hasFDerivAt_id (𝕜:=ℝ) (0:X)).prodMk ((tone B R p ρ h hm hp).differentiableAt (by simp)).hasFDerivAt)
    have hh : ∆ v 0 x=meetVar x (∆ ζ 0 x):= congr_arg (fun i:X→L[ℝ] H=> i x) he.fderiv
    have hd:ContDiffAt ℝ ω v 0:= (partSpace (Primary c G) (Key B G)).symm.contDiff.contDiffAt.comp (0:X) (contDiffAt_id.prodMk (tone B R p ρ h hm hp))
    have ht : C₀ ∘ v=G' ∘ L:=by change P ∘ W ∘ v=_; rw [W₀]; rfl
    rw [←hh, ←(paysCore B i p R h hm).station hd hv₀ x x,ht,show rim (G' ∘ L) x x=rim G' (L x) (L x) from hG.carriage L.toContinuousLinearMap x x]
    have Ht:=congr_arg (fun f:Tensor.T V ℝ 2=>f ![L x,L x]) (hq 2 (by omega) i).2.2; change iteratedFDeriv ℝ _ _ _ _= iteratedFDeriv ℝ _ _ _ _ at Ht; rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply] at Ht; exact Ht
end YM.MSbar.Rolling
