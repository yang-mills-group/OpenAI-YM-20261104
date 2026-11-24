import YM.MSbar.Wave.Pupil
import YM.MSbar.Wilson.Coordinates
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open Gauge Lattice Wilson RG Tree Precision Exterior Push Push.Uniform
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open Set MvPolynomial Native.Chart
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "X"=> Positions (Primary n G)
local notation "V"=> fieldDir G n 1
local notation "α"=> ((0:ℝ),(1:ℝ))
variable (s:Site n→ G.Color)(p:Clip)(R:PathData G)(F:Nesting G n)
def ran (i:Body 1 n) : Native.Chart.Rail G := (s i.1,s (i.1+step (axisEquiv.symm i.2)))
noncomputable def coneT (t:ℝ × V) : V := fun i=> Native.Chart.head G (ran s i) (t.1,t.2 i)
noncomputable def cones (X':ℝ × Positions (Primary n G)) : Positions (Primary n G):= (tint G _).symm (coneT s (X'.1,tint G _ X'.2))
noncomputable def speedsK (x:Positions (Primary n G)): Positions (Primary n G):= (tint G _).symm (fun i=> speed G (ran s i) (tint G _ x i))
lemma coneDiff : ContDiffAt ℝ ω (cones s) 0:=by
    let V':=tint G (Body 1 n); let u := (0:ℝ × X); refine V'.symm.contDiff.contDiffAt.comp (f:=fun v:ℝ×X=>coneT s (v.1,tint G _ v.2)) u (contDiffAt_pi.mpr fun i=>?_); let Q(z:ℝ×X):=(z.1,V' z.2 i); have hv:Q 0=(0,0):=rfl; exact (show ContDiffAt ℝ ω _ (Q 0) from hv ▸ jet G (ran s i)).comp u (show ContDiffAt ℝ ω Q u from contDiffAt_fst.prodMk ((contDiffAt_apply ℝ G.Color i _).comp u (V'.contDiff.contDiffAt.comp u contDiffAt_snd)))
lemma cone_zero : cones s 0=0:=by ext i; rcases i with ⟨v,j⟩; change Native.Chart.head G _ (0,0) j=0; unfold Native.Chart.head; simp only [still, G.mat_lieExp_zero,G.mat_one,plog_one];rfl
lemma lifts : ∀ᶠ (u:ℝ×X) in 𝓝 0, represent (tint G _ (cones s u))= gauge (fun y=> G.lieExp (u.1 • (-s y))) (represent (tint G _ u.2)):=by
    let K(z:ℝ×X)(e: Edge (Site n)) := (z.1,tint G _ z.2 (e.1,Exterior.coord e.2)); have he(e): Tendsto (fun z=> K z e) (𝓝 0) (𝓝 (0,0)):= continuousAt_fst.prodMk (((continuous_apply _).continuousAt).comp ((tint G _).continuousAt.comp continuousAt_snd)); filter_upwards [eventually_all.mpr (fun i=> (he i).eventually (down G (ran s (i.1,Exterior.coord i.2))))] with v h; funext i
    rw [cones, ContinuousLinearEquiv.apply_symm_apply,Work.F03.represent_link]; unfold Lattice.gauge
    apply (h i).trans; dsimp only; rw [Work.F03.represent_link]; unfold ran hit; rw [show axisEquiv.symm (Exterior.coord i.2)=i.2 from axisEquiv.symm_apply_apply _, smul_neg _ (s (_+ _)),Work.F03.exp_neg_color,inv_inv]
lemma spruceT : ∀ᶠ v:X in 𝓝 0, cones s (0,v)=v∧HasDerivAt (fun z:ℝ=> cones s (z,v)) (speedsK s v) 0:=by
    let K:= tint G (Body 1 n); let p(i:Body 1 n)(x:X):=K x i
    have hv(i): Tendsto (p i) (𝓝 0) (𝓝 0):=(continuous_apply i).continuousAt.comp K.continuousAt
    have ht : Tendsto (fun x:G.Color=> ((0:ℝ),x)) (𝓝 0) (𝓝 (0,0)):=continuousAt_const.prodMk continuousAt_id; filter_upwards [eventually_all.mpr (fun i=> (hv i).eventually ((enters G (ran s i)).and (ht.eventually ((jet G (ran s i)).eventually (by simp)))))] with x h
    let f(t:ℝ):=coneT s (t,K x); have hz(i): HasDerivAt (fun y:ℝ=>f y i) (Native.Chart.speed G (ran s i) (K x i)) 0:=breeze G _ _ (h i).2
    have hh:f 0=K x:=funext fun i=> (h i).1
    have hk: HasDerivAt f _ 0:=hasDerivAt_pi.mpr hz
    refine ⟨congr_arg K.symm hh|>.trans (K.symm_apply_apply x),?_⟩
    exact (K.symm.hasFDerivAt.comp_hasDerivAt _ hk)
-- scaled.Walter.S enlargement t×r.M.
variable (p':ℕ){S:ℝ → Config G n→ℝ}(h:Trend S F R p p')
local notation "ζ!"=>tariff n p' p R F
variable (v:Positions (Primary n G))
noncomputable def checkK (z:ℝ × ℝ) : ℝ:= scaledT p' (tariff n p' p R F) (z.1, cones s (z.1 • (z.2,v)))- scaledT p' (tariff n p' p R F) (z.1,z.1 • v)
include h
lemma checkD : ContDiffAt ℝ ω (checkK s p R F p' v) 0:=by
   let T:=checkK s p R F p' v; change ContDiffAt ℝ ω T 0; let u(z:ℝ×ℝ):=z.1 • (z.2,v); apply ((scale_diff ..).contDiffAt.comp _ (contDiffAt_fst.prodMk (show ContDiffAt ℝ ω (cones s ∘ u) 0 from (show ContDiffAt ℝ ω _ (u 0) from by rw [show u 0=0 from zero_smul _ _]; exact coneDiff s).comp _ (contDiffAt_fst.smul (contDiffAt_snd.prodMk contDiffAt_const))))).sub; exact (scale_diff ..).contDiffAt.comp _ (contDiffAt_fst.prodMk (contDiffAt_fst.smul contDiffAt_const))
lemma heck (r:ℝ) : Grade (fun t=>checkK s p R F p' v (t,r)) (p'+2+1) :=by
    let P:= ζ!; let x:ℝ→ ℝ× X:=fun t=>t•(r,v); have he:x 0=0:=zero_smul ..; have hf:Tendsto x (𝓝 0) (𝓝 0):= by rw [←he]; exact ((continuous_id.smul continuous_const).continuousAt)
    let W(t):=cones s (x t); have hp: W 0=0:=by unfold W; rw [he,cone_zero]
    have hQ: ContDiffAt ℝ 1 W 0:= ((he.symm ▸ coneDiff s : ContDiffAt ℝ ω _ (x 0)).comp 0 (contDiffAt_id.smul contDiffAt_const)).of_le le_top
    -- syntax semicolons
    let w(t:ℝ):= (t⁻¹) • W t
    obtain ⟨C,X₀,hX,hg⟩:= hQ.exists_lipschitzOnWith
    have hk: Price (fun _ (_:Unit)=>True) 0 (fun t _=>w t):=by
        apply fixed 0 (C:ℝ); filter_upwards [width, (show ∀ᶠ x in 𝓝 (0:ℝ), x∈X₀ from hX).filter_mono nhdsWithin_le_nhds] with t hh hh' i _
        have he:=hg.dist_le_mul t hh' 0 (mem_of_mem_nhds hX); unfold w; obtain ⟨hv,-⟩:=hh; simp only [hp,dist_zero_right,Real.norm_eq_abs,abs_of_pos hv] at he
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le),pow_zero,pow_zero,mul_one,mul_one]; exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hv.le)).trans_eq (by field_simp)
    let P':= (fun t:ℝ=> v); have hp(x:ℝ)(hx:0<x): x•w x = W x:=smul_inv_smul₀ hx.ne' _; have hh:∀ᶠ t in Γ,S t (postcard G n t (w t))= S t (postcard G n t (P' t)) := by
        filter_upwards [((hf.mono_left nhdsWithin_le_nhds).eventually (lifts s)),h.base,width] with t ht he hF
        unfold postcard; rw [hp _ hF.1]; rw [show represent (tint _ _ _) = _ from ht]; exact he.1.shield ..
    have hf := equivalence p' p R F h hk (Price.fromConst v) hh; have hz := (Price.xrise _ 2).product hf -- implicit Grade def
    rw [show p'+2+1=2+(p'+1) from (by omega)]; refine hz.egress ?_; filter_upwards [width] with t ht y hy; have hP:= cool n p' p R F h.plane
    rw [mul_sub,← scale_r p' ζ! hP, ← scale_r p' ζ! hP, hp _ ht.1];rfl
lemma omens : ∀ i:ℕ, i≤p'+2 → bill (fun t:ℝ=> pine (checkK s p R F p' v) 1 (t,0) (0,1)) i=0:= bench _ (checkD s p R F p' h v) (Eventually.of_forall (fun x=> heck s p R F p' h v x)) -- order
end YM.MSbar.Wave
