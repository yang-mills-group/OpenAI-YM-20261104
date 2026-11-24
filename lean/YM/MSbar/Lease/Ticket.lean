import YM.MSbar.Cottage.Suns
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open ConnectedActivityE6
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U: Config G f}{R: Rep G f}{σ C T H K A B a b v r δ w β:ℝ}{M k m:ℕ}
open Finset RG.PathData Tree Push.Uniform Pressure
variable (F:Forest S.ratio) (X :Support f)
open SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric
variable (J:Voice G) (Q: Config G c) (μ: Positions (Key F G))(Y:Support f)
variable (i:S.Choices)(p:Palisade)(x: Positions (Primary c G)) (h:Grants i R F p m)
set_option quotPrecheck false
local notation "W"=> (represent (tint G (Exterior.Body 1 c) x))
def stars (p:Palisade)(d:ℝ):=
    let j:= p.coords*countCost p.a; |ice p.coords p.gap p.a p.density| *(d*(p.density*j)+d*(p.density*j)*j*d)
include h
lemma terror (ha:‖x‖ ≤ a) (hb:a<p.initial): ‖vest (priced F i R.clip R.path) x‖ ≤ stars p a :=by
    let f:=priced F i R.clip R.path; let M:=Key F G; let A:Positions M:=fderiv ℝ (Slope f) 0 (meetVar x (0:Positions M)); let j:= p.coords*countCost p.a; let k:=ice p.coords p.gap p.a p.density; have he:0≤ a:=(norm_nonneg _).trans ha
    let D := a*(p.density*j)+a*(p.density*j)*j*a; have hz:‖A‖≤ D:=sight_range h.buys _ (by rw [norm_meet, max_le_iff,norm_zero]; exact ⟨ha,he⟩) (hb.trans_le p.enroll)
    apply (pi_norm_le_iff_of_nonneg (show 0 ≤ stars p a from mul_nonneg (abs_nonneg _) ((norm_nonneg _).trans hz))).mpr; intro t; let m:=plank f t; have hk : ‖vest f x t‖= |blush m A|:=by change |-blush m A|= _; exact abs_neg _
    rw [hk]; exact (washes ..).trans (mul_le_mul ((income h.buys t).trans (le_abs_self k)) hz (norm_nonneg _) (abs_nonneg _))
omit h
-- fixed center and radii routine. board X card arbitrary root. `host=3*distance`.
variable (P:Patch)(J:Voice G)(K:KernelChoices)
local notation "Ξ"=> tip G P.L
-- local α log.Buys

def pillow (x:ℝ):=3*distance x
def room (x:ℝ):= distance x * Real.sqrt (Real.log x)
def ceilingP (p:Palisade):=
    let j:= p.coords*countCost p.a; let f:= |p.density*j| *(1+|j|); |ice p.coords p.gap p.a p.density| *f

def rot (p:Palisade)(x:ℝ):=(2+ceilingP p)*skies x
def voyageB (x:ℝ) := let r:= radiusB x; (4*r+2)*(r+100)+r+100
lemma sail (p:Palisade){v : ℝ}(h:0≤v)(hp:v≤1) : stars p v≤ ceilingP p*v := by
   unfold stars ceilingP; let f:=ice p.coords p.gap p.a p.density; let j:= p.coords*countCost p.a
   let c:=p.density*j; change |f| * (v*c+v*c*j*v)≤ |f| *(|c| *(1+|j|))*v; rw [mul_assoc |f|]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg f)
   have hh: c*j*v ≤ |c| *|j|:= (le_abs_self _).trans (by rw [abs_mul,abs_mul,abs_of_nonneg h]; exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hp)
   linarith only [mul_le_mul_of_nonneg_left hh h,mul_le_mul_of_nonneg_left (le_abs_self c) h]
lemma fees (g:Clear G J) : ∀ᶠ x:ℝ in atTop,
      let y:=tip G P.L x; let t:= rot p y; let w:= room y; let r:= y^(-(1:ℝ)); let V:=base J y; let E:=skies y
      1<y ∧ 0<pillow y ∧ pillow y≤ w ∧ E≤ t∧ E<p.initial ∧ shade G*E ≤ J.r ∧ stars p E + w≤ t ∧ t+2*w<p.initial ∧ shade G*t ≤ J.r ∧ 0<V ∧ 4*(J.C*(shade G*t)+V/4) ≤ temp y ∧ necklace P ≤ voyageB y ∧ r ≤1 ∧ Posture.gardenCity p J t r w :=by
    let d:=tip G P.L; let E:=skies ∘ d; let v:=base J ∘ d; let t:= rot p∘ d; let R₀:= -(1/2:ℝ); let r x:= (d x)^(-(1:ℝ))
    let A:=4*(J.C*(shade G*(2+ceilingP p))+2*J.C*shade G)
    have hF:= (flog P (G:=G)); have hV:Rate G P.L R₀ t:=hF.mul_left _; have hz:Rate G P.L (-1) r:= Rate.power
    have hg':Rate G P.L R₀ (fun x=> J.C*(shade G*t x)+r x):= ((hV.mul_left _).mul_left _).add (hz.weaken (by norm_num [R₀]))
    have hL:= Work.E09.betaF_growth G P.L
    have hB:= Beam.lesser (G:=G) (L:= P.L) ((Beam.logfine G P.L|>.power 2).mul (Beam.coin A)) (show 0<(1:ℝ) from one_pos)
    have hk:0 ≤ ceilingP p:=by unfold ceilingP; positivity
    have hA:0<J.C:=zero_lt_one.trans_le g.cost; have ht': 0≤ A:= by unfold A; have hz:= shade_pos G; positivity
    let i:= J.C*(1+J.C*J.r); have hp:0< i:=by unfold i; have hh:=g.depth; positivity
    have hc0:= (show Rate G P.L (-1) (fun x=> i*r x) from hz.mul_left _)
    filter_upwards [shiftedLog G P.L, (Real.tendsto_log_atTop.comp hL).eventually_ge_atTop 9,
      hF.below (by norm_num) _ one_pos,
      hV.below (by norm_num [R₀]) _ (show 0<p.initial/4 by have h:=p.first; positivity),
      (hV.mul_left (shade G)).below (by norm_num [R₀]) _ g.depth,
      hB, hL.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (necklace P)), gross_scale G P.L,
      hz.below (by norm_num) _ g.dist,
      (hz.mul_left J.C) R₀ (by norm_num [R₀]),hg'.below (by norm_num [R₀]) _ g.dist,hc0 R₀ (by norm_num [R₀])] with x hx hd hf hu hs h he hm hK hJ hz H₀
    let y:=tip G P.L x; let a:= Real.log y; let V:=base J y; let e:=skies y; let p':=pillow y; let w:=room y; let Z:=rot p y;have h': 1<y:=hx.2.2.1; have ha:9≤ a:= hd; have hu':0<y:= zero_lt_one.trans h'; let q:= y^R₀; have hq:0<q:=Real.rpow_pos_of_pos hu' _
    have hA': 1<a:=by linarith only [ha]
    let c:=Real.sqrt a; have hh':0≤c:=Real.sqrt_nonneg _; have H:c^2=a:=Real.sq_sqrt (by linarith only [ha]); have hH : 3 ≤ c:= by nlinarith only [hh',H,ha]
    have hH':c ≤ a:=by nlinarith only [hh',ha,H]
    have hL : 0< distance y:= (mul_pos hq (zero_lt_one.trans hA')); have hp':0<p':=mul_pos (by norm_num) hL
    have hw : p' ≤ w:= by unfold p' pillow; rw [mul_comm]; exact mul_le_mul_of_nonneg_left hH hL.le
    have hE : w≤ e:=mul_le_mul_of_nonneg_left hH' hL.le
    have hb: e≤1:= (le_abs_self (E x)).trans hf; have ho:0<e:=hp'.trans_le (hw.trans hE)
    have hZ:e≤Z:=le_mul_of_one_le_left ho.le (by linarith only [hk]); have hf': Z≤p.initial/4:=(le_abs_self (t x)).trans hu; have hj:=p.first; have hg': shade G*Z≤J.r:= (le_abs_self _).trans hs; have hn:0<V:=by unfold V base; have hh:=shade_pos G; positivity
    intro x' t₀ w' r' V' E'; refine ⟨h',hp',hw,hZ,by change e<p.initial;linarith only [hf',hZ,hj],(mul_le_mul_of_nonneg_left hZ (shade_pos G).le).trans hg', (add_le_add (sail _ ho.le hb) hE).trans ?_, ?_,hg',hn, ?_, ?_,hm,?_⟩
    · change _ ≤ (2+_)*e; linarith only [ho]
    · change Z+2*w <_; linarith only [hf',hE,hZ,hj]
    · have hU : a^ (2:ℕ)*A ≤ bbP y:= (le_abs_self _).trans (by rw [Real.rpow_one] at h; exact h)
      have hQ':q=(Real.sqrt y)⁻¹:= by unfold q R₀; rw [Real.rpow_neg hu'.le,Real.sqrt_eq_rpow]
      have hy : 4*(J.C*(shade G*Z)+V/4)=q*(a^2 * A):= by unfold q A V base R₀ Z rot skies distance a; ring
      rw [show 4*(J.C*(shade G*t₀)+V'/4)=q*(a^2 * A) from hy]; apply (mul_le_mul_of_nonneg_left hU hq.le).trans_eq; exact congr_arg₂ (·*·) hQ' rfl
    · exact le_trans he (show radiusB y≤ voyageB y from by unfold voyageB; dsimp only; omega)
    have hVx:q≤ distance y:=le_mul_of_one_le_right hq.le hA'.le; have hxq: q≤ w := hVx.trans (le_mul_of_one_le_right hL.le (by linarith only [hH])); have hq':0<r x:=Real.rpow_pos_of_pos hu' _
    refine ⟨hq',(le_abs_self _).trans hK, (le_abs_self _|>.trans hJ).trans (hxq.trans (le_trans (hE.trans hZ) (le_mul_of_one_le_left ((ho.trans_le hZ).le) (shade_one G)))),?_, (le_abs_self _).trans hz⟩
    change J.C*(shade G*Z)*(J.C*r x)+J.C*r x ≤ w; apply le_trans (b:=i*r x) ?_ ((le_abs_self _|>.trans H₀).trans hxq); unfold i; have ht:= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg' hA.le) (show 0≤ J.C*r x from mul_nonneg hA.le hq'.le)); linarith only [ht]
end YM.MSbar.Heath.Cottage
