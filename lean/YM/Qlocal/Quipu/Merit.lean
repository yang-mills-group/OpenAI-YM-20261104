import YM.Qlocal.Quipu.Incline
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
-- witness gauge.Flow limit plus at any fixed position all short canonical slip entries. Costs next. gauge U(t) definition fixes spelling uppercase. Use engine `rule` with `exteriorL`. no unit dilations hidden.St.V.
local notation "S"=> Coarse G
local notation "Ω"=> rule (Coarse G) n
local notation "X"=> fieldDir G n 1
local notation "M"=> ports G n
variable (U:Config G n)(o:Lattice.Order)(p:Site n)(v w:Cover)

variable (χ:G.El)(x: Ker.rule (Coarse G) n)(e: Edge (Site n))(q:Site n) {t d d0 θ ℓ: ℝ} (hw: ‖x‖ ≤ 1) (hh: PaintSupply G k d)
local notation "K"=> (ports G n)
abbrev ivory (G:Gauge)(k:ℕ)(t:ℝ):= (1+outerCost G k t)
abbrev paceL (G:Gauge)(n: ℝ)(k:ℕ)(d:ℝ) := (4*n)*(ivory G k d*royalty G)
def depend (G:Gauge) (n:ℝ)(k:ℕ) (d:ℝ):= let r:= royalty G; paceL G n k d * r+(ivory G k d*r+paceL G n k d)
local notation "w0"=> (ivory G k d)
local notation "u0"=> paceL G n.val k d
local notation "p0"=> depend G n.val k d
local notation "β"=> royalty G
local notation "σ"=> Uniform.shade G
local notation "Τ0"=> passing x
local notation "Τ"=> blade o p χ x
include hw
lemma corridor (e:Body 1 n): ‖ports G n x e‖≤Uniform.shade G:= by
 apply le_trans (norm_le_pi_norm ..); apply (tint_le ..).trans; nth_rw 2 [← mul_one (Uniform.shade G)] -- may occ wrong
 refine mul_le_mul_of_nonneg_left (le_trans ?_ hw) (shade_pos _).le; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; exact norm_le_pi_norm x ..
include hh
lemma years_credit : Allows k (fun t:ℝ=> G.mat (passing x t e)) 0 (outerCost G k d):= by
 let x0:= (ports G n x) (e.1, coord e.2); let Q:=ContinuousLinearMap.toSpanSingleton ℝ x0; have h1:‖Q‖≤ Uniform.shade G:= (ContinuousLinearMap.norm_toSpanSingleton x0).trans_le (corridor x hw _)
 simp_rw [passing, Work.F03.represent_link]; exact (hh.2 (Q 0) ((Q.map_zero).symm ▸ (norm_zero|>.le.trans (shade_pos _).le))).comp (allows_linear h1 (((Q.map_zero).symm ▸ (norm_zero|>.le.trans (shade_pos _).le)))) -- h1 instance.L.h signature
omit hw in
lemma ivory_ge : 0≤ ivory G k d:=add_nonneg zero_le_one (outer_pos G _ hh.1).le
lemma happy_paid : Mode (passing x) 0 k (ivory G k d):= by
 refine ⟨ivory_ge hh,fun e=>?_⟩; have h:= years_credit x e hw hh; simpa only [mul_one] using! thicken (f:=fun t:ℝ=> passing x t e) (Brush.offer.2 ⟨h.analytic.of_le (m:=k) le_top,h.norm_le⟩)
local notation "q1"=> max_le (royalty_ge G) (le_rfl)
lemma nice : Brush k (royalty G) (paceL G n.val k d) (fun t:ℝ=> G.mat (breeze o p χ x t q)) 0:= by
 let w:= Incline.loom o p q; have h:= happy_paid x hw hh; have he:= tour w p h.pos h.atLink; apply Brush.climb (d:= w.length*(ivory G k d *royalty G)) (u:=royalty G); rotate_left
 · exact le_rfl
 · apply mul_le_mul_of_nonneg_right _ (mul_nonneg h.pos (zero_le_one.trans (royalty_ge _))); exact_mod_cast extraordinarily o p q
 unfold breeze flow; have hz:Brush k (royalty G) (0*royalty G+w.length*(w0*royalty G)) (fun t:ℝ=>G.mat (χ) *G.mat (travel (passing x t) p w)) 0 := links (f:=fun _ :ℝ=> χ) (a_oneB G χ le_rfl) he _ q1; simpa only [G.mat_mul,zero_mul,zero_add] using! hz
omit hw
include n
lemma pace_ge : 0≤ paceL G n.val k d:= by unfold paceL; have hv:= ivory_ge hh; have hf := royalty_ge G; positivity
lemma depend_ge : 0≤depend G n.val k d:= by unfold depend; have hx:= pace_ge (n:=n) hh; dsimp only; have hp:= royalty_ge G; have hg:= ivory_ge hh; positivity
include hw
lemma right_phase : Mode (blade o p χ x) 0 k (depend G n.val k d):= by
 let d₁:=u0; let P:=royalty G; let z:= breeze o p χ x; have h:= happy_paid x hw hh; refine ⟨depend_ge (n:=n) hh,fun i=>?_⟩; have hx : Brush k P (d₁*P+(w0*P+d₁)) (fun t=> G.mat (z t i.1)* (G.mat ((passing x t) i) *G.mat ((z t (i.1+step i.2))⁻¹))) 0:= links (f:=fun t=>z t i.1) (nice o p χ x _ hw hh) (links (f:=fun t:ℝ=> passing x t i) (h.atLink _) (Blaze.reverse (f:=fun t:ℝ=> z t (i.1+step i.2)) (nice o p χ x _ hw hh)) _ q1) _ q1; unfold blade gloss; simp only [Lattice.gauge,mul_assoc,Gauge.mat_mul]; exact hx
lemma available(e): Allows k (fun t:ℝ=>G.mat (blade o p χ x t e)) 0 (royalty G*(1+depend G n.val k d)^k):= by
 refine ⟨planeQ o p χ x e,fun i hi=>?_⟩; have h: 0≤p0:= depend_ge hh; exact ((right_phase o p χ x hw hh).atLink e |>.order i hi).trans (mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ h (le_add_of_nonneg_left zero_le_one) _) (pow_le_pow_right₀ (le_add_of_nonneg_right h) hi)) (zero_le_one.trans (royalty_ge _)))
noncomputable abbrev leaning (G:Gauge)(n:Side)(k:ℕ)(d ℓ:ℝ):= composeCost k ℓ (royalty G*(1+depend G n.val k d)^k)
local notation "v0"=> leaning G n k d ℓ
variable (hp: Allows k G.plog 1 ℓ)
include hp
lemma announce (i:Leaf n (Coarse G)): Allows k (fun t:ℝ=> pulled o p χ x t i) 0 (leaning G n k d ℓ):= by
 let i':= (i.1,axisEquiv.symm i.2.1); let f(t:ℝ):= G.mat (blade o p χ x t i'); let j:= i.2.2; have ht:f 0=1:=by simp [f,bornQ]
 let L0:=EuclideanSpace.proj (𝕜:=ℝ) j;
 have hx:‖L0‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [one_mul]; change ‖x j‖ ≤ _; simpa only [Real.norm_eq_abs,EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using (abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ j) x))
 have hu:= ((ht.symm ▸ hp : Allows k G.plog (f 0) ℓ).comp (available o p χ x hw hh i')).linear L0 hx; rw [one_mul] at hu; exact hu
omit hw n in
lemma leaning_ge(q:Side):0≤ leaning G q k d ℓ:= by have he:= hp.nonneg; have h:= depend_ge (n:=q) hh; have hg:= royalty_ge G; unfold leaning composeCost; positivity
omit hw hp hh n
private lemma bends {f:ℝ→ℝ} (h: Allows (k+1) f 0 t)(he:f 0=0): Allows k (Laplace.SigmaP.shift f) 0 t:=by
 let v:= Laplace.SigmaP.shift f; have h0:ContDiffAt ℝ ω f 0:= h.analytic; refine ⟨shifty h0,fun j hj=>?_⟩; let k:= h.norm_le (j+1) (Nat.succ_le_succ hj); rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at k ⊢; have hv : someJ v j=someJ f (j+1):= (congr_fun (shift_down he h0) _).trans (congr_arg _ (Nat.add_comm ..))
 have hx:iteratedDeriv (j+1) f 0=((j+1:ℕ):ℝ)*iteratedDeriv j v 0:= by
    unfold someJ at hv; simp_rw [smul_eq_mul, Nat.factorial_succ,Nat.cast_mul] at hv; have hb: (j.factorial:ℝ)>0:= (by positivity); have hh:(↑(j+1:ℕ):ℝ)>0:= (by positivity); field_simp at hv; first|exact hv.symm| (rw [← hv]; ring)| linarith -- inspect
 rw [hx,norm_mul,Real.norm_of_nonneg (by positivity)] at k; exact le_trans (le_mul_of_one_le_left (norm_nonneg _) (by norm_cast; omega)) k
include n
variable (hK:PaintSupply G (k+1) d) (hG:Allows (k+1) G.plog 1 ℓ)
include hw hK hG
lemma lent : Allows k (lifts o p χ x) 0 (leaning G n (k+1) d ℓ):=by
 let T:= pulled o p χ x; let v:= lifts o p χ x; refine allows_pi (leaning_ge hK hG n) (fun i=>?_)
 let L:= ContinuousLinearMap.proj (φ:=fun _:Leaf n (Coarse G)=>ℝ) (R:=ℝ) i; let P:= L ∘ T; have hx : Allows (k+1) P 0 (leaning G n (k+1) d ℓ):=announce o p χ x hw hK hG _; have hm:P 0=0:= by rw [show P 0=L (T 0) from rfl, show T 0=_ from incline_blank .., map_zero]
 have he(y): v y i= Laplace.SigmaP.shift P y:= (L.dslope_comp T 0 y (fun _=> (necessary o p χ x).differentiableAt (by simp))).symm; change Allows k (fun y=> v y i) 0 _; simp_rw [he]; exact bends hx hm
omit hw n hK hG
variable {φ₀:Type} (Y:φ₀→ℝ)
include hp hh
lemma prosperity : Weight Y (k*k) (fun i n=>leaning G n k d ℓ):= by
 let u:= ivory G k d; let r:= royalty G; have hr:0≤r:= zero_le_one.trans (royalty_ge G); have hx:0≤u:= ivory_ge hh; have he:= hp.nonneg; let U:= Weight.length Y; have ht:Weight Y 1 (fun i n=> paceL G n.val k d):= (Weight.times ((Weight.fixed Y 4 (by norm_num)).times (Weight.length Y)) (Weight.fixed Y _ (mul_nonneg hx hr))); have h':Weight Y 1 (fun i n=>1+depend G n.val k d):= Weight.stamp ((Weight.fixed Y 1 zero_le_one).ups zero_le_one) ((ht.times (Weight.fixed Y _ hr)).stamp (((Weight.fixed Y _ (mul_nonneg hx hr)).ups (Nat.zero_le 1)).stamp ht))
 have hξ: Weight Y k (fun i n=>1+royalty G*(1+depend G n.val k d)^k):= by simpa only [Nat.zero_add,Nat.one_mul] using! (((Weight.fixed Y 1 zero_le_one).ups (Nat.zero_le (0+1*k))).stamp ((Weight.fixed Y _ hr).times (h'.raise k)))
 simpa only [Nat.zero_add] using! (Weight.times (Weight.fixed Y _ (mul_nonneg (Nat.cast_nonneg (α:=ℝ) k.factorial) he)) (hξ.raise k))

end Incline
end YM.Qlocal.Quipu.Eluder
