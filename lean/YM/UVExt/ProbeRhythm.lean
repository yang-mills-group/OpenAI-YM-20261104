import YM.UVExt.JoinedThermals
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern

/-! Lift shifted canonical moment with HELD physical argument and original likelihood. X is reference output (chart's center). q>0 a real baseline ratio for the reference γ_min. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.UVExt.EnergyRay.Thermal.Core
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision ConnectedActivityE6 Mask Coat Raw ConnectedActivityE6.Blaze Silica Vine Flux Polar Gaussian Eider Poll
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

variable {G:Gauge} {c f L:Side} {S: StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio} {P:Teller G}
    (X:ConnectedActivityE6.Coat T F) (R:Rep G f) (q:ℝ) (Y:F.Slice G) (Z:Air f G) (V:Config G c) (a:ℝ)
variable {r:ℝ} (hq:0<q) (hR:0<R.beta) {k : Finset ℕ} {W η : ℝ} {I:Finset (Bond f)} {Ñ:Precision.ChartRatio G}
    {Y': YM.ConnectedActivityE6.Target G P} {P':Target.Order G W} {l:ℕ} {μ g v : ℝ}
local notation "Yₕ" => X.wrapY Y
local notation "Cₕ" => vary (X.wrapY Y) V

def key := worldZ (Yₕ) (scaled R q).beta Z
def take := steer Yₕ a (key X R q Y Z) V
def swept (b:ℝ) := WithLp.toLp 2 <| stand <| (gStep b)⁻¹ • (take X R q Y Z V a-voltage Cₕ)
private def unclipped (r:ℝ) := Real.sqrt r • (swept X R q Y Z V a R.beta)
def shutter (r:ℝ) := course Yₕ a (scaled R r).beta (Real.sqrt (r/q) • Z) V
def ker (t:ℂ) i := chandelier (k:=k) (a:=η) (d:=l) (Ñ:=Ñ) (W:=W) Cₕ R
    (take X R q Y Z V a) ((Yₕ).input (key X R q Y Z)) (swept X R q Y Z V a R.beta) i |>.run t

def realProbe (r:ℝ) := Gaussian.tilt (Pond.circuit (lensS I G) X.relating) (r/q) (Pond.swim (lensS I G) Z) * Flux.scalp I Yₕ V (scaled R r).beta a (Real.sqrt (r/q)• Z)
def densityCore := let z:=swept X R q Y Z V a R.beta; - Gaussian.value (Pond.circuit (lensS I G) (Cₕ).relating) (Pond.swim (lensS I G) z)
variable (I)
def ratio (t:ℂ) := let b:=densityCore (I:=I) X R q Y Z V a
                   let c:=realProbe (I:=I) X R q Y Z V a 1 /Real.exp b
                   Primitive.thermal (c:ℂ) b (lensS I G).card |>.run t
def monolith (W η:ℝ) (Ñ:ChartRatio G) (l:ℕ) (p:Molecule S) (k:Finset ℕ) (t:ℂ) := ratio X R q Y Z V a I t * ∏ i∈p, ker (k:=k) (η:=η) (l:=l) (Ñ:=Ñ) (W:=W) X R q Y Z V a t i

variable (hr:0<r)
include hR hq hr
lemma key_scale : worldZ (Yₕ) (scaled R r).beta (Real.sqrt (r/q) • Z) = key X R q Y Z := by
  unfold worldZ key
  rw [atmosphere_scaled _ R _ _ (div_pos hr hq) hR,worldZ]; unfold gStep; dsimp only [scaled]; rw [Real.sqrt_mul hq.le,Real.sqrt_mul hr.le,Real.sqrt_div hr.le,smul_smul]
  congr 2; field_simp
lemma shutter_eq : shutter X R q Y Z V a r=unclipped X R q Y Z V a r := by
  have hx : course Yₕ a (scaled R r).beta (Real.sqrt (r/q) • Z) V=swept X R q Y Z V a (scaled R r).beta := by
    unfold course; rw [key_scale _ _ _ _ _ hq hR hr]; rfl
  unfold shutter; rw [hx]; unfold unclipped swept gStep
  dsimp only [scaled]; rw [Real.sqrt_mul hr.le,inv_inv,inv_inv,mul_smul]; rfl
lemma real_ratio : ratio X R q Y Z V a I (r:ℝ)=((realProbe (I:=I) X R q Y Z V a r:ℝ):ℂ) := by
  let N:=lensS I G; let z:=Pond.swim N Z; let w:=swept X R q Y Z V a R.beta; let y:=Pond.swim N w
  let H:=Pond.circuit N (Cₕ).relating; let A:=Pond.circuit N X.relating
  let j:= Flux.jacL I Yₕ a (scaled R q).beta V Z
  have hsq : 0<Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hg : Real.exp (-Real.log A.det / 2) ≠0 := Real.exp_ne_zero _
  have h': Real.sqrt (2*Real.pi)>0 := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hh : (√(2*Real.pi))^(Fintype.card ↥N) ≠0 := pow_ne_zero _ h'.ne'
  let c:= j * (Real.sqrt (1/q))^N.card * Real.exp (-Real.log H.det / 2 + Real.log A.det / 2 + Gaussian.value A z)
  have hM (s:ℝ) (hs:0<s): realProbe (I:=I) X R q Y Z V a s=c*(Real.sqrt s)^(Fintype.card ↥N)*Real.exp (-s*Gaussian.value H y) := by
    have hs' := div_nonneg hs.le hq.le
    have ht : scalp I (X.wrapY Y) V (scaled R s).beta a (Real.sqrt (s/q)• Z)=j * (Shield.lens₀ H (Real.sqrt s • y) / Shield.lens₀ A (Real.sqrt (s/q) • z)) := by
      unfold scalp; rw [jacL,key_scale _ _ _ _ _ hq hR hs,(show course Yₕ a (scaled R s).beta (Real.sqrt (s/q)• Z) V=Real.sqrt s • w from shutter_eq X R q Y Z V a hq hR hs)]; rfl
    have hE (z:Body ↥N) (M:Matrix ↥N ↥N ℝ) (u:ℝ)(hu:0≤u): Shield.lens₀ M (Real.sqrt u • z) = ((Real.sqrt (2*Real.pi))^(Fintype.card ↥N))⁻¹ * Real.exp (-Real.log M.det/2) * Real.exp (-u*Gaussian.value M z) := by
       unfold Shield.lens₀; change _ * Real.exp (-_/2- Gaussian.value M (√u • z)) = _
       rw [Gaussian.value_smul,Real.sq_sqrt hu,mul_assoc,←Real.exp_add]; ring_nf
    unfold realProbe; let Y':=Real.sqrt s; rw [ht];
    rw [hE z A (s/q) hs',hE y H s hs.le]
    unfold Gaussian.tilt c; simp only [Fintype.card_coe]; rw [Real.sqrt_div hs.le q, show 1/q=q⁻¹ from one_div q, Real.sqrt_inv,
      show (1-s/q)*Gaussian.value A z=Gaussian.value A z - (s/q*Gaussian.value A z) by ring,Real.exp_sub]
    rw [Real.exp_add,Real.exp_add, show -Real.log A.det/2=-(Real.log A.det/2) by ring,Real.exp_neg,show -(s/q)*Gaussian.value A z=-(s/q*Gaussian.value A z) by ring,Real.exp_neg]
    rw [div_pow, inv_pow]; change (Real.sqrt s)^N.card / (Real.sqrt q)^N.card * _ * _ = _; field_simp [Real.exp_ne_zero _]
    <;> ring
  have ht:=hM 1 zero_lt_one; simp only [Real.sqrt_one,one_pow,mul_one,neg_mul,one_mul] at ht; rw [ratio,hM r hr,ht]; change (Primitive.thermal ((c * Real.exp (-Gaussian.value H y) / _) : ℝ) (-Gaussian.value H y) N.card).run r=_
  change (Primitive.thermal ((c * Real.exp (-Gaussian.value H y)/Real.exp (-Gaussian.value H y)):ℝ) (-Gaussian.value H y) N.card).run r=_
  rw [Primitive.standard _ _ _ _ hr,(mul_div_cancel_right₀ c (Real.exp_ne_zero _)), Fintype.card_coe];
  push_cast; rw [neg_mul]; ring
variable (hÑ:Ñ.scale≠0)
local notation "owner" => Matter.own
include hÑ
lemma ker_eq (i) : ker X R q (k:=k) (η:=η) (W:=W) Y Z V a (r:ℝ) (l:=l) (Ñ:=Ñ) i=
    (ember Cₕ η (scaled R r) W Ñ (take X R q Y Z V a) ((Yₕ).input (key X R q Y Z)) (unclipped X R q Y Z V a r) k l i:ℝ) := by
  unfold ker; exact ember_def _ hR hÑ _ _ hr
lemma monolith_real (p:Molecule S) (A:Cash W X.x μ L Y' P' g T (scaled R r))
    (hh : Canary G a v) (hv : Drivable X a v V) (he: 8*η*X.t≤a/2) (hη:0<η*X.t) :
    (monolith X R q Y Z V a I W η Ñ l p (owner p) r)=
       (Gaussian.tilt (Pond.circuit (lensS I G) X.relating) (r/q) (Pond.swim (lensS I G) Z) *
        rhythm I X V a Ñ p (scaled R r) W η l (Y,Real.sqrt (r/q)•Z):ℝ) := by
  have hz := key_scale X R q Y Z hq hR hr
  have hx:=proceeds Yₕ a A.laws.intake.positive (Real.sqrt (r/q)• Z) V
  change worldZ Cₕ (scaled R r).beta (shutter _ _ _ _ _ _ _ _) = _ at hx
  rw [shutter_eq _ _ _ _ _ _ _ hq hR hr,hz] at hx
  unfold monolith; rw [real_ratio _ _ _ _ _ _ _ hq hR _ hr]
  unfold rhythm recoil; push_cast; rw [← mul_assoc]; apply congrArg₂; · change ((_ * _ : ℝ):ℂ)=_; rw [Complex.ofReal_mul]
  unfold Polar.floating; rw [show course Yₕ a (scaled R r).beta (Real.sqrt (r/q) • Z) V=unclipped X R q Y Z V a r from (shutter_eq X R q Y Z V a hq hR hr),hx]
  let w:=unclipped X R q Y Z V a r
  have hV:=Armor.reeled (R:=scaled R r) (plastic (X:=Cₕ) (conquered Yₕ hh V (key X R q Y Z) ⟨hv.good⟩ hη he) hη) (show Room _ _ _ (Cₕ).x from A.laws.data.room) W Ñ (owner p) l A.laws.intake
  push_cast; exact Finset.prod_congr rfl (fun z hz' => by rw [ker_eq X R q Y Z V a hq hR hr hÑ z]; exact congrArg (fun x:ℝ=>(x:ℂ)) (hV z w).symm)
end YM.UVExt.EnergyRay.Thermal.Core
namespace YM.UVExt.EnergyRay.Thermal.Core
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision ConnectedActivityE6 Mask Coat Raw ConnectedActivityE6.Blaze Silica Vine Flux Polar Gaussian Eider Poll
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {G:Gauge} {c f L:Side} {S: StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio} {P:Teller G}
    (X:ConnectedActivityE6.Coat T F) (R:Rep G f) (q:ℝ) (Y:F.Slice G) (Z:Air f G) (V:Config G c) (a:ℝ)
variable {r g v μ:ℝ} (hq:0<q) (hR:0<R.beta) {k : Finset ℕ} {W η : ℝ} {I:Finset (Bond f)} {Ñ:Precision.ChartRatio G}
    {Y': YM.ConnectedActivityE6.Target G P} {P':Target.Order G W} {l:ℕ}
local notation "Yₕ" => X.wrapY Y
local notation "Cₕ" => vary (X.wrapY Y) V

def veer := steer Yₕ a (fun i=>prune a (key X R q Y Z i)) V
def orbitC (r:ℝ) := sweepZ Cₕ (scaled R r).beta (veer X R q Y Z V a)
def rod i := chandelier (d:=l) (Ñ:=Ñ) (a:=η) (W:=W) (k:=k) Cₕ R (veer X R q Y Z V a)
   ((Yₕ).input (key X R q Y Z)) (orbitC X R q Y Z V a 1) i
def uncluttered (I:Finset _) W η Ñ l (p:Molecule S) (k:Finset ℕ) (t:ℂ) := ratio X R q Y Z V a I t * ∏ i∈p, (rod (l:=l) (k:=k) (W:=W) (η:=η) (Ñ:=Ñ) X R q Y Z V a i).run t
local notation "tr'" => uncluttered
lemma orbit_rescale {r:ℝ} (hr:0<r): orbitC X R q Y Z V a r= Real.sqrt r • orbitC X R q Y Z V a 1 := by
   unfold orbitC sweepZ gStep; dsimp only [scaled]; rw [one_mul,Real.sqrt_mul hr.le,inv_inv,inv_inv,mul_smul]; rfl
local notation "owner" => Matter.own
open Traces
lemma analytic_bundle {ι : Type*} (g:ι→Primitive) (z:Finset ι) : AnalyticOnNhd ℂ (bundled z g) {x:ℂ|0<x.re} := by
   apply DifferentiableOn.analyticOnNhd _ (isOpen_Ioi.preimage Complex.continuous_re)
   have hx:= DifferentiableOn.finsetProd (u:=z) (fun i _=>(g i).differentiable_run)
   rwa [show (∏ i∈z,(g i).run)=(bundled z g) from funext (fun x=> Finset.prod_apply x z _)] at hx

theorem eq_mate {f g:ℂ→ℂ}{α : Set ℝ} {t:ℂ} (hα:IsOpen α) (hC:Convex ℝ α) (hv:AnalyticOnNhd ℂ f (Complex.re⁻¹'α)) (hf:AnalyticOnNhd ℂ g (Complex.re⁻¹'α)) (hfg : ∀ r:ℝ, r∈α → f (r:ℂ)=g (r:ℂ)) (ht:t.re∈α) : f t=g t := by
   let J:=Complex.re⁻¹'α
   have hD:Convex ℝ J:= Convex.linear_preimage hC Complex.reCLM.toLinearMap
   let x:= t.re
   have hx:(x:ℂ) ∈ J := by simpa [x,J]
   apply hv.eqOn_of_preconnected_of_mem_closure hf hD.isPreconnected hx _ ht
   refine Metric.mem_closure_iff.mpr ?_
   obtain ⟨δ,hδ,Hδ⟩:= Metric.isOpen_iff.mp hα x ht
   intro ε (h:ε>0)
   let q:=min (ε/2) (δ/2); have hq:0<q:=lt_min (half_pos h) (half_pos hδ)
   have hh:x+q∈α:=Hδ (Metric.mem_ball.mpr (by simpa [x,Real.dist_eq,abs_of_pos hq] using! ( show q<δ from (min_le_right ..).trans_lt (half_lt_self hδ))))
   have hv' : x+q ≠ x:=by linarith
   change ∃ z:ℂ, z∈_ ∧ _
   refine ⟨(↑(x+q):ℂ),⟨hfg (x+q) hh,fun h=>hv' (Complex.ofReal_injective h)⟩,?_⟩
   · rw [dist_eq_norm]; simp only [Complex.ofReal_add,sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg];
     rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]; exact (min_le_left _ _).trans_lt (half_lt_self h)

variable (hÑ : Ñ.scale≠0)
include hR hq hÑ
lemma reduced_eq (hr:0<r) (p:Molecule S) (A:Cash W X.x μ L Y' P' g T (scaled R r))
    (hh : Canary G a v) (hv : Drivable X a v V) (he: 8*η*X.t≤a/2) (hη:0<η*X.t) (ht:(Cₕ).Noncrystal):
    monolith X R q Y Z V a I W η Ñ l p (owner p) (r:ℂ)=tr' X R q Y Z V a I W η Ñ l p (owner p) (r:ℝ) := by
 have hz:=thatch Yₕ hh V η W p l Ñ ⟨hv.good⟩ hη he ht (show Room _ _ _ _ from A.laws.data.room) A.laws.intake (Real.sqrt (r/q)• Z)
 change Polar.floating Cₕ η _ W Ñ (shutter ..) _ l p= ∏ i∈p,ember Cₕ η _ W Ñ _ _ _ _ _ _ at hz
 rw [key_scale X R q Y Z hq hR hr] at hz
 have he:=monolith_real (l:=l) X R q Y Z V a hq hR I hr hÑ p A hh hv he hη
 rw [he,uncluttered,real_ratio X R q Y Z V a hq hR I hr]; unfold rhythm recoil; push_cast; rw [← mul_assoc]
 apply congrArg₂
 · change _= ((_ * _ : ℝ) : ℂ); rw [Complex.ofReal_mul]
 change (↑(Polar.floating _ _ _ _ _ (shutter _ _ _ _ _ _ _ _) _ _ _):ℂ)=_
 rw [hz]; push_cast; exact prod_congr rfl fun i hi=> (congrArg (fun z=> (ember Cₕ η _ W Ñ _ _ z _ l i:ℂ)) (orbit_rescale X R q Y Z V a hr)).trans (ember_def R hR hÑ i r hr).symm

lemma reductions (U:Set ℝ) (hu:IsOpen U) (hZ:U⊆Set.Ioi 0) (hu':Convex ℝ U) (p:Molecule S) (A: (r:ℝ) → r∈U → Cash W X.x μ L Y' P' g T (scaled R r))
    (hh : Canary G a v) (hv : Drivable X a v V) (he: 8*η*X.t≤a/2) (hη:0<η*X.t) (ht:(Cₕ).Noncrystal) (t:ℂ) (h:t.re∈U) :
    monolith X R q Y Z V a I W η Ñ l p (owner p) t=tr' X R q Y Z V a I W η Ñ l p (owner p) t := by
    let S:=Complex.re ⁻¹' U
    have hS : S ⊆ {z:ℂ|0<z.re}:= fun _ hx=> hZ hx
    have hN : AnalyticOnNhd ℂ (ratio X R q Y Z V a I) S:= by unfold ratio; exact (Primitive.differentiable_run _|>.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)|>.mono hS)
    refine eq_mate hu hu' (hN.mul (analytic_bundle _ p|>.mono hS)) (hN.mul (analytic_bundle _ p |>.mono hS)) (fun r hr=>?_) h
    exact reduced_eq X R q Y Z V a hq hR hÑ (hZ hr) p (A r hr) hh hv he hη ht
end YM.UVExt.EnergyRay.Thermal.Core
namespace YM.UVExt.EnergyRay.Thermal.Core
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision ConnectedActivityE6 Mask Coat Raw ConnectedActivityE6.Blaze Silica Vine Flux Polar Gaussian Eider Poll Shield
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {G:Gauge} {c f L:Side} {S: StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio} {P:Teller G}
    (X:ConnectedActivityE6.Coat T F) (R:Rep G f) (q:ℝ) (Y:F.Slice G) (Z:Air f G) (V:Config G c) (a:ℝ)
variable {r g v μ:ℝ} (hq:0<q) (hR:0<R.beta) {k : Finset ℕ} {W η : ℝ} {I:Finset (Bond f)} {Ñ:Precision.ChartRatio G}
    {Y': YM.ConnectedActivityE6.Target G P} {P':Target.Order G W} {l:ℕ}
local notation "Yₕ" => X.wrapY Y
local notation "Cₕ" => vary (X.wrapY Y) V
local notation "owner" => Matter.own
variable (hÑ : Ñ.scale≠0)

include hq hR hÑ
lemma puncture (hr:0<r) (p:Molecule S) (A:Cash W X.x μ L Y' P' g T (scaled R r))
    (hh : Canary G a v) (hv : Drivable X a v V) (he: 8*η*X.t≤a/2) (hη:0<η*X.t) :
    (∏ i∈p, ker (η:=η) (l:=l) (W:=W) (k:=k) (Ñ:=Ñ) X R q Y Z V a r i)=
       ((Polar.floating Cₕ η (scaled R r) W Ñ (shutter X R q Y Z V a r) k l p:ℝ):ℂ) := by
    have hz := key_scale X R q Y Z hq hR hr; have hx:=proceeds Yₕ a A.laws.intake.positive (Real.sqrt (r/q)• Z) V
    change worldZ Cₕ (scaled R r).beta (shutter _ _ _ _ _ _ _ _) = _ at hx
    rw [shutter_eq _ _ _ _ _ _ _ hq hR hr,hz] at hx; unfold floating
    rw [shutter_eq _ _ _ _ _ _ _ hq hR hr,hx]; let w:=unclipped X R q Y Z V a r
    have hV:=Armor.reeled (R:=scaled R r) (plastic (X:=Cₕ) (conquered Yₕ hh V (key X R q Y Z) ⟨hv.good⟩ hη he) hη) (show Room _ _ _ (Cₕ).x from A.laws.data.room) W Ñ k l A.laws.intake
    push_cast; exact Finset.prod_congr rfl (fun z hz' => by rw [ker_eq X R q Y Z V a hq hR hr hÑ z]; exact congrArg (fun x:ℝ=>(x:ℂ)) (hV z w).symm)
omit Y Z
include hÑ hR hq
lemma shutter_m (hh:Canary G a v) (hv : Drivable X a v V) (A:Cash W X.x μ L Y' P' g T (scaled R r)) (ht:X.width=P'.K): Measurable (fun (t:F.Slice G × Air f G)=>shutter X R q t.1 t.2 V a r) := by
    let U:=A.laws.data
    refine ((steering univ X hh V hv measurable_fst (by exact (show Measurable (fun (t:F.Slice G × Air f G)=> (Real.sqrt (r/q)) • t.2) from Measurable.smul (f:=fun _=> (Real.sqrt (r/q))) (g:= Prod.snd) measurable_const measurable_snd)) A.laws.intake.ready (show ShellAccess _ G _ _ _ _ from by rw [ht]; exact U.access) (scaled R r).beta).2)
variable (hÑ':LocalRatio Ñ)
include hÑ' hR hq
lemma kernel_real_m (hr:0<r) (hh:Canary G a v) (hv : Drivable X a v V) (A:Cash W X.x μ L Y' P' g T (scaled R r)) (ht:X.width=P'.K) (he:8*η*X.t≤a/2) (hη:0<η*X.t) i : Measurable (fun (t:F.Slice G × Air f G)=>ker (η:=η) (l:=l) (W:=W) (Ñ:=Ñ) (k:=k) X R q t.1 t.2 V a r i) := by
    let U:=A.laws.data
    have hz (t:F.Slice G × Air f G):= puncture (η:=η) (l:=l) (W:=W) (Ñ:=Ñ) (k:=k) X R q t.1 t.2 V a hq hR hÑ hr {i} A hh hv he hη
    simp only [prod_singleton] at hz
    simp_rw [hz]; exact Complex.measurable_ofReal.comp (collectionB X (show ShellAccess _ G _ _ _ _ from by rw [ht]; exact U.access) A.laws.intake hÑ' measurable_const measurable_fst (shutter_m (P':=P') (Ñ:=Ñ) X R q V a hq hR hÑ hh hv A ht) _ _ _ _)
lemma ratio_real_m (hr:0<r)(hh:Canary G a v) (hv : Drivable X a v V) (A:Cash W X.x μ L Y' P' g T (scaled R r)) (ht:X.width=P'.K): Measurable (fun (t:F.Slice G × Air f G)=>ratio X R q t.1 t.2 V a I (r:ℝ)) := by
 let z (t: F.Slice G × Air f G):= t.2; let Y z:= X.wrapY (Prod.fst (z:F.Slice G × Air f G)); let K:= lensS I G; let ρ:=r/q; let β:=(scaled R r).beta
 have hC:=A.laws.data
 simp_rw [real_ratio X R q _ _ V a hq hR _ hr]; refine Complex.measurable_ofReal.comp (Measurable.mul (f:=fun t=>Gaussian.tilt (Pond.circuit K X.relating) ρ (Pond.swim K (z t))) ?_ ?_)
 · unfold tilt; refine measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul ?_)); exact (value_cont _).measurable.comp ((Pond.swim_m K).comp measurable_snd)
 unfold scalp; let z' t:=course (Y t) a β (Real.sqrt ρ • z t) V
 apply Measurable.mul (f:=fun t=> jacL I _ a β _ _)
 · let b:=A.laws.intake
   exact ((steering I X hh V hv measurable_fst (by exact (show Measurable (fun (t:F.Slice G × Air f G)=> (Real.sqrt (r/q)) • t.2) from Measurable.smul (f:=fun _=> (Real.sqrt (r/q))) (g:= Prod.snd) measurable_const measurable_snd)) b.ready (show ShellAccess _ G _ _ _ _ from by rw [ht]; exact hC.access) β).1)
 apply Measurable.div (f:=fun t=>lens₀ (Pond.circuit K (vary X V).relating) (Pond.swim K (z' t)))
 · exact Shield.bulbB (S:=fun t=> Pond.circuit K (vary X V).relating) (fun i j=> (measurable_const)) ((Pond.swim_m K).comp (shutter_m X R q V a hq hR hÑ hh hv A ht)) -- maybe `hÑ ht`
 exact Shield.bulbB (S:=fun t=> Pond.circuit K X.relating) (fun i j=> (measurable_const)) ((Pond.swim_m K).comp (Measurable.smul (f:=fun (_:F.Slice G × Air f G)=>Real.sqrt ρ) measurable_const measurable_snd))

lemma pattern_m (i:Head S) : Traces.UniformForm (fun t:F.Slice G × Air f G=> chandelier (k:=k) (a:=η) (d:=l) (Ñ:=Ñ) (W:=W) (vary (X.wrapY t.1) V) R
    (take X R q t.1 t.2 V a) ((X.wrapY t.1).input (key X R q t.1 t.2)) (swept X R q t.1 t.2 V a R.beta) i) := by
       unfold Traces.UniformForm; cases i with
       | inl z => left; exact ⟨seedPower X z,fun t=> ⟨_,_,(show (Primitive.thermal _ _ (seedPower (vary (X.wrapY t.1) V) z)) = Primitive.thermal _ _ (seedPower X z) from congrArg (Primitive.thermal _ _) rfl)⟩⟩
       | inr i=> rcases i with i|i|i
                 · left; refine ⟨0,fun t=> ⟨_,0,rfl⟩⟩
                 · dsimp only [chandelier]; split; next h=>right; exact fun t=>Exists.intro _ rfl
                   left; exact ⟨0,fun t=>⟨_,_,rfl⟩⟩
                 left; exact ⟨0,fun t=>⟨_,_,rfl⟩⟩
lemma one_kernel (hr:0<r) {s:ℝ} (hs:0<s) (hk:r≠s) (U:ℂ) (hh:Canary G a v) (hv : Drivable X a v V) (A:Cash W X.x μ L Y' P' g T (scaled R r)) (B:Cash W X.x μ L Y' P' g T (scaled R s)) (ht:X.width=P'.K) (he:8*η*X.t≤a/2) (hη:0<η*X.t) (i:Head S) : Measurable (fun (t:F.Slice G × Air f G)=>ker (l:=l) (η:=η) (W:=W) (k:=k) (Ñ:=Ñ) X R q t.1 t.2 V a U i) := by
  exact Traces.UniformForm.sample _ (pattern_m (η:=η) (Ñ:=Ñ) (W:=W) (l:=l) (k:=k) X R q V a hq hR hÑ hÑ' i) hr hs hk (kernel_real_m _ _ _ _ _ hq hR hÑ hÑ' hr hh hv A ht he hη i) (kernel_real_m _ _ _ _ _ hq hR hÑ hÑ' hs hh hv B ht he hη i) U
lemma irrespective (hr:0<r) {s:ℝ} (hs:0<s) (hk:r≠s) (U:ℂ) (hh:Canary G a v) (hv : Drivable X a v V) (A:Cash W X.x μ L Y' P' g T (scaled R r)) (B:Cash W X.x μ L Y' P' g T (scaled R s)) (ht:X.width=P'.K) (he:8*η*X.t≤a/2) (hη:0<η*X.t) (p:Molecule S): Measurable (fun (t:F.Slice G × Air f G)=> monolith X R q t.1 t.2 V a I W η Ñ l p k U) := by
    apply Measurable.mul (f:=fun t: F.Slice G × Air f G=>ratio X R q t.1 t.2 V a I U) (g:=fun t=> ∏ i ∈ p, ker (k:=k) (l:=l) (Ñ:=Ñ) (W:=W) (η:=η) X R q (Prod.fst t) (Prod.snd t) V a U i)
    · exact Traces.thermal_measurable (k:=(lensS I G).card) _ (fun t=> ⟨_,_,rfl⟩) hr hs hk (ratio_real_m _ _ _ _ _ hq hR (I:=I) hÑ hÑ' hr hh hv A ht) (ratio_real_m _ _ _ _ _ hq hR (I:=I) hÑ hÑ' hs hh hv B ht) U
    exact Finset.measurable_prod p (fun i _=> one_kernel X R q V a hq hR hÑ hÑ' hr hs hk U hh hv A B ht he hη i)
end YM.UVExt.EnergyRay.Thermal.Core
