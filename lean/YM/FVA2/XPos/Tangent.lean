import YM.FVA2.XPos.Tree
import YM.FVA2.Laplace.Bare
import YM.FVA2.Change.Prescription
/-! # XSpace.Tree realization of its Orb Wilson weights at finite regulator -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.XPos
open Function Set Filter Finset Lattice Wilson
open Orbit Orbit.Screen Orbit.Grove Laplace XSpace
open PertExtension PertExtension.Orb Series Radial GaussianScore
open MeasureTheory Measure PowerSeries
open FormalOPE.RG10.MultiGauge Splice
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {R:XSpace.Period}(T:R.Tree)
local notation "E"=> T.Field G
local notation "V"=> Complement G (Marked T)
local notation "J"=> shrub G (Marked T) ( valid T )
local notation "F"=> XSpace.Bare.relative (G:=G) T
set_option quotPrecheck false
local notation "L"=> (screen T G).toContinuousLinearEquiv
lemma creed : Jacobs (⇑(screen T G)) (screen T G).toContinuousLinearEquiv:= ⟨ ( L ).contDiff.contDiffAt, map_zero _,ContinuousLinearEquiv.fderiv ( L )⟩
lemma genuine_action : T.action (G:=G)= (J).price ∘ (screen T G):= by
 funext i; rw [Function.comp_apply,Screen.price,shrub_down,screen_path]; rfl
lemma coiff : ∀ᶠ p:E in 𝓝 0, F p=(J).weight ( L p ):= by
 let θ := screen T G; have he : Tendsto θ (𝓝 0) (𝓝 0):= (creed T).forwards
 filter_upwards [he.eventually (shrub_cost (G:=G) (Marked T) ( XPos.valid T )),eventually_all.mpr (fun i:T.Free=> (continuous_apply i|>.tendsto (0:E)).eventually ((spin_even (G:=G)).and (MS.Bare.Maurer.real_ratio (Bare.chart_ratio G))))] with x hx hp
 rw [show (J).weight ( L x )=_ from hx, Bare.relative, ← Equiv.prod_comp (portal T), hair]; apply Finset.prod_congr rfl; intro i _; obtain ⟨hv,hu⟩:= hp (portal T i); rw [ show (Bare.chart G).J _= _ from hu ]; change _= LocalH.spin G ( flux G i.val ( x (portal T i) )); unfold flux; split; rfl; exact hv.symm
lemma eve (R:XSpace.Period) : Even R.side.val:= even_iff_two_dvd.mpr R.even
local notation "K" => Config G R.side
variable {O: Config G R.side → ℝ} (h:Orb.PreTest O)
lemma speaks : O ∘ T.links= (J).play O ∘ screen T G:= by funext i; rw [Function.comp_apply, show ((J).play O ∘ screen T G) i= _ from congr_arg O (screen_path (G:=G) T i)]; -- orientation
include h
lemma hears : ContDiffAt ℝ ∞ (O ∘ T.links) 0:= by rw [speaks]; refine ( ContDiffAt.comp (f:=( L )) 0 ?_ ( L ).contDiff.contDiffAt); rw [map_zero]; exact hearing (J) (eve ..) h
variable (μ:Measure (T.Field G))[μ.IsAddHaarMeasure]
theorem price_origin : pricetag μ F T.action (O ∘ T.links)= PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= by
 let S:= J; let ν:= addHaar (G:= V); have p : Steep S.price:= S.viable (eve ..); let k:= Jacobs.amount L μ ν; let D := S.weight; let x := (creed (G:=G) T); let θ := screen T G; have hy : T.action (G:=G)=ᶠ[𝓝 0] S.price∘θ:= Eventually.of_forall (congr_fun (genuine_action T)); have ht : ∀ᶠ y in 𝓝 0, F y=meter L (fderiv ℝ (⇑θ) y) * D (θ y):= by
    filter_upwards [coiff (G:=G) T] with y hv; rw [ show fderiv ℝ (⇑θ) y=( L ).toContinuousLinearMap from ContinuousLinearEquiv.fderiv ( L ),meter_self,one_mul]; exact hv
 rw [ ← S.genuine (eve .. ) ν h ]; unfold pricetag Screen.charge; refine shed2 k ?_ ?_ (Laplace.ready ν p S.head) (Jacobs.pay_pos ..); all_goals unfold Laplace.rows
 · rw [ x.moment_change μ ν (K':=S.play O * D) p hy (( S.hearing (eve ..) h ).mul ( S.analytic.of_le le_top)), Laplace.up]; filter_upwards [ht] with y h; rw [ Pi.mul_apply,h,Pi.mul_apply ]; rw [show (O ∘ T.links) y=_ from congr_fun (speaks (O:=O) T) y];  apply mul_left_comm
 rw [ x.moment_change μ ν p hy (S.analytic.of_le le_top) ht,Laplace.up]

omit h
lemma jet_amount (v:E) : jet T.action 2 v= T.quadratic G v v/2:= by
 unfold jet; rw [show (fun _ : Fin 2 => v) = ![v,v] from funext (fun i => by fin_cases i <;> rfl), (T.action_jets G).2.2]; norm_num [Nat.factorial]; ring
variable (G) in
def Qx : Law (T.Field G) where
 P:= T.quadratic G
 turns := T.symmetric
 slope := by
    obtain H:= ( creed (G:=G) T ).steepens ( (J).viable (eve ..) ); rw [ ← genuine_action T ] at H; obtain ⟨c,hc,ht⟩:=H.gap; simp_rw [jet_amount] at ht; exact ⟨c,hc,ht⟩
 smooth := by
    rw [show (fun x:T.Field G => T.quadratic G x x)= fun x:T.Field G => (2:ℝ) * Radial.jet T.action 2 x from funext (fun x => by rw [jet_amount]; ring)]; unfold jet; exact continuous_const.mul (continuous_const.mul ((iteratedFDeriv ℝ 2 T.action (0:E)).coe_continuous.comp (continuous_pi fun _=> continuous_id)))
local notation "X"=> T.action (G:=G)
lemma kern_orig : (Qx G T).kern = Radial.kernel X:= by funext y; unfold Law.kern Radial.kernel; rw [jet_amount T y,neg_div]; rfl
lemma read_Q (i j:T.Key G): (Bare.Q T G).cov i j= Wick.bosonMatrix (Qx G T) (T.basis G) i j := by
 let M:= T.covariance G; let fc:=Complex.ofRealHom; let t:= Wick.bosonHessian (Qx G T) (T.basis G); have hu : t=(T.hessian G).map fc:= by ext i j; simp only [Matrix.map_apply,XSpace.Period.Tree.hessian,LinearMap.BilinForm.toMatrix_apply]; rfl
 have hh : t * M.map fc=1:= by rw [hu,← Matrix.map_mul (f:=fc),show T.hessian G * M=1 from T.covariance_val G, Matrix.map_one fc (map_zero fc) (map_one fc)];
 have he:= left_inv_eq_right_inv (mul_eq_one_comm.mpr hh) ( Wick.boson_ok ( Qx G T ) ( T.basis G ) ); exact congr_fun (congr_fun he i) j
include h
lemma prices : PowerSeries.mk (Orb.diag (Orb.restrictedO O))=enjoy (Qx G T) μ (Stack.rise (O ∘ T.links)) (Laplace.sink F T.action):= by
 rw [← price_origin T h μ]; exact receipt μ (Qx G T) (kern_orig T) (Bare.relative_one T G) ((Bare.relative_smooth T G).of_le le_top) (hears T h)
end YM.FVA2.XPos
