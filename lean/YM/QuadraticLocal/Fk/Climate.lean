import YM.QuadraticLocal.Fk.Clearance
import YM.Comparison.RG02.Bulk.Spur
/-!
# Explicit equality of unmarked Fk phase layers to Response tokens

Every power of `t` before revaluation via PathData. Includes leading t^-2 distinct at empty
T.Fore.J. No pressure.L.Cos gauge choices hidden. Orientation using dream law + FACTORIAL
normalization (use to get natural coupling coefficients).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Fk.Dress
open Filter Function Finset Lattice Wilson RG Pressure RG.Supply Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat Lapis
open AllOrder AllOrder.Floe AllOrder.Response Extra.Iteration Tree Blaze MeasureTheory
open Comparison.RG02 Comparison.RG02.Bulk Assembly Next.SectorChange
open Marker Extra.Trajectories Multi Push Push.Uniform Laplace Laplace.SigmaP
open PertExtension PertExtension.Series PertExtension.GaussianScore
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {f c:Side}{V:Type}[DecidableEq V] {J:Census V} {S:StepData c f}
local notation "X"=> Apex c G
variable (F : Forest S.ratio) (k:S.Choices) {p:Clip}{R:PathData G}{O:ChartRatio G}
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "E"=> Apex c G × Poll.Body (Precision.Key F G)
local notation "χ"=> ℝ× (Apex c G × Poll.Body (Precision.Key F G))
local notation "v"=> weld (Precision.Key F G)
local notation "w"=> tint G (Exterior.Body 1 c)
local notation "r"=> (Precision.Key F G → ℝ)
variable (M:Layout G)(A:Finset Age)
variable (h:Legal A M)
variable (C:Bulk.Kernel S p R O)
variable {a C₀ Λ:ℝ}{N:ℕ} (F' : (Bid.Dir G c) → AxisChart G F) (U : Push.Uniform.Before G a C₀ S.patch.J S.kernel (N+3)) (hT:U.Service F p R F')
variable (hG:Bid.Larger (G:=G) S)(hQ:R.Bounds p a C₀ Λ)
local notation "K"=> Laplace.startup F O k R p U hG hQ hT C.ratio
local notation "K0"=> augment F M A K h
set_option quotPrecheck false
local notation "Γ"=> Response.castle (K0).hard (K0).quiet (K0).pay.steer
local notation "C'"=> C.covariance F k
local notation "Cost"=> (Gaussian.coat (C'))
local notation "μ"=> (volume: Measure Y)
local notation "Ω₁"=> (Impulse (fderiv ℝ (K0).quiet 0) (K0).high (K0).paid)
variable (D:Bulk.Colors J G f)
local notation "R₀"=> Fk.grant M A D
local notation "U₀" x:max y:max=> Bulk.translated C F (w x) y
local notation "B₀"=> trim G F
local notation "A₀"=> Bulk.geometric C F k R₀
-- geometry coupons.K.Weight.
include h in
lemma spins : ContDiffAt ℝ ω A₀ 0:= (stone_smooth C F k).add (show ContDiffAt ℝ ω (fee C F R₀) 0 from
   ((contDiffAt_fst.pow 2).mul ((officer_known C F).smooth)).add (joint_receipt S F (Fk.level M A h)).smooth)
open Radial
-- Real/Pol.Rule.Value.Comparison at all n≥zero. No cutoff cloud.S or smaller coupon.
lemma quilt (x:X)(y:Y)(i:ℕ) : layers (A₀) i (U₀ x y.ofLp)= (Ω₁) i (x,y):=by
   by_cases he:i=0; · subst i; rw [Radial.Stationary.layers_zero,Impulse,win0]; rfl
   let T := B₀; let z:= (colorful (fderiv ℝ (K0).quiet 0) (x,y)); let G₀:= (A₀ ∘ T.toContinuousLinearMap); let L:=z.2; let ν (q:χ):= mist F O R q.2; let s:= Fintype.card F.Free * Real.log O.scale;
   have hz:z=(1,L):=rfl
   have hm: ContDiffAt ℝ ω (mist F O R) 0:= mist_nice F O R p U hQ C.ratio
   have hν: ContDiffAt ℝ ω ν 0:= hm.comp (f:=Prod.snd) (0:χ) contDiffAt_snd; let Vp (q:χ):= q.1^2*ν q
   have hp : ContDiffAt ℝ ω Vp 0:= (contDiffAt_fst.pow 2).mul hν
   have hη : ContDiffAt ℝ ω (K0).high 0:= (K0).pay.activity
   have hu: U₀ x y.ofLp=T z:= (placed F k C F' U hT x y).symm; let W : χ→ℝ:= fun _=>s
   have hW: G₀=ᶠ[𝓝 0] (K0).high+Vp:= high_geom F k M A h D C F' U hT hG hQ; -- shadow
   have ht : Radial.jet Vp (i+2) z=Radial.jet ν i z:=by
      rw [hz,favor_exp (mist F O R) hm 1 L (i+2) 2]; change _= Assembly.jet ((mist F O R)∘ (ContinuousLinearMap.snd ℝ ℝ E)) i (1,L);
      rw [if_pos (by omega),one_pow,one_mul,show i+2-2=i by omega,Assembly.jet_continuous_right _ (hm.of_le le_top)]; rfl
   have hQ': Radial.jet A₀ (i+2) (U₀ x y.ofLp)= Radial.jet (K0).high (i+2) z+Radial.jet ν i z:=by
      rw [hu, show Radial.jet A₀ (i+2) (T z)= Radial.jet G₀ (i+2) z from (Assembly.jet_continuous_right T.toContinuousLinearMap ( (spins F k M A h C D).of_le le_top) z).symm]
      have he : Radial.jet G₀ (i+2)= Radial.jet ((K0).high+Vp) (i+2):=by unfold Radial.jet; funext q; rw [(hW.iteratedFDeriv ℝ (i+2)).self_of_nhds]
      rw [he,Laplace.jet_add hη hp,ht]
   unfold Radial.layers Impulse; rw [if_neg he, add_zero,hQ',win_atn _ he]; change _= Radial.jet (Real.log ∘ (K0).paid) (i+0) z - Radial.jet (K0).high (i+2) z
   have hz₀:Radial.jet (Real.log ∘ (K0).paid) i z + Radial.jet ν i z= 0:= by
     rw [← Laplace.jet_add (f:=Real.log ∘ (K0).paid) (((K0).pay.ample.log (minted (C:=C) ..|>.ne'))) hν, show (Real.log ∘ (K0).paid)+ν=W from ?_]; swap; · rw [pay_log F k M A h C F' U hT hG hQ]; exact funext fun q=> sub_add_cancel ..
     unfold Radial.jet; rw [congr_fun (iteratedFDeriv_const_of_ne he s) (0:χ)]; simp
   simp only [add_zero]; linarith
-- computation. Equality real.L
local notation "Ξ" n:max=> Radial.expsum (Radial.layers (A₀)) n n
-- pointwise generator
lemma pure_exp (x:X)(y:Y)(i:ℕ) : (Ξ i) (U₀ x y.ofLp)= EXP Ω₁ i (x,y):=by
   let f:= U₀ x y.ofLp; have he:=quilt F k M A h C F' U hT hG hQ D x y; let a := Ω₁; let p':=fun i=> a i (x,y)
   have hh: PositionX.Jet.light p' := (show _ from congr_fun (win0 (token (fderiv ℝ (K0).quiet 0) (K0).high (K0).paid)) _); -- maybe `congr_fun`
   have hN (j:ℕ)(i:ℕ) : PertExtension.Series.Zone.TaylorPow (Radial.layers A₀) j i f= xpow p' j i:= by
       induction j generalizing i with
       | zero=> rw [power_zero]; rfl -- just if i=0
       | succ j ih=> rw [Zone.TaylorPow, Response.power, plus_sum]; unfold Zone.mul; apply sum_congr rfl fun i _=> ?_; rw [ih]; exact congr_arg₂ (·*·) rfl (he _)
   change (Ξ i) f=expS p' i; rw [exp_pay hh le_rfl, onward,Finset.sum_apply]; unfold expsum; apply sum_congr rfl fun j _=> ?_; rw [hN]; rfl
variable [Fintype V]
-- natural coeff no denominator, explicit leading. integral is all vertical Poll sites and GP charge.
set_option maxHeartbeats 200000 in
lemma raw (x:X)(n i:ℕ) (hi:i≤ n) : ((Order.observe J n (Bulk.Fk C F k R₀ (w x) n) i).part J.quiet)= Complex.ofReal ((climate Γ μ Ω₁ i x)):=by
   let f0:= Bulk.Fk C F k R₀ (w x) n; let y:= (fderiv ℝ (orbit F F') 0)
   let g(z:r):=(Ξ i) (U₀ x z); let d : Precision.Key F G→ℝ:=0; let t : ℂ := ↑(Nat.factorial i);
   have hb:= Assembly.order_read (Bulk.stage C F (w x)) (Bulk.hinge (G:=G) F) (Fk.grant M A D).power (Bulk.markFn S F (Fk.grant M A D)) A₀ (C.covariance F k) (C.symm F k) (C.positive F k) J.quiet hi
   simp only [Assembly.insideMoment,Bulk.clear] at hb
   have hz : ((Order.observe J n (Bulk.Fk C F k R₀ (w x) n) i).part J.quiet)= ↑(∫ z:r,g z ∂Gaussian.cloud C'):= hb.trans integral_complex_ofReal
   let H:=gaussSkin (Precision.Key F G)
   have he: (g ∘ H)=(fun y:Y=> EXP Ω₁ i (x,y)):= funext (fun y=> pure_exp F k M A h C F' U hT hG hQ D x y i)
   have hv : climate Γ μ Ω₁ i x= (Γ).average μ (g ∘ H):= by rw [he]; rfl
   exact hz.trans (congr_arg Complex.ofReal ((hv.trans (bill F k M A h C F' U hT hG hQ g)).symm))
end YM.QuadraticLocal.Fk.Dress
