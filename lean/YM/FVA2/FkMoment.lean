import YM.FVA2.RayScatter
import YM.RGComparison.Core16.Silk.Roll

/-!
# RGComparison/Core16 Fk ray formula equals the normalized open-coarse-field kernel

General real Lawn equation, instantiated for *every P.Steady*, but does not *require* the
meter/frontier incl in Steady. For the inversion torus next construct the actual parameters,
which differ from those used in e.g. full-volume analytic comparison: use full quotient
penalty and orbit marks. Use ψ for Fk tag.Here prove equality to RG10 normalized kernel with
its `J(h)` jac.Actueval. Conditional vacuum, includes `rays` and all coarse variables. Only
normalize scalar proportion factor AFTER full conditional step, including the full field
power series. Pointwise at geometry---not claiming analytic estimates for lattice FK.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.RayScatter.Fork
open Filter Topology Function PowerSeries MeasureTheory Lattice FormalOPE.RG10
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router
open FormalOPE.RG10.OpenSlots FormalOPE.RG10.Sync
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Precision
open GaussianScore RGComparison.Core16 RGComparison.Core16.Therm RGComparison.Core16.Lumen
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{S:Side}{ι k T A D L I K:Type}[Fintype ι] [Fintype k]
variable {F: Type} [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {X:Shelf G A D}(P:Planet X S ι k T)(Z:ChartRatio G)(hZ:LocalRatio Z)
local notation "Eκ"=> Fk.Panel G ι
local notation "μ"=> tangent G ι
variable {b:ℝ}{p:Fk.Panel G ι × F→ℝ}
    (h:ContDiffAt ℝ ω p 0)(Q:Quadratic (Fk.Panel G ι × F))(hy:∀ v,Q.flourish v=2*jet p 2 v)
    (hp:(Quadratic.core Q).RespectsPrice)(y:F)

local notation "J"=> (jacobian Z (U:=ι))
local notation "Ξ"=> Stack.overhead Z ι
local notation "Jκ"=> (J ∘ (LinearMap.fst ℝ Eκ F))

-- only assume relation of elementary field charts p,y.Lexponent to RG10 cost; not assuming any price equality. Not hidden
include h hZ

def interaction (p:Fk.Panel G ι×F→ℝ) : Ticket (Fk.Panel G ι × F):= boost (LinearMap.fst ℝ Eκ F) (OpenSlots.tissue Z ι) * Stack.exponential (Stack.advancing p)
omit h
lemma inclineI : incline (interaction Z p):= pool (preserve_boost _ (awake hZ)) (Stack.initial _)
local notation "W0"=> (interaction Z p)
local notation "xF"=> (LinearMap.fst ℝ Eκ F)
lemma Hhold : ContDiffAt ℝ ω Jκ 0:= OpenSlots.leaned xF (Chart.Ratio.jacobian_smooth hZ)
lemma smear_abs : Stack.roll Ξ * W0= Stack.rise Jκ * Stack.exponential (Stack.advancing p):= by
    unfold interaction OpenSlots.tissue; rw [map_mul, boost_c, MarkovChain.Vault.climbing xF ((Chart.Ratio.jacobian_smooth hZ).of_le le_top)]; rw [ ← mul_assoc, ← mul_assoc ]; unfold Stack.roll; rw [ ← map_mul, ← map_mul, show jacobian Z (0:Eκ)=Ξ from rfl, mul_inv_cancel₀ (Stack.official (I:=ι) hZ).ne',map_one,map_one, one_mul ]; -- orientation

section helper
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (Q:Quadratic (E×F))(hp:(Quadratic.core Q).RespectsPrice)
variable [MeasurableSpace E][BorelSpace E](τ:Measure E)[Measure.IsAddHaarMeasure τ]
omit hZ
omit [FiniteDimensional ℝ F] in
lemma roll_μ (c:ℝ)(V:Ticket (E×F)): Q.uptake τ hp (Stack.roll c * V)= Stack.roll c * (Q.uptake τ hp V):= by
    apply PowerSeries.ext; intro i; unfold Quadratic.uptake throughPrice Stack.roll; rw [coeff_C_mul]; simp only [ AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe, coeff_C_mul, ← Algebra.smul_def, map_smul ]
end helper

local notation "xη"=>Q.uptake μ hp
local notation "ν"=>Stack.read y
variable {ψ:(L→G.Color)→ℝ}(v:Stuff G ι L)
    (hc:Fk.rise P =ᶠ[𝓝 0] charge p b y)
include hc hy h hZ
local notation "Tκ"=> basePower Q hp y μ b * Ξ

lemma uniform_nil : PowerSeries.mk (Fk.birth P Z) = C (Tκ) * ( ν ( xη W0 ) ):= by
    have he : Fk.cap Z (Fk.vacant (G:=G) (ι:=ι)) (fun _=>1)= Jκ ∘ recover y:= by
        funext v; unfold Fk.cap; rw [mul_one]; rfl
    rw [Fk.birth, Fk.harvest, he, stamp_protect μ _ _ ( Filter.EventuallyEq.refl .. ) hc, RayScatter.absolute b h Q hy hp y μ _ (Hhold Z hZ),← smear_abs Z hZ, roll_μ,map_mul, map_mul, Stack.rollThrough,mul_assoc]; -- stamp_protect also visible?

lemma cover_all (u:Fk.Panel G ι× F→ℝ)(hv:(ψ ∘ Fk.scene v) =ᶠ[𝓝 0] u ∘ recover y)(he:ContDiffAt ℝ ω u 0): PowerSeries.mk (Fk.harvest P Z v ψ)= C (Tκ) * ν ( xη ( W0* Stack.rise u) ):= by
    let V: ℝ × Eκ→ℝ:= (Jκ * u) ∘ recover y; have hP: Fk.cap Z v ψ =ᶠ[𝓝 0] (Jκ * u) ∘ recover y:= hv.mono fun x hx=> congr_arg (fun a:ℝ=> J (x.2)*a) hx
    rw [ Fk.harvest, stamp_protect μ _ _ hP hc, absolute b h Q hy hp y μ (Jκ * u) (ContDiffAt.mul (Hhold Z hZ) he), Stack.rise_mul ((Hhold Z hZ).of_le le_top) (he.of_le le_top), mul_right_comm, ← smear_abs Z hZ, mul_assoc,roll_μ, map_mul (Stack.read y),map_mul PowerSeries.C, Stack.rollThrough,mul_assoc ]

include hp
lemma positive : 0 < Fk.birth P Z 0:= by
    rw [← coeff_mk 0 (Fk.birth P Z), uniform_nil (P:=P) _ hZ h Q hy hp y hc, coeff_C_mul,coeff_zero_eq_constantCoeff_apply,constantOne, mul_one ]; exact mul_pos (base_power_pos b Q hp y μ) (Stack.official (I:=ι) hZ)
where constantOne : constantCoeff ( ν ( xη W0 ) )=1:= by rw [ ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Stack.reading_term, PowerSeries.coeff_zero_eq_constantCoeff_apply, Quadratic.upright Q μ hp (inclineI (p:=p) Z hZ) ]; rfl

lemma complete_select (u:Eκ × F→ℝ)(hv:(ψ ∘ Fk.scene v) =ᶠ[𝓝 0] u ∘ recover y)(he:ContDiffAt ℝ ω u 0): PowerSeries.mk ( Fk.valuation P Z v ψ )= ν ( Q.fit μ hp (Stack.rise u) W0 ):= by
    let f:= Fk.harvest P Z v ψ; let g:= Fk.birth P Z; have hz:constantCoeff (PowerSeries.mk g)≠0:= by rw [constantCoeff_mk]; exact ( Fork.positive P Z hZ h Q hy hp y hc ).ne';
    rw [show mk ( Fk.valuation P Z v ψ )=PowerSeries.mk f* (PowerSeries.mk g)⁻¹ from PowerSeries.ext (fun i=> PowerSeries.coeff_mk ..)]; symm; apply ( PowerSeries.eq_mul_inv_iff_mul_eq hz ).mpr; unfold f g; rw [cover_all P Z hZ h Q hy hp y v hc u hv he, uniform_nil P Z hZ h Q hy hp y hc,mul_left_comm _ (C _),← map_mul, mul_comm (Q.fit _ _ _ _), Quadratic.fit_eq _ _ _ _ _ (inclineI Z hZ)]

theorem perch (u:Eκ × F→ℝ)(hv:(ψ ∘ Fk.scene v) =ᶠ[𝓝 0] u ∘ recover y)(he:ContDiffAt ℝ ω u 0)(a:ℕ): PowerSeries.mk (Fk.read P Z v ψ a)= Stack.drop a ( ν ( Q.fit μ hp (Stack.rise u) W0 )):= by rw [ ← complete_select P Z hZ h Q hy hp y v hc u hv he ]; apply PowerSeries.ext; intro i; simp [Fk.read, Stack.drop]
-- irrespective of any cost estimates on `Fk.Steady`, its positive Hessian supplies
-- exactly the conditional frame.Valid also e.g. full NON-quotient Planet (separate kernels).
omit hy h hp hc
section fate
variable (v:Stuff G ι L)
local notation "σ"=> Eκ × ℝ
local notation "↻"=> Prod.swap (α:=Eκ) (β:=ℝ)
local notation "Aκ"=> Fk.rise P ∘ ↻
local notation "Sν"=> ψ ∘ Fk.scene v ∘ ↻

variable [Fintype T][Fintype D](Pgood:P.Steady)
def TrueLaw : Quadratic (Eκ × ℝ):= Quadratic.genesis 1 ( Fk.rise P ∘ ↻ )
omit hZ
include Pgood
private lemma A_hot : ContDiffAt ℝ ω (Aκ) 0:= (Fk.bump_hot Pgood).comp (0:Eκ×ℝ) (contDiffAt_snd.prodMk contDiffAt_fst) -- parameter optional
omit Pgood [Fintype T] [Fintype D] in
lemma A_quad (x:Eκ × ℝ): (TrueLaw P).flourish x=2* jet Aκ 2 x:= by rw [ TrueLaw, Quadratic.native, show term 1 0= (1:ℝ) from coeff_zero_one, one_mul ]
theorem A_respects : (TrueLaw P|>.core).RespectsPrice:= by
     let Q:=TrueLaw P|>.core; let f: σ→ℝ:= Aκ; have hx (x:Eκ): Q.flourish x/2= jet (Fk.rise P) 2 (0,x):= by
         have he:= A_quad P (x,0); let v: σ≃ₗ[ℝ] Fk.Door G ι:=LinearEquiv.prodComm ℝ Eκ ℝ
         rw [show Prod.swap (α:=Eκ) (β:=ℝ)= v.toContinuousLinearEquiv.toContinuousLinearMap from rfl, GermLaplace.jet_pull (m:=v.toContinuousLinearEquiv.toContinuousLinearMap) _ ((Fk.bump_hot Pgood).of_le le_top)] at he; change (TrueLaw P).flourish (x,0)/2=_; rw [he]; change (2*jet (Fk.rise P) 2 (0,x))/2=_; ring
     have hq : ∃ (c:ℝ), 0<c ∧ ∀ x:Eκ,c*‖x‖^2 ≤ Q.P x x/2:= by
          obtain ⟨c,hc,h⟩:= Fk.prepared Pgood; refine ⟨ c,hc,fun x=>?_⟩; change _ ≤ Q.flourish x/2; rw [hx]; simpa using h (0,x)
     refine ⟨ ⟨ Q.P,Q.side,hq, ?_⟩,rfl ⟩
     rw [ show (fun x=> (Q.P x) x)= (fun x=> (2:ℝ)* jet (Fk.rise P) 2 (0,x)) from funext fun i=> (by obtain h:=hx i; unfold Quadratic.flourish at h; linarith) ]; exact continuous_const.mul (( Smooth.continuousJet .. ).comp ( continuous_const.prodMk continuous_id ))

omit Pgood in
lemma read_hold (he:ContDiffAt ℝ ω (ψ∘ Fk.scene v) 0) : ContDiffAt ℝ ω (Sν) 0:= he.comp (f:= ↻) (0:Eκ×ℝ) (contDiffAt_snd.prodMk contDiffAt_fst)
include hZ
-- digital earnings for this ray. Uses the normalized log.Bucket matching
-- incl motion of the mean, which depends on the prescribed ray.C.Mark scaling after.
local notation "δ"=> TrueLaw P
local notation "Wρ"=> interaction Z Aκ
local notation "ρ"=> A_respects P Pgood
local notation "θ"=> (δ).fit μ ρ
lemma ray_value (he: ContDiffAt ℝ ω (ψ ∘ Fk.scene v) 0)(a:ℕ): PowerSeries.mk (Fk.read P Z v ψ a) = Stack.drop a (Stack.read (1:ℝ) (θ (Stack.rise Sν) Wρ)):= by
      have hU : charge Aκ 0 1= Fk.rise P:= funext fun u=> by rcases u with ⟨t,v⟩; simp [charge,RayScatter.tax,recover];
      apply perch P Z hZ (A_hot P Pgood) (δ) (A_quad P) ρ 1 v (hU.symm.eventuallyEq); · refine Filter.Eventually.of_forall (fun x=>?_); change ψ ( Fk.scene v x )= ψ (Fk.scene v (↻ (recover (1:ℝ) x))); simp [ recover ]
      exact read_hold v he
lemma ray_to_route (A:Ticket σ)(W:Type)[Fintype W](T': Layout W Eκ)(K:Layout Unit ℝ):
     digital K ( θ A Wρ ) = Route.Bulk.transfer (Sync.matrix (ρ).inner T' LinearMap.id) (digital (across T' K) (boost ((δ).center ρ) A)) (RayScatter.logarithm (δ) ρ Wρ T' K ) := digital_ink (δ) _ _ _ _ _ _ (inclineI _ hZ) -- remove
end fate
end YM.FVA2.RayScatter.Fork
