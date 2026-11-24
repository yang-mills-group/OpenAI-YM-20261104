import YM.SignedWilsonExpansion.F9.Desk
/-! # Crop-past estimate at any purchased order. Always on signed group laws -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k m c v b N M i j l r d n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
namespace MarqueQ.Crops
open SignedWilsonExpansion.Commission MarqueQ MarqueQ.PorchK Asymptotics FPS
variable {ι V':Type}
variable {L: Filter ι}{g Y B Tp Y' I': ι→ ℝ}{V: Type} [AddCommGroup V][Module ℂ V]
variable (h:Maxer L Y)
-- τ cost vs g and cap within.Compare clock x still complex for move algebra.
noncomputable def calcT (t:ℂ)(n:ℕ): InkQ →ₗ[ℂ] ℂ:= (Polynomial.aeval t).toLinearMap ∘ₗ PowerSeries.trunc (n+1)
lemma timed (x:InkQ)(t:ℂ)(k:ℕ): calcT t k x=∑ i∈Finset.range (k+1), coeff i x*t^i:=by
   unfold calcT; rw [LinearMap.comp_apply,AlgHom.toLinearMap_apply]; change Polynomial.eval₂ _ t _=_; exact eval₂_trunc_eq_sum_range t (RingHom.id ℂ) _ _
lemma timed_step (x:InkQ)(t:ℂ): calcT t (k+1) x=calcT t k x+coeff (k+1) x*t^(k+1):=by rw [timed,timed,Finset.sum_range_succ]
namespace clockQ
variable (p:∀ᶠ i in L, |g i|≤1) (τ:ι→ℂ)(u:τ=O[L] g)
include p u
lemma power (i:ℕ)(j:ℕ)(v:j ≤ i): (fun a=> (τ a)^i)=O[L] fun a=> (g a)^j:=by
    refine IsBigO.trans (u.pow _) (IsBigO.of_bound' (?_)); filter_upwards [p] with i hi; simp only [ norm_pow ]; exact pow_le_pow_of_le_one (abs_nonneg _) hi v
include h
lemma chooseOne (q:ι→InkQ)(v:charge e L Y B q)(k:ℕ)(hk:k ≤ e) : Wage L Y B (fun i=> calcT (τ i) k (q i)):=by
    simp_rw [timed]; apply Wage.sum h; intro i u; have hx:= Finset.mem_range.mp u; refine (Wage.mul (v i (by omega)) (Wage.enroll (power p τ ‹_› i 0 (Nat.zero_le _)))).fix (.refl ..) (?_); exact Eventually.of_forall fun j=> by change B j * (g j^(0:ℕ))=_; simp
lemma dropFee (q:ι→ InkQ)(v:charge e L Y B q)(k j:ℕ)(hk:k≤j)(hv:j ≤ e) : Wage L Y (B*g^(k+1)) (fun i=>calcT (τ i) j (q i)-calcT (τ i) k (q i)):=by
    induction hk with
    | refl=> simp_rw [sub_self]; exact Wage.nil
    | @step j hj ih=>
       have ht':k≤j:=hj; have he:=(Wage.mul (v (j+1) hv) (Wage.enroll (power p τ u (j+1) (k+1) (by omega)))); refine (Wage.plus h (ih (by omega)) he).fix (?_) (.refl ..); exact Eventually.of_forall fun i=> by dsimp only; rw [timed_step]; ring
omit p u
lemma toPoly (q:ι→InkQ)(v: charge k L Y B q)(i:ℕ): Wage L Y B fun j=> coeff i (PowerSeries.trunc (k+1) (q j):InkQ):=by
    by_cases hp:i≤k; · simp_rw [PowerSeries.coeff_coe_trunc_of_lt (Nat.lt_succ_of_le hp)]; exact v i hp
    simp_rw [Polynomial.coeff_coe, coeff_trunc, if_neg (show ¬ i< k+1 from mt Nat.le_of_lt_succ hp)]; exact Wage.nil
omit h in
private lemma powerC {a:ℕ}(x:Polynomial ℂ)(p:x.natDegree ≤ a)(t:ℂ): calcT t a x=x.eval t:=by rw [calcT, LinearMap.comp_apply, trunc_coe_eq_self (Nat.lt_succ_of_le p), AlgHom.toLinearMap_apply,Polynomial.aeval_def]; rfl
include p u
lemma mulch (x y:ι→InkQ)(v:charge k L Y B x)(w:charge k L Y I' y):
    Wage L Y ((B*I')*g^(k+1)) (fun i=> calcT (τ i) k (x i)*calcT (τ i) k (y i)-calcT (τ i) k (x i*y i)) := by
    let T:=trunc (R:=ℂ) (k+1); let a i:= T (x i)* T (y i); let f(i):=(a i:InkQ); have he: charge (k+k) L Y (B*I') f:=by
       have ht:= charge.mul (a:=fun i=>( T (x i):InkQ)) (b:=fun i=>(T (y i):InkQ)) (e:=k+k) h (B:=B) (t0:=I') (fun i _=> toPoly h x v i) (fun i _=> toPoly h y w i)
       simp only [f, a, Polynomial.coe_mul]; exact ht
    refine Wage.fix (dropFee h p τ u f he k (k+k) (Nat.le_add_right ..) le_rfl) (Eventually.of_forall fun i=> (?_)) (.refl ..)
    have hx:(a i).natDegree≤ k+k:= (Polynomial.natDegree_mul_le ..).trans (add_le_add (Nat.le_of_lt_succ (natDegree_trunc_lt ..)) (Nat.le_of_lt_succ (natDegree_trunc_lt ..)))
    have hh(i):T (f i)=T (x i*y i):=by unfold f a; rw [Polynomial.coe_mul]; exact trunc_trunc_mul_trunc ..
    dsimp only; rw [show calcT (τ i) k (f i)=calcT (τ i) k (x i*y i) from congr_arg (Polynomial.eval (τ i)) (hh i),powerC _ hx,show Polynomial.eval (τ i) (a i)=_ from Polynomial.eval_mul]; rfl
end clockQ
end MarqueQ.Crops
end YM.WilsonCoeffUV.Mer.Xa
