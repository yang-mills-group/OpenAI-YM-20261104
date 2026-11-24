import YM.LocalLTE.Brochure.Scale
import YM.LocalLTE.Brochure.Cost
import YM.Extra.ITERATION_NO_LOSS.Rebuild
/-! Cost transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open LocalLTE.Inset Org
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open ClockB Urns
open LocalLTE.Fan LocalLTE.Fan.Pastel LocalLTE.Port LocalLTE.Port.LoopBank Coat
variable {G:Gauge}(L:Side)(p:Stage)(m u M:ℕ)(μ ζ:ℝ)
local notation "σ"=>Mallow.aust
namespace Coterie
abbrev countB (t:ℝ)(u:ℕ):= t+3*(u:ℝ)
abbrev ballast(x:ℝ):= x^(-(2:ℝ))
abbrev books(x:ℝ)(ζ:ℝ):= ballast x*(x^aust + x^(-ζ))
abbrev past(x:ℝ)(ζ:ℝ):= ballast x * x^(-ζ)
variable (hk:0≤ζ) (he:0≤μ)
local notation "YΤ"=> (fun x=> betaF G x L)
local notation "U₀" x=> (L.val*radiusB x)
local notation "b"=> p.power
local notation "b'"=> p.order
-- Pay at coarse step where R=hatβ fine becomes CURRENT. κ old.Future Parent S. uniform.Degrees.
structure Acres (G:Gauge)(L:Side)(p:Stage) (ζ x:ℝ)(m:ℕ):Prop where
     serve (V:Type) [Fintype V] (hi:Fintype.card V ≤ m) (P:BudgetPoint) (hP:P.power=p.power)(hh:P.order=p.order) : let t:= betaF G x L; capacity P V (books t ζ) (past t ζ) (Urns.divisor t) (past t ζ) (t^ζ) (L.val*radiusB x) ≤ t^(-(1:ℝ))
include hk
lemma buildup : ∀ᶠ x in atTop, Acres G L p ζ x m:=by
    let u:= (YΤ); let t x:= past (u x) ζ; let k x:= books (u x) ζ; let f x:= (1+((↑(L.val*radiusB x:ℕ)):ℝ))^(b*b'); let s x:= Urns.divisor (u x)
    have hs:Rate G L 0 s:= afterShift L (G:=G) 0
    have hT:Rate G L 0 (fun x=> ((L.val*radiusB x:ℕ):ℝ)):=by simp_rw [Nat.cast_mul]; exact Rate.radius_price.mul_left _
    have hf: Rate G L 0 f:= by simpa only [zero_mul] using! (((Rate.const 1).add hT).pow (b*b'))
    have ht:Rate G L (-2+ -ζ) t:= Rate.mul Rate.power Rate.power
    have hv:=Rate.add (Rate.power (G:=G) (L:=L) (a:=aust)|>.weaken (by norm_num [aust]:Mallow.aust ≤ 0)) ((Rate.power (a:=-ζ)).weaken (neg_nonpos.mpr hk))
    have hK:Rate G L (-2) k:=by simpa only [add_zero] using! ((Rate.power (a:=-(2:ℝ))).mul hv)
    let q x:=2*(f x*((m:ℝ)*k x))+(u x)^ζ*(2*((m:ℝ)*t x)+2*((m:ℝ)*(t x*s x)))
    have hq:Rate G L (-2) q:=by
       have hx:= hf.mul (hK.mul_left (m:ℝ))|>.mul_left 2; rw [zero_add] at hx; apply Rate.add hx
       have ht':= (ht.mul hs); rw [add_zero] at ht'
       convert! (Rate.mul Rate.power (((ht.mul_left (m:ℝ)).mul_left 2).add ((ht'.mul_left (m:ℝ)).mul_left 2))) using 1; ring
    filter_upwards [hq (-1) (by norm_num), (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx h
    have hh:0 ≤ u x:= zero_le_one.trans h; refine ⟨fun V H ht A' ha h' =>?_⟩
    let j:=Fintype.card V; have hj:(j:ℝ)≤ m:= Nat.cast_le.mpr ht
    have hv:0 ≤ t x:=by unfold t past ballast; positivity
    have hs:0 ≤ s x:= (Urns.nonzero _).le; have hK:0 ≤ k x:= by unfold k books ballast; positivity
    have hf:0 ≤ f x:=by unfold f; positivity
    apply le_trans _ ((le_abs_self _).trans hx)
    unfold capacity turnQ; rw [ha,h']; change 2*(f x*((j:ℝ)*k x))+(u x)^ζ*(2*((j:ℝ)*t x)+2*((j:ℝ)*(t x*s x))) ≤ q x
    exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj hK) hf) zero_le_two) (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj hv) zero_le_two) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj (mul_nonneg hv hs)) zero_le_two)) (Real.rpow_nonneg hh _))
include he
-- volume ascent.Year. local output caps.Track.Ask u+1 at next coarse weight. Need Y_old. 
omit hk in
lemma beaming : ∀ᶠ x in atTop, neat x (countB μ (u+1)) ≤ ballast x* neat (YΤ x) (countB μ u):=by
    let y:= countB μ u; let z:= -y-2; let a:= G.slopeConstant*Real.log L.val; let Gf (x:ℝ):=betaF G x L
    have he:z ≤ 0:= by unfold z y countB; linarith [Nat.cast_nonneg (α:=ℝ) u]
    filter_upwards [eventually_ge_atTop a,(Work.E09.betaF_growth G L).eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((2:ℝ)^(-z))] with x h hp hz ht
    have hx: 0<x:= zero_lt_one.trans_le hz
    have hf: x+a≤2*x:=by linarith only [h]
    have hb: neat (YΤ x) y= Gf x ^ z:=rfl
    have hK: (2:ℝ)^z*x^z≤ Gf x^z:= by rw [← Real.mul_rpow (by norm_num) hx.le]; exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hp) hf he
    change _ ≤ x^(-(2:ℝ))* Gf x^z; refine le_trans ?_ (mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hx.le _)); have hG:z+(-3:ℝ)=-countB μ (u+1)-2:=by unfold z y countB; push_cast; ring
    unfold neat; rw [← hG]; rw [show z+(-3)=(-2)+((-1)+z) by ring, Real.rpow_add hx, Real.rpow_add hx]; apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _); refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx.le _)
    rw [Real.rpow_neg (by norm_num)] at ht; rw [Real.rpow_neg_one]; have hq:= (inv_le_inv₀ hx (inv_pos.mpr (Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) z))).mpr ht; rwa [inv_inv] at hq
-- buy in same Posts.Roost
variable {s:Sheet G} {D:Rolls s}{P:Protection D}
structure YearEnd (μ ζ:ℝ)(M N:ℕ)(V:Delays P):Prop where
     wake (j i:ℕ):StepStages j i→∀ x≥ V.betaEntry j, Acres G (D.L j) (s.profile j) ζ x N ∧ radiusB (betaF G x (D.L j)) ≤ 2*radiusB x∧ ∀ (u:ℕ), u< M → neat x (countB μ (u+1)) ≤ ballast x* neat (betaF G x (D.L j)) (countB μ u)
-- combined credentials.Boring stamp plus Posters.
lemma dinner(V:Delays P) : ∃ U:Delays P,DelayLe V U ∧ ∀ Y:Delays P,DelayLe U Y → YearEnd μ ζ M m Y:=by
    have ht (j i:ℕ): ∀ᶠ x in atTop, Acres G (D.L j) (s.profile j) ζ x m ∧ radiusB (betaF G x (D.L j)) ≤ 2*radiusB x∧ ∀ (u:ℕ), u< M → neat x (countB μ (u+1)) ≤ ballast x* neat (betaF G x (D.L j)) (countB μ u) :=by
       let l:= D.L j; have h(k:Fin M):= beaming (G:=G) l k.val μ he
       filter_upwards [Rebuild.geometry (G.slopeConstant*Real.log (D.L j).val), buildup (G:=G) l (s.profile j) m ζ hk,eventually_all.mpr h] with x hx he ht
       exact ⟨he,hx.1.1,fun k h=> ht ⟨k,h⟩⟩
    obtain ⟨x,-,he,h⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ fun i hi=> ht j i)
    exact ⟨{V with betaEntry:=x},⟨he,le_rfl,le_rfl,le_rfl⟩,fun Y hy=>⟨fun j i h' t hx=> h j t ((hy.beta j).trans hx) i h'⟩⟩
variable (G)
def campJ (h0:0 ≤ μ)(h₁:0 ≤ ζ) (F:Prereq G): Prereq G where
    jobs:= fun V κ=> F.jobs V κ ∧ YearEnd μ ζ M m V
    buys:= by
         intro s D P U κ hκ; obtain ⟨Y,he,H⟩:= F.buys U κ hκ; obtain ⟨T,hT,hY⟩:= Coterie.dinner m M μ ζ h₁ h0 Y; exact ⟨T,he.trans hT,fun W h=>⟨H W (hT.trans h),hY W h⟩⟩
end Coterie
end YM.PhysicalNext.Repeat.Mallow
