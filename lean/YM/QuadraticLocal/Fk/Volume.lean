import YM.QuadraticLocal.Cycle.Bank
import YM.QuadraticLocal.Fk.Untag
import YM.QuadraticLocal.Fk.Station
/-!
# The finite-period prescription ≠ cover; provide post-L numerical η-alias price

At every a in any delayed stage regime before volumes. Need also use poll >0 from Lore
non-option. Doesn't itself say this small price remains in REAL re-expression.Support.Eleven. It
certifies slippage of formal Taylor degree bank against finite prescription on ANY link stencil,
 even multiplied by these large arguments & all markers φ. These power budgets explicitly
 preserve separate calculation in `Step` (which uses auxiliary τ). Don't extrapolate to a
coarser step after all-volume convergence without using that step's winding price again.

Quantifier: through all requested order+2≤ y and integer β-demand bounded by the moving
stage (`Y`, may request this simultaneously all considered α-leaves.Regrowth.Sc.Uri`). Width
and lower κ supplied ahead.Same as pre-L kernel.Focusing; these are extra post-L delays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration
open ThroughLaunch Height Opera Boulevard Trio Slide Sienna Fare Lapis Coat
open Input Org Supply Roost Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Burn AllOrder.Ink AllOrder.Ink.Money
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Wheel
open AllOrder.Wheel.Ride AllOrder.Wheel.Ride.Pair AllOrder.Catch
open QuadraticLocal.Sunrise QuadraticLocal.Echo Earn Mentor Poetry.Agenda RemainderComparison Mentor.Wharf
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Legato.VowsR AnalyticBridge.VerifiedReset Offices
namespace Volume
variable {G:Gauge} {X : Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(D:Rolls X.p)(Q:R.Tab D)
open Precision
variable (ψ:ℕ→ℕ) (K0:Offices.Books R D Q ψ)
variable {P:Protection D} {x y a:ℕ}(r : Opportunity x y) (K:Epoch R D x y r)
local notation "κ"=> Burn.horizon K.vac
local notation "Lx" => D.L x
local notation "φ"=> Poetry.Agenda.poll R κ x
local notation "w"=> Wharf.upper D R x y Q ψ K0
local notation "z"=> Wharf.title D R x y Q ψ K0
local notation "Ξ"=> RemainderComparison.Breeze.areaBudget
set_option quotPrecheck false
local notation "ϕ"=> (fun ξ:ℝ=> Pressure.betaF G ξ (D.L x))
local notation "Λ"=> (fun ξ:ℝ=> ConnectedActivityE6.loopBill G (D.L x) ξ)
-- use absolute for powers.
def cutRank (Y:ℕ)(ωZ:ℝ):ℝ:= |(2+ωZ)^Y|
local notation "P𝓏" n:max=> ( Air.united n (Breeze.areaBudget (n).val r.count ((( D.L x ).val:ℝ)^4)) )
local notation "Yn" t:max=> (ϕ t) ^ (x:ℕ)
noncomputable def spare (p:ℝ)(n:Side) := ( Wharf.rate z w (Λ p) n * dearth (φ) n)*(Volume.cutRank ((Burn.horizon K.vac)+4) ((ϕ p)^(x:ℕ))) * ( Air.united n (Breeze.areaBudget (n).val r.count ((( D.L x ).val:ℝ)^4)) )
noncomputable def goal (t:ℝ):= (ϕ t)^(-(x:ℝ))
local notation "χ₀" n:max=> (fun t=> Volume.spare R D Q ψ K0 r K t n)
open AbsoluteSums.Animals -- name billCost
-- polynomial growth
section lift
variable (C:ℝ)(hp:0 ≤ C)(m n k:ℕ)
local notation "n₀"=> (1+ (n:ℝ))
local notation "c₀"=> (81*C+1)
include hp
lemma scope_bill : Breeze.areaBudget n k C ≤ ((81*C+1)^k*Real.exp 1) * (1+(n:ℝ))^(4*k):= by
 let s:ℝ:= (1+(n:ℝ)); have hy:1≤ s:=le_add_of_nonneg_right (Nat.cast_nonneg _);
 have hX:0≤(n:ℝ):= Nat.cast_nonneg n
 have h : ((ballCost n:ℕ):ℝ) ≤81*s^4:=by
    unfold ballCost; push_cast; calc
       _ ≤ (3*s)^4:= pow_le_pow_left₀ (by positivity) (by unfold s; linarith) _
       _ = _:=by ring
 unfold Breeze.areaBudget; change _ ≤ _ * s^_; rw [mul_right_comm, pow_mul s, ← mul_pow]; apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _); apply pow_le_pow_left₀ (by positivity) _; nlinarith only [mul_le_mul_of_nonneg_right h hp, one_le_pow₀ (n:=4) hy]
end lift
open AbsoluteSums
local notation "s★"=> ( (φ/2) : ℝ )
variable (n:Side)
local notation "ν"=> (n.val:ℝ)
local notation "n₀"=> (1+ (n.val:ℝ) )
local notation "L₁"=> ( (D.L x).val :ℝ)
local notation "ℓ1"=> ( z+4+4*r.count ) -- x,y
lemma canon (t:ℝ) : 0 < Poetry.Agenda.poll R (Burn.horizon K.vac) x∧ 0 < Wharf.upper D R x y Q ψ K0 ∧ 0≤ cutRank (κ+4) (Yn t):=⟨ (AllOrder.Ink.Money.soprano _ (Poetry.Agenda.receives R (Burn.horizon K.vac) x).choose_spec.1 _), (Wharf.ready ..).choose_spec.choose_spec.1, abs_nonneg _ ⟩
-- ℓ.Exposure budget. polynomial multiplied by x.Ph.Bpp.Rule.
-- Maybe Lx e from cover.This is unit multiplier for field arguments ≤ this `ŵ-hat^x`.
local notation "Γℓ"=> ((81*L₁^4+1)^r.count * Real.exp 1)
local notation "Γ"=> Γℓ * ( s★⁻¹^ ( z+4+4*r.count ) * ((z+4+4*r.count).factorial:ℝ) * Real.exp s★ )
local notation "bz" ξ:max => ( w * (1+|Λ ξ|)^z )
local notation "g" t:max=> Volume.cutRank ((Burn.horizon K.vac)+4) ((ϕ t)^(x:ℕ))
local notation "B₁" t:max=> (( bz t )* (g t) * Γ)
lemma earning (ξ:ℝ) : Volume.spare R D Q ψ K0 r K ξ n ≤ ((w * (1+|ConnectedActivityE6.loopBill G (D.L x) ξ|)^z) * (g ξ)* (Γ)) * (Real.exp (-( (Poetry.Agenda.poll R ( Burn.horizon K.vac ) x)/2)*(n.val:ℝ))) := by
 obtain ⟨hσ,hW,hg⟩:= canon R D Q ψ K0 r K ξ; have hz:0≤ ν:= Nat.cast_nonneg _; have hy:0≤ w:= hW.le; let U:=(bz ξ); have hU:0≤ U:= by unfold U; positivity
 let D0:= dearth φ n
 have ht:Volume.spare R D Q ψ K0 r K ξ n ≤ ((U * (g ξ))*Γℓ) * (Real.exp (-(φ)*ν)* (1+ν)^(z+4+4*r.count)):= by
    unfold Volume.spare; calc
       _ ≤ ( U *(n₀)^z * D0)*(g ξ)* ( (n₀)^4* ( Γℓ * (n₀)^(4*r.count))) := by
          unfold Wharf.rate Air.united; dsimp only; have hq : 0≤ Breeze.areaBudget n.val r.count (L₁^4):=by unfold Breeze.areaBudget; positivity
          have hn:ν ≤ 1+ν:= le_add_of_nonneg_left zero_le_one; unfold D0 U; dsimp only; -- gcongr maybe
          gcongr; exact scope_bill _ (by positivity) _ _
       _ = _:= by rw [pow_add,pow_add]; unfold D0 dearth; ring -- `κ xt`.pow_add at LHS? ring later
 refine ht.trans ?_; have hℓ:= polynomial_cost (half_pos hσ) hz (z+4+4*r.count); let Gp:=(s★)⁻¹^(z+4+4*r.count) * ((z+4+4*r.count).factorial:ℝ) * Real.exp s★
 let a:= n₀ ; let f(α:ℝ):= Real.exp (α*ν); let Z0:= (U*(g ξ)*Γℓ);
 calc _ ≤ Z0* (Real.exp (-(φ)*ν)* (Gp*f s★)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓ (Real.exp_nonneg _)) (mul_nonneg (mul_nonneg hU hg) (by positivity)) 
      _ = Z0*Gp * (Real.exp ((s★)*ν)*Real.exp (-(φ)*ν)):=by unfold f; ring
      _ = _:=by rw [← Real.exp_add,show (s★)*ν+ -(φ)*ν= -(s★)*ν by ring]; unfold Gp Z0 U; ring
local notation "F✔"=> (fun ξ:ℝ=> (bz ξ)*(g ξ) * (Γ) )
local notation "χ₁"=> (fun t:ℝ=> F✔ t*Real.exp (-( (Poetry.Agenda.poll R ( Burn.horizon K.vac ) x)/2)*(radiusB t:ℝ))) -- likely need `(F✔) t`
lemma budgeting (ℓ:ℝ) : Rate G (D.L x) ℓ (fun (ξ:ℝ)=> (( bz ξ)*( g ξ)* (Γ)) * Real.exp (-(φ/2)*(radiusB ξ:ℝ))) :=by
 obtain ⟨hσ,hW,_⟩:= canon R D Q ψ K0 r K 0; let t:=φ; let A' := fun ξ=> (( bz ξ)*( g ξ)* (Γ)) * Real.exp (-(φ/2)*(radiusB ξ:ℝ)); let b:ℝ:= x*(Burn.horizon K.vac+4:ℕ)
 have hB : Rate G (D.L x) 0 (fun ξ:ℝ=> bz ξ):= by
    let P:=(Plateau.Claim.absolute (ConnectedActivityE6.loopBill_rate G ( D.L x ))); simpa only [zero_mul] using (( (Rate.const (G:=G) («L»:=D.L x) (1:ℝ)).add P).pow z).mul_left w
 have ht : Rate G (D.L x) (1*x) (fun ξ:ℝ=> (ϕ ξ)^(x:ℕ)):= Rate.hat.pow _
 have hE : Rate G (D.L x) b (fun ξ:ℝ=> ( g ξ )):= by simpa only [b,Nat.cast_mul, cutRank,one_mul] using (Plateau.Claim.absolute ((((Rate.const 2).weaken (le_trans (by positivity : 0 ≤ (1:ℝ)*(x:ℝ)) le_rfl)).add ht).pow (Burn.horizon K.vac+4))) -- pow_
 have hk : Rate G (D.L x) (ℓ-b) (fun ξ:ℝ=> Real.exp (-(φ/2)*(radiusB ξ:ℝ))):= Plateau.dearth_rate G (D.L x) _ (by positivity : 0<(φ/2)) _;
 simpa only [zero_add, add_sub_cancel, add_sub_cancel_right] using ((( hB.mul hE).mul_right (Γ)).mul hk)
lemma rent : ∀ᶠ t in atTop,∀ n:Side, radiusB t≤n.val → Volume.spare R D Q ψ K0 r K t n ≤ Pressure.betaF G t ( D.L x )^(-(x:ℝ)):= by
 filter_upwards [(budgeting R D Q ψ K0 r K (-(x:ℝ)-1)) (-(x:ℝ)) (by linarith)] with t ht; -- `Rate` is funext. fix
 intro n hn; have h₁:= Volume.earning R D Q ψ K0 r K n t; obtain ⟨hσ,hW,hg⟩:= canon R D Q ψ K0 r K t; refine le_trans (le_trans h₁ (mul_le_mul_of_nonneg_left (?_: Real.exp _ ≤ Real.exp (-(φ/2)*(radiusB t:ℝ))) (by positivity))) ((le_abs_self _).trans ht)
 exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hn) (by linarith))
-- Budget ready after post-L: lookup extension; any η_Per horizon.Progress.Kit validity
variable (V:Delays P)
structure Fund : Prop where
  supports (x y:ℕ)(r:Opportunity x y)(K:Epoch R D x y r)(t :ℝ): V.betaEntry x ≤ t → ∀ n:Side, Pressure.radiusB t ≤ n.val → Volume.spare R D Q ψ K0 r K t n ≤ (Pressure.betaF G t ( D.L x ))^(-(x:ℝ))
lemma bankroll (V:Delays P) : ∃ y:Delays P,DelayLe V y ∧ ∀ x:Delays P, DelayLe y x → Volume.Fund R D Q ψ K0 x := by
 let f' i j (r:Opportunity i j) (K: Epoch R D i j r) t:= ∀ n:Side, (Pressure.radiusB t) ≤ n.val → Volume.spare R D Q ψ K0 r K t n ≤ betaF G t (D.L i) ^ (-(i:ℝ)); -- expand
 let q i j t:= ∀ (r:Opportunity i j)(K:Epoch R D i j r), f' i j r K t
 have ha i j:∀ᶠ t in atTop,q i j t:= eventually_all.mpr (fun r=> eventually_all.mpr (fun K=> Volume.rent R D Q ψ K0 r K))
 let p i t:= ∀ j:ℕ, PriceCompiler.StepStages i j → q i j t; -- maybe pg.He.Resource
 obtain ⟨A,-,hA,h⟩:=collect_upper V.betaEntry p (fun x=> (eventually_transitions x atTop _ (fun y _=> ha x y))); refine ⟨{V with betaEntry:=A},⟨ hA, le_rfl, le_rfl, le_rfl⟩,fun Y hy=> ⟨fun x y r K t ht=> h x t ((hy.beta x).trans ht) y r.meet r K⟩⟩
variable (G)
def wind : LawScroll G ψ where
    clause (E) D PP C R₀ q Wp Z Q₀ S R Y K T' V:= Volume.Fund R D Y ψ K V
    permits := by
      intro S Tq R C E h; refine ⟨(fun _=> (0:ℕ)),fun l hL D q Wp Z Q' S' he P T₀ Y Book hP V=>?_⟩; exact bankroll («X»:=ThroughLaunch.currency S Tq l) R D Y ψ Book V
end Volume
end YM.QuadraticLocal
