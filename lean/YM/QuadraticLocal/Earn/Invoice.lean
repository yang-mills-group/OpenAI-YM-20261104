import YM.QuadraticLocal.Earn.Rendering
/-!
## First authorization: energy at the running threshold

For ALL model marks in this schema. Render on their mask supports. Need to
convert true exponent length & rank prices to the repeated step
β powers. Use polynomial prices anchored at all slots; don't even mention
volume. Uses assigned_tail at EVERY center and inside weights. The unused exponent
reserve below is exposed for the LONG off-region proof; price EVERY such term. We
keep the actual coverage weights even on length tails, after multiplying by test
and joint factors inside!

 `B(B.model)` years.L ≤ B_clock.real.K variance`, `g>0` current running convention.
 V` ≥1 and ≥t/g`: estimate ℓ where `t=B.threshold`. Need this ALL times
 model invoked, not e.g. a new V at each MORE label. Stage choices and certification
 below. The output for this norm scales linearly in the analytic envelope (use also
 on weighted debt parts by restricting the list).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice RG Wilson Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals
open AnalyticBridge VerifiedReset Collection Precision Exterior Extra.Iteration Next.Scheduling Next.Foundations
open QuadraticLocal.Sunrise
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type*}[DecidableEq V]{G:Gauge}{n:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ}
namespace Invoice
open Row Wages
variable (B:BudgetPoint)(U:ℝ)
variable (X:ι→ Row P R G α)(t:V→ℝ) (hw:∀ i,0<t i)
-- common growth for current Epoch.Both projected height α.T.Global taxes.Title ≤ aν etc. need positivity on V.Boost.
def Supports (a:ℝ) (g:ℝ) (σ:ℝ) (e:ℝ) : Prop:=
   0<g ∧ g≤1 ∧ 1≤U ∧ B.threshold ≤ g*U ∧ 0≤σ ∧ Footprint.reserve σ a ((B.B:ℝ))⁻¹ e
local notation "M"=> B.B
local notation "Zoo"=> B.power*B.order

variable (s Ψ:ℕ)
def tax (s q:ℕ):ℝ:= 1000+(s:ℝ)+q
def memories (s:ℕ):ℕ:= Wages.grade s B.power B.order
-- resources quote.Every.A

def liberty (G:Gauge)(k s P n b:ℕ)(W:ℝ):ℝ:=Wages.startup G s P n * W^s * ((b:ℝ)+2)^k
def price (V:ℕ)(a c:ℝ) (G:Gauge) :ℝ:= Footprint.payment 1 (B.B+2) (Zoo+memories B s) c (liberty G Zoo s B.power B.order B.B U) 1 a (Invoice.tax s V)
-- price factor `*b` where b is actual cost.B.Volume transfer.G

lemma settledP (G:Gauge)(p s n:ℕ):1 ≤ Wages.startup G s p n:= by
   unfold Wages.startup; apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two); exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (slot_ge ..))
lemma pay_nn (hU:1 ≤ U) (G:Gauge)(k n d b:ℕ): 0 < liberty G k s d n b U:= by unfold liberty; have ht:=lt_of_lt_of_le zero_lt_one (settledP G d s n); have hu:=lt_of_lt_of_le zero_lt_one hU; positivity
lemma positive (hU:1≤U) (V:ℕ)(he:0<e) (G:Gauge) : 0 < price B U s V a e G:=by
    let v:= liberty G Zoo s B.power B.order B.B U; have ht:= pay_nn U s hU G Zoo B.order B.power B.B; unfold price Footprint.payment Footprint.degreeIncome; have hi:0<Footprint.spread 1 (M+2):=by unfold Footprint.spread Animals.ballCost; positivity
    have hc:0<1-Real.exp (-e):= sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)); positivity
variable (K:Row P R G α)
lemma p_bound (A:Atom G s): 0≤ A.magnitude:= Finset.sum_nonneg fun _ _=> abs_nonneg _
variable (hU:Supports B U a g σ e) (hk:K.Graceful σ) (hK: K.lamp.r ≤ s)
include hU hk hK
set_option quotPrecheck false
local notation "fee"=> (liberty G (B.power*B.order) s B.power B.order B.B U)
local notation "Φ" i:max=> (1+((X i).length:ℝ))
lemma letters : K.baseCost B g ≤ g^K.lamp.e*fee*(1+(K.length:ℝ))^(B.power*B.order+memories B s) := by
   let p:= Zoo; let t':= B.threshold; let v':= memories B K.lamp.r; let a:= liberty G p s B.power B.order B.B U; let v:= memories B s; let f:= (1+(K.radius B.B:ℝ)); let g₁:= g^K.lamp.e; obtain ⟨hg,hg',hU,hB,hz,_⟩:=hU
   have ht:t'>0:= B.threshold_pos; let k':=K.lamp.r
   let d:= (M:ℝ); let A0:=K.atom.length; let r:=(K.atom.length:ℝ); let l':=(K.length:ℝ); let u:= K.atom.magnitude; let U':= Wages.startup G k' B.power B.order; let U'':= Wages.startup G s B.power B.order; have he : K.baseCost B g = ( (f^p) * g₁ * (t'/g)^k')*(U'*u*(r+1)^v'):=by
      unfold baseCost; rw [Wages.scan,abs_of_pos (zpow_pos hg _), Loan.lag, zpow_sub₀ hg.ne',zpow_natCast,zpow_natCast, div_pow]; field_simp; dsimp only [v',t',U',r,u,k',g₁,f,p,memories] -- K ? unfold
      ring
   have h₀:0 ≤ u:= p_bound _ _; have hx:u≤1:= by apply le_trans _ hk; exact le_mul_of_one_le_right h₀ (Real.one_le_exp (mul_nonneg hz (Nat.cast_nonneg _)))
   have hl : r≤l':= Nat.cast_le.mpr (Nat.le_add_left ..)
   have hu : U' ≤ U'':= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (slot_ge ..)) hK) (by positivity) -- `_`
   have hp:= settledP G B.power s B.order; have h1 := settledP G B.power k' B.order
   have h₁ : 0≤ t'/g:= div_nonneg ht.le hg.le; have h₂ : t'/g ≤ U:= (div_le_iff₀ hg).mpr (by linarith)
   have h₃ :(t'/g)^k' ≤ U^s:= (pow_le_pow_left₀ h₁ h₂ _).trans (pow_le_pow_right₀ hU hK)
   have h₄ : f ≤ (d+2)*(1+l'):=by
       have hr: f=1+(d+1+l'):=by unfold f d l' Row.radius; push_cast; rfl
       rw [hr]; nlinarith only [show 0≤ d from Nat.cast_nonneg _, show 0≤ l' from Nat.cast_nonneg _]
   have h₅ : U'*u*(r+1)^v'≤ U''*(1+l')^v:= by
       have h'(u v:ℝ)(hv :0≤u)(h:u≤1)(hx:0≤v): v*u≤ v:=mul_le_of_le_one_right hx h
       apply mul_le_mul ((h' u U' h₀ hx (zero_le_one.trans h1)).trans hu) _ (by unfold r; positivity) (zero_le_one.trans hp);
       apply (pow_le_pow_left₀ (by unfold r; positivity) (show r+1≤1+l' from (by linarith)) _).trans; apply pow_le_pow_right₀ (by unfold l'; exact le_add_of_nonneg_right (Nat.cast_nonneg _)); unfold v' v memories Wages.grade; exact Nat.mul_le_mul_left _ hK
   calc
     _ = _:= he
     _ ≤ (((d+2)*(1+l'))^p * g₁ * U^s)*(U''*(1+l')^v):= by
        have hf:0<f:= by unfold f; positivity
        have hp':0 < g₁:= pow_pos hg _; have hx:0 ≤ U':=zero_le_one.trans h1; have hm:0 ≤ r:= Nat.cast_nonneg _; have hh:0<U:=lt_of_lt_of_le zero_lt_one hU
        -- give gcongr
        gcongr <;> first | assumption | positivity
     _ = _:= by rw [mul_pow]; unfold liberty; unfold d l' U'' p g₁ v; ring

-- rendering at THIS registration.ALL tests. weights
omit hU hk hK
variable (hℓ:Offers X t σ r) (h₁: ∀ i,(X i).Graceful σ)(hJ:∀ i,(X i).lamp.r ≤ s) (hq:∀ i,(X i).mode.val.card ≤ Ψ)
local notation "k̂"=> (κ (G:=G)) -- ignore
local notation "area"=> (fun i=> (X i).ground B)
def income (g:ℝ) (i:ι):= Poly.toll t (X i).mode*(X i).charge B g
lemma income_nn (b:ℝ) (i:ι)(hw:∀i,0<t i):0≤ income B X t b i:= by
   apply mul_nonneg (Poly.worth hw _).le; apply mul_nonneg _ (X i).sound.le; exact mul_nonneg (by positivity) ((X i).real_quote B b).1
include hw hU hℓ h₁ hJ hq
lemma paying (m:ℕ) (x:Site n) : SumBudget (fun i=> if m ≤ (X i).length then if x∈(X i).ground B then (income B X t g i)*Real.exp (a*(coverNumber B.B ((X i).ground B):ℝ)) else 0 else 0) (price B U s Ψ a e G * r * Real.exp (-e)^m):=by
    obtain ⟨hg,hg',hU',ht,hσ,hT⟩:= hU
    let φ i:=Poly.toll t (X i).mode * (X i).salary; let z i:=(X i).center; let l i:=(X i).length; let X0 i:=(X i).ground B; let F i:=(X i).height σ
    let p:=(B.power*B.order+memories B s)
    have hφ i:0<φ i:=mul_pos (Poly.worth hw _) ((X i).sound)
    have hz : Footprint.Anchored z φ l σ r:= by
       intro i; convert hℓ i using 1; ext j; unfold φ; split
       next h=>unfold Row.height l; ring
       next=>rfl
    have hΦ(i):income B X t g i ≤ fee*φ i*(1+(l i:ℝ))^p:= by
       have he: g^(X i).lamp.e ≤ (1:ℝ):= pow_le_one₀ hg.le hg'
       let a₁:=(1+(l i:ℝ))^p
       have hv:= letters (a:=a) (g:=g) (e:=e) B U s (X i) ⟨hg,hg',hU',ht,hσ,hT⟩ (h₁ i) (hJ i)
       change _ ≤ g^(X i).lamp.e * fee * a₁ at hv
       rw [show income B X t g i=(X i).baseCost B g * φ i from (by unfold income φ Row.charge; ring)];
       have hs:0≤ fee:= (pay_nn U s hU' G Zoo B.order B.power B.B).le; have hj:0≤ a₁:=by unfold a₁; positivity
       exact (mul_le_mul_of_nonneg_right (hv.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hs he) hj)) (hφ i).le).trans_eq (mul_right_comm ..)
    let hL : Supports B U a g σ e:= ⟨hg,hg',hU',ht,hσ,hT⟩; have he := Footprint.assigned_tail (id : Site n→Site n) 1 (fun i=>by simp) z φ (fun i=>(hφ i).le) l X0 hz (B.B+2) p B.B (fun i j hj=>?_) (fun i=>?_) (pay_nn U s hU' G Zoo B.order B.power B.B).le hT (income B X t g) (fun i=> income_nn B X t g i hw) hΦ m x («v»:=Invoice.tax s Ψ) -- find infer
    rotate_left
    · rw [id_eq, separation_comm]; have h:=near (X i) _ j hj; exact h.trans (by unfold Row.radius l; nlinarith)
    · let i0:=X i; have hr:0< (M:ℝ):=Nat.cast_pos.mpr B.B_pos; have hh : M * coverNumber M (X0 i) ≤ (1000+s+Ψ)*M+l i:= (i0.tiles M B.B_pos).trans (by unfold i0; gcongr <;> first | apply hJ | apply hq)
      unfold tax; field_simp; push_cast; rw [Nat.mul_comm M] at hh; exact_mod_cast hh
    exact budget_loosen he (le_of_eq (by unfold price Footprint.payment Footprint.degreeIncome; ring))
end Invoice
end YM.QuadraticLocal.Earn
