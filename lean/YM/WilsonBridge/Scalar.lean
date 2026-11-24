import YM.WilsonBridge.Master
/-!
# The very same denominator (including real formal coupling changes)

Useful at the finite end or with marker channels. Powers in inserted rankLevel are
moved by these literal scalar series products. `response` defined on any End Wick rule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open Function Finset
open PowerSeries (mk coeff)
open scoped BigOperators
variable {E F V : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] {p:Sector V}[Fintype V] {n:ℕ}
local infixl:70 " ⚘ " => Trunk.core

def series : T ℂ ≃ₗ[ℂ] Cn where
    toFun := mk
    invFun X i:= coeff i X
    map_add' f g:= by ext i:1; rw [map_add]; simp
    map_smul' f g:= by ext i:1; simp
    left_inv x:= funext fun k=> PowerSeries.coeff_mk k x
    right_inv x:= PowerSeries.ext fun i=> PowerSeries.coeff_mk i _
lemma pack (F:T ℂ) (i:ℕ): coeff i (series F)= F i:= PowerSeries.coeff_mk ..
lemma scalar_series (F H:T ℂ): series (F ⚘ H)=series F * series H:= by ext i:1; simp_rw [pack,PowerSeries.coeff_mul,pack]; rfl

def bilfee (E:Type)[AddCommGroup E][Module ℂ E]: Bil ℂ E E where
    toFun c:=c • LinearMap.id -- cod
    map_add' c x := add_smul ..
    map_smul' c x:= by rw [smul_eq_mul]; exact mul_smul .. -- inspect
abbrev multiply (a:T ℂ)(F:T E): T E:= pairW (bilfee E) a F
local infixr:73 " ∙ " => multiply
lemma mul_price (X:T ℂ)(Y:T E)(i:ℕ): (X ∙ Y) i=∑ d∈ antidiagonal i,X d.1 • Y d.2 := by unfold multiply; simp [bilfee,paired]
lemma price_scalar (X Y:T ℂ) : X ⚘ Y = X ∙ Y := by funext i; rw [mul_price]; rfl
lemma price_pair (L:E →ₗ[ℂ] F)(X:T ℂ)(Y:T E): promote L (X ∙ Y)=X ∙ promote L Y:= by funext i; rw [promised,mul_price,mul_price,map_sum]; simp_rw [map_smul,promised]
lemma price_left (L:Angled E)(X:T ℂ)(Y Z:T E) : pairW L (X ∙ Y) Z=X ∙ (pairW L Y Z):= by
    funext i; rw [paired,mul_price]; simp_rw [mul_price,paired,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum]; exact (associate (fun i j k=> X i • L (Y j) (Z k)) i).symm -- metavars precision
lemma price_right (L:Angled E)(X:T ℂ)(Y Z:T E) : pairW L Y (X ∙ Z)=X ∙ (pairW L Y Z):= by rw [flips L Y (X ∙ Z), flips L Y Z, price_left L.flip]
lemma price_twice (X Y:T ℂ)(Z:T E): X ∙ (Y ∙ Z)=Y ∙ (X ∙ Z):= by
    -- through scalar associativity
    have hp (X Y:T ℂ) : X ∙ (Y ∙ Z)=(X ⚘ Y) ∙ Z:= by
       funext i; simp_rw [mul_price, price_scalar,mul_price,Finset.sum_smul, Finset.smul_sum,smul_smul,smul_eq_mul]; exact associate (fun i j k=> (X i*Y j) • Z k) i
    rw [hp,hp, show X ⚘ Y= Y ⚘ X from series.injective (by rw [scalar_series,scalar_series,mul_comm])]

-- use a monomial power X^d for putting back negative *external* powers.
-- priceMove written as a shift but is a literal product in the series algebra.
def priceMove (d:ℕ)(F:T E): T E := series.symm (PowerSeries.X^d) ∙ F
lemma shifts (Y:T E)(n d:ℕ) : priceMove d Y (n+d)=Y n:= by
    change (series.symm _ ∙ Y) (n+d)=_; rw [mul_price,Finset.sum_eq_single_of_mem (d,n) (by simp [Nat.add_comm])]; · change coeff d ((PowerSeries.X:Cn)^d) • _=_; simp
    intro k hk he; change coeff k.1 ((PowerSeries.X:Cn)^d) • _=_; rw [PowerSeries.coeff_X_pow, if_neg (show k.1 ≠ d from fun h=>he (Prod.ext h (by dsimp; have hc:= Finset.mem_antidiagonal.mp hk; omega))),zero_smul]
lemma shifts_zero {n d:ℕ}(Y:T E)(h:n < d): priceMove d Y n=0:= by
    unfold priceMove; rw [mul_price]; apply Finset.sum_eq_zero; intro k hk; change coeff k.1 ((PowerSeries.X:Cn)^d) • _=_; rw [PowerSeries.coeff_X_pow,if_neg (show k.1≠d by obtain ht:= mem_antidiagonal.mp hk; omega),zero_smul]
omit [Fintype V] in
lemma prefactor {O:Raw V ℂ} {d:ℕ} (hd:From O d) : rankLevel 0 O= priceMove d (rankLevel d O):= by
    funext i; obtain he|he:= lt_or_ge i d; · rw [shifts_zero _ he]; funext l; unfold rankLevel; by_cases hv:(l.length:ℤ)=(i:ℤ)+0; exact (enough _ hv).trans (hd _ (by omega)); exact strange _ hv
    obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le' he; rw [shifts]; unfold rankLevel; norm_num

namespace EndRule
variable (p) (K:Grain V) (Q X: SpecB V)
local notation "M"=> PermV p
local infixl:70 " ★ "=> Actors.core (PermV p)
local notation "R"=> exp0 p Q
local notation "P"=> ℶV K R
def top (p:Sector V)(K:Grain V)(Q:SpecB V): Linear (SpecB V) (T ℂ):= (ℶV K) ∘ₗ ((PermV p).core (exp0 p Q))
def pay (p:Sector V)(K:Grain V)(Q:SpecB V) := (series (ℶV K (exp0 p Q)))⁻¹
def response (p:Sector V)(K:Grain V)(Q:SpecB V): Linear (SpecB V) (T ℂ) := (Trunk.core (series.symm (EndRule.pay p K Q))) ∘ₗ EndRule.top p K Q
lemma agrees (h:Q 0=0) (X:SpecB V) : Endμ K p Q X (response p K Q X):= by
    let S:=series P; have he:P 0=1:= Swirl.yetB (p:=p) h
    unfold Endμ; change _= P ⚘ (series.symm S⁻¹ ⚘ ℶV K (R ★ X)); apply series.injective; simp_rw [scalar_series,series.apply_symm_apply]; rw [← mul_assoc]; change _= S*S⁻¹ * _; rw [PowerSeries.mul_inv_cancel S (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact ((pack P 0).trans he).trans_ne one_ne_zero),one_mul] -- power series nondivision!
lemma unique (h:Q 0=0)(Z:T ℂ) (hz:Endμ K p Q X Z) : response p K Q X=Z:= Swirl.classicalμ h (agrees p K Q h X) hz
lemma natural (F:T ℂ) : response p K Q (F ∙ X)= F ∙ (response p K Q X) := by
    let V := series.symm (EndRule.pay p K Q)
    change V ⚘ (promote (View K) (pairW (product p) _ (F ∙ X)))= F ∙ (V ⚘ promote (View K) (pairW (product p) _ X))
    rw [price_right, price_pair, price_scalar, price_twice V F, price_scalar]
end EndRule
end YM.WilsonBridge
