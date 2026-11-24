import YM.Integration.WilsonReceivedFirstPrepaidReading

/-! Removing the paid old and fresh marker radii on the full submitted coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedFirstQIncidence
open Finset Marker QuadraticLocal Wilson RG
open scoped BigOperators Classical

/-- All four exponents are fixed by the originally enrolled tests. -/
def degree (old fresh raw pad:ℕ) : ℕ :=
  max (old+9) (max (fresh+7) (raw+pad+6))

def fee (old fresh raw κ:ℝ) : ℝ := 2*max old (max fresh raw)*(10+κ)

theorem priced {V:Type} [Fintype V] [DecidableEq V] {S:Marker.Census V} (mask:S.Mode)
    (old fresh:Finset V) (covered:mask.val⊆old∪fresh)
    (oldFree newFree r:V→ℝ) (oldPos:∀v,0<oldFree v) (newPos:∀v,0<newFree v)
    {x y C₀ C₁ C₂ Ω upper rebate h κ:ℝ} {d₀ d₁ d₂ pad:ℕ}
    (heat:1≤x) (rise:x≤y) (oldC:1≤C₀) (freshC:1≤C₁) (rawC:1≤C₂)
    (lowerOne:1≤Ω) (lowerCap:Ω≤y) (upperOne:1≤upper) (upperCap:upper≤y)
    (stamp:rebate≤y) (hOne:1≤h) (hCap:h≤(10+κ)*y^5) (κpos:0<κ)
    (oldAt:∀v∈old,r v=(oldFree v/(C₀*y^(d₀+1)*upper))/(max 1 (Ω*rebate))/2)
    (freshAt:∀v∈fresh,r v=min (newFree v/(C₁*x^(d₁+1)*Ω)/2)
      (newFree v/((C₂*x^(d₂+1))*x^pad))) :
    (∏ v∈mask.val,min (oldFree v) (newFree v))/(fee C₀ C₁ C₂ κ*y^(degree d₀ d₁ d₂ pad))^mask.val.card ≤
      Marker.Poly.toll (Stoop.radius r h) mask := by
  let C:=max C₀ (max C₁ C₂)
  let D:=degree d₀ d₁ d₂ pad
  let K:=10+κ
  let T:=fee C₀ C₁ C₂ κ
  have x₀:0<x:=zero_lt_one.trans_le heat
  have y₁:1≤y:=heat.trans rise
  have y₀:0<y:=x₀.trans_le rise
  have U:0<Ω:=zero_lt_one.trans_le lowerOne
  have A:0<upper:=zero_lt_one.trans_le upperOne
  have hh:0<h:=zero_lt_one.trans_le hOne
  have k₀:0<K:=by dsimp [K]; linarith
  have c₀:0<C₀:=zero_lt_one.trans_le oldC
  have c₁:0<C₁:=zero_lt_one.trans_le freshC
  have c₂:0<C₂:=zero_lt_one.trans_le rawC
  have c0:C₀≤C:=le_max_left _ _
  have c1:C₁≤C:=(le_max_left _ _).trans (le_max_right _ _)
  have c2:C₂≤C:=(le_max_right _ _).trans (le_max_right _ _)
  have cPos:=c₀.trans_le c0
  have t₀:0<T:=by change 0<2*C*K; positivity
  have base:0<T*y^D:=mul_pos t₀ (pow_pos y₀ _)
  have envelope:0 < max 1 (Ω*rebate):=zero_lt_one.trans_le (le_max_left _ _)
  have coverPrice:max 1 (Ω*rebate)≤y^2:=max_le (one_le_pow₀ y₁)
    ((mul_le_mul_of_nonneg_left stamp U.le).trans ((mul_le_mul_of_nonneg_right lowerCap y₀.le).trans_eq (sq _).symm))
  have oldBound:C₀*y^(d₀+1)*upper*max 1 (Ω*rebate)*2*h≤T*y^D:=by
    calc
      _ ≤ C*y^(d₀+1)*y*y^2*2*(K*y^5):=by gcongr
      _ = T*y^(d₀+9):=by change _=(2*C*K)*_; simp only [pow_add,pow_one]; ring
      _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ y₁ (le_max_left _ _)) t₀.le
  have newBound:C₁*x^(d₁+1)*Ω*2*h≤T*y^D:=by
    calc
      _ ≤ C*y^(d₁+1)*y*2*(K*y^5):=by gcongr
      _ = T*y^(d₁+7):=by change _=(2*C*K)*_; simp only [pow_add,pow_one]; ring
      _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ y₁ ((le_max_left _ _).trans (le_max_right _ _))) t₀.le
  have rawBound:C₂*x^(d₂+1)*x^pad*h≤T*y^D:=by
    calc
      _ ≤ C*y^(d₂+1)*y^pad*(K*y^5):=by gcongr
      _ ≤ 2*(C*y^(d₂+1)*y^pad*(K*y^5)):=le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = T*y^(d₂+pad+6):=by change _=(2*C*K)*_; simp only [pow_add,pow_one]; ring
      _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ y₁ ((le_max_right _ _).trans (le_max_right _ _))) t₀.le
  have entry (v:V) (seen:v∈mask.val) :
      min (oldFree v) (newFree v)/(T*y^D)≤Stoop.radius r h v:=by
    let a:=min (oldFree v) (newFree v)
    change a/(T*y^D)≤r v/h
    rcases mem_union.mp (covered seen) with oldLive|newLive
    · rw [oldAt v oldLive,div_div,div_div,div_div]
      exact div_le_div₀ (oldPos v).le (min_le_left _ _) (by positivity) (by simpa only [mul_assoc] using oldBound)
    · rw [freshAt v newLive]
      rcases le_total (newFree v/(C₁*x^(d₁+1)*Ω)/2) (newFree v/((C₂*x^(d₂+1))*x^pad)) with first|second
      · rw [min_eq_left first,div_div,div_div]
        exact div_le_div₀ (newPos v).le (min_le_right _ _) (by positivity) (by simpa only [mul_assoc] using newBound)
      · rw [min_eq_right second,div_div]
        exact div_le_div₀ (newPos v).le (min_le_right _ _) (by positivity) rawBound
  calc
    _ = ∏v∈mask.val,min (oldFree v) (newFree v)/(T*y^D) :=by
      rw [Finset.prod_div_distrib]; simp only [Finset.prod_const]; rfl
    _ ≤ _:=Finset.prod_le_prod (fun v _=>div_nonneg (le_min (oldPos v).le (newPos v).le) base.le) entry

/-- Undoing the complete coefficient radius at the measured coupling loses two powers per degree and slot. -/
theorem hearing {V:Type} [Fintype V] [DecidableEq V] {S:Marker.Census V} (mask:S.Mode)
    {r:V→ℝ} {g heat T sources amount ε:ℝ} {D p q:ℕ}
    (gp:0<g) (small:g≤1) (heat₀:0<heat) (same:heat*g^2≤4) (fee₀:0<T) (source₀:0<sources)
    (ep:0<ε) (value:0≤amount)
    (wallet:sources/(T*heat^D)^mask.val.card≤Marker.Poly.toll r mask)
    (earned:Marker.Poly.toll r mask * amount ≤
      (ε*sources/(T^mask.val.card*4^(D*mask.val.card)))*g^p)
    (margin:q+2*(D*mask.val.card)≤p) : amount≤ε*g^q:=by
  let n:=mask.val.card
  let d:=D*n
  have n₀:0<(T*heat^D)^n:=by positivity
  have a:amount≤((T*heat^D)^n/sources) *
      ((ε*sources/(T^n*4^d))*g^p):=by
    have invoice: (sources/(T*heat^D)^n)*amount ≤ (ε*sources/(T^n*4^d))*g^p:=
      (mul_le_mul_of_nonneg_right wallet value).trans earned
    calc
      _ = ((T*heat^D)^n/sources)*((sources/(T*heat^D)^n)*amount):=by field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_left invoice (div_nonneg n₀.le source₀.le)
  have afford:q+2*d≤p:=margin
  have used:heat^d*g^p≤4^d*g^q:=by
    calc
      _ ≤ heat^d*g^(2*d+q):=mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le small (by omega)) (pow_nonneg heat₀.le _)
      _ = (heat*g^2)^d*g^q:=by rw [pow_add,mul_pow,←pow_mul]; ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg heat₀.le (sq_nonneg _)) same d) (pow_nonneg gp.le _)
  calc
    _ ≤ _:=a
    _ = (ε/4^d)*(heat^d*g^p):=by dsimp [d,n]; rw [mul_pow,←pow_mul]; field_simp
    _ ≤ (ε/4^d)*(4^d*g^q):=mul_le_mul_of_nonneg_left used (by positivity)
    _ = _:=by field_simp

end YM.Integration.WilsonReceivedFirstQIncidence
