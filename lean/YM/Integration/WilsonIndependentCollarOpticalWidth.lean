import YM.Integration.WilsonIndependentCollarShortHistory

/-! Interpolate directly at each original width. The entire growing collar
then costs a single square of the largest local Wilson price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalWidth
open Function Finset Lattice RG Wilson Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonReceivedFixedDigitHistory
open scoped BigOperators Classical

private theorem deposit {v W P B t s D:ℝ} (hv:0≤v) (weak:v≤W) (_pos:0≤P) (bpos:0≤B)
    (strong:v≤P*Real.exp (-t*D)) (room:W*P^2≤B^3) (width:2*t=3*s):
    v≤B*Real.exp (-s*D):=by
  have ep:(Real.exp (-t*D))^2=(Real.exp (-s*D))^3:=by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul];congr 1;norm_num; nlinarith [congr_arg (fun z:ℝ=>z*D) width]
  apply (pow_le_pow_iff_left₀ hv (by positivity) (by decide : 3≠0)).mp
  calc v^3 = v*v^2:=by ring
       _ ≤ W*(P*Real.exp (-t*D))^2:=mul_le_mul weak (pow_le_pow_left₀ hv strong _)
         (sq_nonneg _) (hv.trans weak)
       _ ≤ (B*Real.exp (-s*D))^3:=by
         rw [mul_pow,ep,←mul_assoc,mul_pow]
         exact mul_le_mul_of_nonneg_right room (by positivity)

theorem opening {U α V ι:Type} [NormedAddCommGroup V] {r:ℕ} (d:Bank.Distance U)
    (p:ι→U) (S:Finset ι) (X:Ten V (U×α) r) {τ σ M T:ℝ} (width:2*τ=3*σ)
    (weak:Wig d p 0 (M^S.card) S X) (Mpos:0≤M) (Tpos:0≤T)
    (strong:Wig d p τ ((T*(T^2*M))^S.card) S X):
    Wig d p σ ((T^2*M)^S.card) S X:=by
  refine ⟨by positivity,?_⟩; intro x
  apply deposit (norm_nonneg _) (show ‖X x‖≤M^S.card by simpa using weak.2 x)
    (by positivity) (by positivity) (strong.2 x) _ width
  apply le_of_eq
  calc
    M^S.card*((T*(T^2*M))^S.card)^2 = (M*(T*(T^2*M))^2)^S.card:=by rw [←pow_mul,pow_mul',mul_pow,←mul_pow]
    _ = ((T^2*M)^S.card)^3:=by rw [show M*(T*(T^2*M))^2=(T^2*M)^3 by ring,←pow_mul,←pow_mul,Nat.mul_comm]

variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}

/-- Only the cheap unweighted connected kernel and the top enrolment enter
the induction. The older strong account is proved at every actual block. -/
theorem original (Q:Realm G (e+1) Credit.leanC) (policy:Cloze D k Q Credit.leanC)
    (N:ℕ) (cell:Digits Q.draws ι) (Y:Outerm G D) (well:Wellness k Y) (M T:ℝ)
    (hM:0≤M) (hT:1≤T) (days m:ℕ) (hm:Q.anchor ≤ m) (cut:m+days≤N)
    (price:∀ j, m ≤ j → j < m+days → Q.cash (vigor G D k e Credit.leanC Credit.leanC) j ≤ T)
    (width:∀ j (hj:Q.anchor≤ j), m ≤ j → j < m+days →
      2*elixir (Q.mint j hj).gear=3*(Q.mint j hj).σ)
    (low:∀ j d, m ≤ j → j+d=m+days → ∀ y S,shingled y S
      (itinerary Q.draws Q.paid k N cell d j Y) e 0 M)
    (incoming:Uniform Q Y (m+days) (by omega) (T^2*M)):
    Uniform Q (itinerary Q.draws Q.paid k N cell days m Y) m hm (T^2*M):=by
  induction days generalizing m with
  | zero=>simpa [itinerary] using incoming
  | succ d ih=>
    let U:=itinerary Q.draws Q.paid k N cell d (m+1) Y
    have hw:Wellness k U:=sound Q.draws Q.paid k N cell Q.hG Q.green Y well d (m+1) (by omega)
    have mid:Uniform Q U (m+1) (by omega) (T^2*M):=by
      apply ih (m+1) (by omega) (by omega) (fun j h v=>price j (by omega) (by omega))
        (fun j h v f=>width j h (by omega) (by omega)) (fun j d' h v=>low j d' (by omega) (by omega))
      simpa only [Nat.add_assoc,Nat.add_comm 1 d] using incoming
    intro y S q hq r
    let x:=chartIn (loose Q.draws m) y (cell m)
    have top:=one_shore policy (U x) (hw.level' x) (hw.quiet' x) m N hm (by omega)
      y (cell m) (S:=S) (A:=T^2*M) (fun J _ o ho l=>mid x J o ho l) (by positivity)
    apply opening _ y S _ (width m hm le_rfl (by omega)) (low m (d+1) le_rfl rfl y S q hq r)
      hM (zero_le_one.trans hT)
    apply (top S (by rfl) q hq r).more
    apply pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth _ hm))) (by positivity))
    exact mul_le_mul_of_nonneg_right (price m le_rfl (by omega)) (by positivity)

end YM.Integration.WilsonIndependentCollarOpticalWidth
end
