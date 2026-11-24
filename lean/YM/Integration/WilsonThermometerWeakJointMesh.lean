import YM.Integration.WilsonThermometerWeakSkyReach
import YM.Integration.WilsonThermometerWeakJointWidth

/-! A single true physical mesh houses the earlier ordinary probe and the
actual reporting field. Its price is bought before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakJointMesh
open Filter Set Lattice RG Push Next.Rank Next.Rank.Station MergeProof MergeProof.East
open PhysicalNext.Repeat.Legato Next.Rank.Tapes Next.Rank.Price
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.alloy.B.a

open WilsonThermometerWeakJointWidth

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (a b:ℝ) (posA:0<a) (posB:0<b) (e:ℕ):
    ∀ᶠ k:ℕ in atTop,∀ ℓ≥k,(A).S.scale ℓ-(A).S.scale k ≤ Real.log ((A).clock.hatBeta ℓ) →
    Allowed (A) b k →
    wheel (A) k ≤ (A).clock.monitor k →
    let i:=widthSky (A) a ℓ;let j:=width (A) b k;let m:=min i j-e
    m+e  ≤  i ∧ m+e  ≤  j ∧ (A).S.a m ≤ gap (A) (power a b e) k:=by
  let B:=max (4*(a+5)) (b+5)
  have near:=eventually_atTop.mp (WilsonThermometerWeakSkyReach.original R simple shop)
  obtain ⟨n₀,sky⟩:=near
  obtain ⟨n₁,blocks⟩:=eventually_atTop.mp (WilsonThermometerWeakPastBlocks.paid R simple shop)
  have clears:= (gap_rate (A) simple B).eventually_lt_const ((A).S.a_pos e)
  filter_upwards [eventually_ge_atTop n₀,eventually_ge_atTop n₁,clears,
    WilsonThermometerWeakStarRatio.original (A) simple,echo_scale (A) simple b posB]
      with k hk₀ hk₁ clear cap shaft ℓ later span ordinary ordinaryCap
  let X:=(A).clock.monitor ℓ
  let M:=(A).clock.monitor k
  have cross:X ≤ M^4:=cap ℓ later span
  have mx:1 ≤ X:=Real.one_le_exp (sq_nonneg _)
  have mm:1 ≤ M:=Real.one_le_exp (sq_nonneg _)
  have pm:0 ≤ M:=zero_le_one.trans mm
  let i:=widthSky (A) a ℓ;let j:=width (A) b k
  have si:=(sky ℓ (hk₀.trans later)) a posA
  have sj:=shaft ordinary ordinaryCap
  rw [←Atlas.mag_bill] at si sj
  have fi:0 ≤ a+5:=by linarith
  have xs:X^(a+5) ≤ M^B:=by
    calc
      X^(a+5)  ≤  (M^4)^(a+5):=Real.rpow_le_rpow (zero_le_one.trans mx) cross fi
      _ = M^(4*(a+5)):=by rw [Real.rpow_mul pm];norm_num
      _  ≤  _:=Real.rpow_le_rpow_of_exponent_le mm (le_max_left ..)
  have aᵢ:(A).S.a i ≤ gap (A) B k:=
    ((div_le_iff₀ ((A).S.a_pos ℓ)).mp si).trans <| by
      change X^(a+5)*(A).S.a ℓ ≤ (A).S.a k*M^B
      rw [mul_comm];exact mul_le_mul ((A).S.strictAnti.antitone later) xs (Real.rpow_nonneg (zero_le_one.trans mx) _) ((A).S.a_pos _).le
  have aⱼ:(A).S.a j ≤ gap (A) B k:=
    ((div_le_iff₀ ((A).S.a_pos k)).mp sj).trans <| by
      change M^(b+5)*(A).S.a k ≤ (A).S.a k*M^B
      rw [mul_comm];exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le mm (le_max_right ..)) ((A).S.a_pos _).le
  have mat:(A).S.a (min i j) ≤ gap (A) B k:=by rcases le_total i j with h|h;simpa [min_eq_left h] using aᵢ;simpa [min_eq_right h] using aⱼ
  have depth:e ≤ min i j:=le_of_not_ge (fun h=>((mat.trans_lt clear).not_ge ((A).S.strictAnti.antitone h)))
  have legal:min i j ≤ ℓ:=(min_le_left ..).trans ((widerSky (A) a ℓ).trans (beforeSky ..))
  dsimp only
  refine ⟨by dsimp [i,j] at depth ⊢;omega,by dsimp [i,j] at depth ⊢;omega,?_⟩
  have paid:=WilsonThermometerWeakPastBlocks.earlier (A).S e mx (blocks ℓ (hk₁.trans later)) (min i j) legal
  calc
    _  ≤  _ := paid
    _  ≤  (M^4)^e*gap (A) B k:=mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans mx) cross e) mat
      ((A).S.a_pos _).le (by positivity)
    _ = gap (A) (power a b e) k:=by
      change (M^4)^e*((A).S.a k*M^B)=(A).S.a k*M^(4*(e:ℝ)+B)
      rw [Real.rpow_add (zero_lt_one.trans_le mm),Real.rpow_mul pm]
      norm_cast
      ring

end YM.Integration.WilsonThermometerWeakJointMesh
end
