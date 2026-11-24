import YM.Integration.WilsonVacuumPreResetFiniteHeatTable

/-! The finite family of one-date quotes is enrolled before the course.
All the underlying finite rows and the independent fresh tensor are read
on the one submitted physical period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatStep
open Function Filter Finset Lattice RG Wilson Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open ActualRunAdmissionScales Next.Foundations PhysicalNext.Repeat.Legato
open WilsonVacuumPreResetFiniteHeatTable WilsonVacuumPreResetFiniteHeatScale
open scoped Topology Classical BigOperators
variable {G:Gauge}

/-- All finite angular rows under the measured reset on the actual side.
The quote precedes the original course and both physical regulators. -/
theorem original (G:Gauge)(e:ℕ):
    ∃v:ℕ→Gear G→ℝ,∀(R:Run G),G.Simple→RG05Preconstruction.ReadoutPurchase R.b→
      ∀ᶠm:ℕ in atTop,∀(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m),
      Q.draws=R.family.path.levels→Q.paid=R.metals.O→Q.y=zz R.family.path.levels→
      v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m→
      ∀N p:ℕ,m<N→
      table R.family.path.levels R.metals.O e N (m+1) (R.family.side (m+1) p) (rate R.family.path.levels (m+1) p)→
      table R.family.path.levels R.metals.O e N m (R.family.side m p) (rate R.family.path.levels m p):=by
  classical
  let T:=Fin (e+1)×Fin (e+2)
  choose u d upper using fun t:T=>WilsonVacuumPreResetFiniteHeatFinance.original G e t.1.val (t.2.val+1) (by omega)
  choose w k reset using fun t:T=>WilsonVacuumPreResetFiniteHeatCourse.reversion G e t.1.val (t.2.val+1) (by omega)
  choose b h correction using fun t:T=>WilsonVacuumPreResetFiniteHeatCourse.fresh G e t.1.val t.2.val (by omega)
  let v(j:ℕ)(I:Gear G):ℝ:=∑t:T,(|u t I|+|w t I|+|b t j I|)
  let M:=∑t:T,(d t+k t+h t)
  have degree(t:T):d t ≤ M ∧ k t ≤ M ∧ h t ≤ M:=by
    have row:d t+k t+h t ≤ M:=Finset.single_le_sum (f:=fun q:T=>d q+k q+h q) (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)
    omega
  have fees(t:T)(j:ℕ)(I:Gear G):u t I ≤ v j I ∧ w t I ≤ v j I ∧ b t j I ≤ v j I:=by
    have row:|u t I|+|w t I|+|b t j I| ≤ v j I:=Finset.single_le_sum (f:=fun q:T=>|u q I|+|w q I|+|b q j I|) (fun _ _=>by positivity) (Finset.mem_univ t)
    constructor
    · linarith [le_abs_self (u t I),abs_nonneg (w t I),abs_nonneg (b t j I)]
    constructor
    · linarith [le_abs_self (w t I),abs_nonneg (u t I),abs_nonneg (b t j I)]
    · linarith [le_abs_self (b t j I),abs_nonneg (u t I),abs_nonneg (w t I)]
  refine ⟨v,?_⟩
  intro R simple reading
  have fresh_all:=Filter.eventually_all.mpr (fun t:T=>correction t R simple reading)
  filter_upwards [fresh_all,WilsonVacuumPreResetFiniteHeatScale.original R simple reading (2*M)] with m fresh price
  intro Q hm draws O clock bill N p live received
  let L:=R.family.path.levels
  let z:=zz L m
  let C:=admittedCost L m
  let n:=R.family.side m p
  let f:=R.family.side (m+1) p
  let I:=(Q.mint m hm).gear
  let J:=L.clock.J (m+1)
  let B:=WilsonVacuumPreResetFiniteHeatFinance.gross z f
  let η:=rate L (m+1) p
  let age:=Real.exp (-(n.val:ℝ)/(4*z))
  have intended:f=n*(loose Q.draws m).L:=by
    rw [draws]
    exact Subtype.ext (R.family.path.levels.clock.op m p).sizes
  have hz:1 ≤ z:=by simpa only [clock] using Q.depth m hm
  have hz':0<zz L (m+1):=by simpa only [clock] using
    (zero_lt_one.trans_le (Q.depth (m+1) (by omega)))
  have hc:1 ≤ C:=admittedCost_one L m
  have fin0:0 ≤ (f.val:ℝ):=Nat.cast_nonneg _
  have hzB:z ≤ B:=by
    change z ≤ z*(1+(f.val:ℝ))^4
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith))
  have hB:1 ≤ B:=hz.trans hzB
  have hη:0<η:=Real.exp_pos _
  have ηle:η ≤ 1:=by
    apply Real.exp_le_one_iff.mpr
    change -(f.val:ℝ)/(16*zz L (m+1)) ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr fin0) (by positivity)
  have hab:0<age:=Real.exp_pos _
  have hp:=fees
  apply WilsonVacuumPreResetFiniteHeatTable.all R simple e N m live.le n (Real.exp_pos _).le
  intro i hi r hr x
  let t(a:ℕ)(ha:a ≤ i):T:=(⟨a,by omega⟩,⟨r,by omega⟩)
  have lower(a:ℕ)(ha:a ≤ i)(q):|unripe L R.metals.O N m (story L R.metals.O N (m+1)).1 n a (r+1) q-
      coil0 L R.metals.O m N n a (r+1) q| ≤ B^M*η:=by
    have rep:=upper (t a ha) Q m hm ((hp (t a ha) J I).1.trans bill) N live n η hη ηle
    change (∀a ≤ e,∀l ≤ _,∀x,|(story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l x-
      emera (actionW Q.draws Q.paid N (m+1)) (n*(loose Q.draws m).L) a l x| ≤ η)→_ at rep
    have coarse:=rep (by rw [←intended, draws,O];exact fun a' ha' l _ x'=>received a' ha' l x') q
    change |unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n a (r+1) q-
      coil0 Q.draws Q.paid m N n a (r+1) q| ≤ 
      WilsonVacuumPreResetFiniteHeatFinance.gross (Q.y m) (n*(loose Q.draws m).L)^(d (t a ha))*η at coarse
    rw [←intended,draws,O,clock] at coarse
    exact coarse.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (degree (t a ha)).1) hη.le)
  have cov(a:ℕ)(ha:a ≤ i)(q):|RootedVacuumWinding.ground L R.metals.O N m n a r q| ≤ C^M*age:=by
    have real:=fresh (t a ha) Q hm draws O clock ((hp (t a ha) J I).2.2.trans bill) N p live q
    rw [clock] at real
    exact real.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (degree (t a ha)).2.2) hab.le)
  have coin:=reset (t i le_rfl) Q m hm ((hp (t i le_rfl) J I).2.1.trans bill) N live
  rw [draws,O,clock] at coin
  have money:rimJ (ratioHigh L R.metals.O N m) i (r+1) ≤ z^M:=
    coin.trans (pow_le_pow_right₀ hz (degree (t i le_rfl)).2.1)
  have kept:=WilsonVacuumPreResetFiniteHeatReset.original L R.metals.O live n i r
    (Q.mint m hm).width (fun a ha=>by
      have term:=WilsonVacuumPreResetFiniteHeatCourse.shelf Q hm live a (r+1) (ha.trans hi)
      have parcel:freshet L R.metals.O N m a (r+1)=freshet Q.draws Q.paid N m a (r+1):=by rw [draws,O]
      rw [parcel]
      exact term) lower cov x
  have small:0 ≤ B^M*η+C^M*age:=add_nonneg
    (mul_nonneg (pow_nonneg (zero_le_one.trans hB) _) hη.le)
    (mul_nonneg (pow_nonneg (zero_le_one.trans hc) _) hab.le)
  calc
    _  ≤  rimJ (ratioHigh L R.metals.O N m) i (r+1)*(B^M*η+C^M*age):=kept
    _  ≤  z^M*(B^M*η+C^M*age):=mul_le_mul_of_nonneg_right money small
    _ = (z^M*B^M)*η+(z*C)^M*age:=by rw [mul_pow]; ring
    _  ≤  B^(2*M)*η+(z*C)^(2*M)*age:=by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ hη.le
        rw [two_mul,pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hz) hzB _) (pow_nonneg (zero_le_one.trans hB) _)
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hz hc) (by omega)) hab.le
    _  ≤  _:=price p

end YM.Integration.WilsonVacuumPreResetFiniteHeatStep
