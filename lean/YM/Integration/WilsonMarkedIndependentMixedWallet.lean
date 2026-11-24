import YM.Integration.WilsonMarkedIndependentMixedSeam

/-! The complete finite and folded connected logarithms on one enrolled
side. The quiet change and every proper marked change are heard jointly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedWallet
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonMarkedIndependentMixedGeometry
open WilsonVacuumPreResetMarkedOrdinaryBound (weights)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]

theorem original (D k:ι→ℕ)(I:Finset ι)(alive:I.Nonempty)(e i r:ℕ)(hi:i≤e):
    ∃v:Gear G→ℝ,∃d:ℕ,∀(Q:Realm G (e+1) Credit.leanC)(j N:ℕ)(a:Q.anchor≤j),
    v (Q.mint j a).gear≤Q.cash Credit.leanC j → j<N → ∀(y:ι → Cover)(b:ι→Site (loose Q.draws j).L)
    (E:family G D)(A B:ℝ),0≤A → 0<B → Eu k E → E ∅=0 →
    safeB (chartIn (loose Q.draws j) y b) E I e (Q.mint j a).gear.past A →
    ∀(n:Side)(η:ℝ),0<η → η≤1 → room n y I →
    let f:=n*(loose Q.draws j).L
    table Q.draws Q.paid e N (j+1) f η →
    (∀J⊆I,J.Nonempty → ∀t≤e,∀s x,
      ‖(E J).1 f t s x-plume ((E J).2 t s) f x‖≤B^J.card*η) →
    ∀x,let gold:=logO Q.draws Q.paid j N E k I
       ‖gold.1 n i r x-plume (gold.2 i r) n x‖≤
          (gross (Q.y j) f)^d*(A+B)^I.card*(η+Real.exp (-(n.val:ℝ)/(512*Q.y j))):=by
  obtain ⟨vf,M,hM,df,back⟩:=WilsonVacuumPreResetMarkedFiniteSourcePrice.original G D I k e i r hi
  obtain ⟨vs,ds,seam⟩:=WilsonMarkedIndependentMixedSeam.original (G:=G) D k I alive e i r hi
  let c(Z:Gear G):=diamond G e (mass k I) Z.past
  let v(Z:Gear G):=max (vf Z) (max (vs Z) (max M (c Z)))
  let d:=1+df+I.card+ds
  refine ⟨v,d,?_⟩
  intro Q j N a cash live y b E A B a0 b0 lawful blank read n η pos unit near f quiet marked x gold
  let Z:=(Q.mint j a).gear
  let z:=Q.y j
  let H:=gross z f
  let fresh:=Real.exp (-(n.val:ℝ)/(512*z))
  have fee:v Z≤z:=by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using cash
  have z1:1≤z:=Q.depth j a
  have hz:z≤H:=le_mul_of_one_le_right (zero_le_one.trans z1)
    (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg f.val (α:=ℝ))))
  have one:1≤H:=z1.trans hz
  have fpay:vf Z≤Q.cash Credit.leanC j:=(le_max_left ..).trans cash
  have spay:vs Z≤Q.cash Credit.leanC j:=(le_max_left ..).trans ((le_max_right ..).trans cash)
  have mp:M≤H:=(le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (fee.trans hz)))
  have cp:c Z≤H:=(le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (fee.trans hz)))
  have c1:1≤c Z:=diamond_nn G Z.depth
  let coef:=c Z*A+B
  let price:ι→ℝ:=fun _=>coef
  have a1:c Z*A≤coef:=le_add_of_nonneg_right b0.le
  have b1:B≤coef:=le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans c1) a0)
  have weights_eq(J:Finset ι):weights price J=coef^J.card:=by simp only [weights,price,Finset.prod_const]
  let prior:=back Q j a fpay N live n η pos unit (fun t cut s _ w=>quiet t cut s w)
    E (repaint E) lawful price (fun _=>b0.trans_le b1)
  have account:=WilsonMarkedIndependentMixedSeam.folded Q j N a live y b I E A a0 lawful blank read n
  have response:=prior (by
    intro J sub act t ht s _h w
    rw [weights_eq]
    constructor
    · exact (account J sub t ht s w).trans (pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans c1) a0) a1 _)
    · exact (marked J sub act t ht s w).trans (by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ b0.le b1 _) pos.le)) x
  let folded:=coilH Q.draws Q.paid j N n E k (ratioHigh Q.draws Q.paid N j) I i r x
  change ‖gold.1 n i r x-folded‖≤M*H^df*(weights price I)*η at response
  rw [weights_eq] at response
  have cap:=seam Q j N a spay live y b E A a0 lawful blank read n near x
  have c0:0≤A+B:=add_nonneg a0 b0.le
  have bound:coef≤H*(A+B):=by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right cp a0) (le_mul_of_one_le_left b0.le one)
  have cost:M*H^df*coef^I.card≤H^d*(A+B)^I.card:=calc
    _≤H*H^df*(H*(A+B))^I.card:=mul_le_mul (mul_le_mul_of_nonneg_right mp (pow_nonneg (zero_le_one.trans one) _))
      (pow_le_pow_left₀ (b0.trans_le b1).le bound _) (pow_nonneg (b0.trans_le b1).le _) (by positivity [one])
    _=H^(1+df+I.card)*(A+B)^I.card:=by rw [mul_pow];simp only [pow_add,pow_one];ring
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one (show 1+df+I.card≤d by dsimp [d];omega)) (pow_nonneg c0 _)
  have costs:z^ds*A^I.card≤H^d*(A+B)^I.card:=mul_le_mul
    ((pow_le_pow_left₀ (zero_le_one.trans z1) hz _).trans
      (pow_le_pow_right₀ one (show ds≤d by dsimp [d];omega)))
    (pow_le_pow_left₀ a0 (le_add_of_nonneg_right b0.le) _) (pow_nonneg a0 _) (pow_nonneg (zero_le_one.trans one) _)
  have triangle:=dist_triangle (gold.1 n i r x) folded (plume (gold.2 i r) n x)
  simp only [dist_eq_norm] at triangle
  apply triangle.trans
  rw [mul_add]
  exact add_le_add (response.trans (mul_le_mul_of_nonneg_right cost pos.le))
    (cap.trans (mul_le_mul_of_nonneg_right costs (Real.exp_pos _).le))

end YM.Integration.WilsonMarkedIndependentMixedWallet
end
