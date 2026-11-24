import YM.Integration.WilsonMarkedIndependentMixedGeometry
import YM.Integration.WilsonVacuumPreResetMarkedFiniteSourcePrice

/-! The authentic upper cover cofactor and its Gazette seam on a compact
separated collection of marked positions, before applying any test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedSeam
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonMarkedIndependentMixedGeometry
open WilsonMarkedIndependentNormalizedWallet (raw)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι→ℕ}{e:ℕ}

omit [DecidableEq ι] in
private theorem price {s y:ℝ}(hs:0<s)(hy:0<y)(hw:s⁻¹≤y)(n:Side):
    catchW (s/32/16) n≤Real.exp (-(n.val:ℝ)/(512*y)):=by
  have h:1 ≤ s*y:=((mul_inv_cancel₀ hs.ne').symm.le).trans (mul_le_mul_of_nonneg_left hw hs.le)
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (by positivity:0<512*y)).mpr
  change (-(s/32/16)*(n.val:ℝ))*(512*y)≤-(n.val:ℝ)
  nlinarith only [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n.val (α:=ℝ))]

theorem folded (Q:Realm G (e+1) Credit.leanC)(j N:ℕ)(a:Q.anchor≤j)(live:j<N)(y:ι → Cover)
    (b:ι→Site (loose Q.draws j).L)(I:Finset ι)(E:family G D)(A:ℝ)(hA:0≤A)
    (legal:Eu k E)(zero:E ∅=0)
    (havePay:safeB (chartIn (loose Q.draws j) y b) E I e (Q.mint j a).gear.past A)(n:Side):
    let c:=diamond G e (mass k I) (Q.mint j a).gear.past
    ∀J⊆I,∀i≤e,∀r x,‖plume ((E J).2 i r) (n*(loose Q.draws j).L) x‖≤(c*A)^J.card:=by
  intro c J part i hi r x
  let Z:=(Q.mint j a).gear
  let card:=flowOne Q I E j N a live Z.past Z.depth y b zero legal A hA havePay n
  let s:=(holt Q j a Z.past Z.depth).s
  have bill:=card.shore J part i hi r
  change MarkU (chartIn (loose Q.draws j) y b) J (plume ((E J).2 i r) (n*(loose Q.draws j).L))
    ((E J).2 i r) s ((c*A)^J.card) at bill
  exact raw bill.bill (holt Q j a Z.past Z.depth).h.le x

/-- Both old proper marked subsets and a positive-grade occupied scalar remain
in the complete unprojected finite Wick contraction on its own booked side. -/
theorem original (D k:ι→ℕ)(I:Finset ι)(alive:I.Nonempty)(e i r:ℕ)(hi:i≤e):
    ∃v:Gear G→ℝ,∃d:ℕ,∀(Q:Realm G (e+1) Credit.leanC)(j N:ℕ)(a:Q.anchor≤j),
    v (Q.mint j a).gear≤Q.cash Credit.leanC j → j<N → ∀(y:ι → Cover)(b:ι→Site (loose Q.draws j).L)
    (E:family G D)(A:ℝ),0≤A → Eu k E → E ∅=0 →
    safeB (chartIn (loose Q.draws j) y b) E I e (Q.mint j a).gear.past A →
    ∀n:Side,room n y I → ∀x,‖coilH Q.draws Q.paid j N n E k (ratioHigh Q.draws Q.paid N j) I i r x-
      plume ((logO Q.draws Q.paid j N E k I).2 i r) n x‖≤
    (Q.y j)^d*A^I.card*Real.exp (-(n.val:ℝ)/(512*Q.y j)):=by
  obtain ⟨σ,c,U,strip,step⟩:=pledges G e i r hi Credit.leanC Credit.leanC
    (fun I=>I.past) (fun I=>I.depth) (J:=I) (Z:=I) le_rfl D k
  let cost(Z:Gear G):=priceM (Hooks G) r (σ Z)+tiePay (Hooks G) r (σ Z/4)+2
  let v(Z:Gear G):=max (c Z) (max (cost Z) U.x)
  refine ⟨v,U.d+2,?_⟩
  intro Q j N a cash live y b E A hA law blank registry n localRoom x
  let Z:=(Q.mint j a).gear
  let z:=Q.y j
  have fee:v Z≤z:=by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using cash
  have quoted:=step Q j N n a live ((le_max_left ..).trans cash) E law blank y b A hA registry
  have mark:=markOrbit quoted alive (small localRoom) (strip Z).1
  have z0:0<z:=zero_lt_one.trans_le (Q.depth j a)
  have flat:=price (strip Z).1 z0 ((strip Z).2.trans ((le_max_left ..).trans fee)) n
  have rent:Q.cash U j≤z^(U.d+1):=by
    change U.x*z^U.d≤_
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right ((le_max_right ..).trans ((le_max_right ..).trans fee)) (pow_nonneg z0.le _)
  have cpay:cost Z≤z:=(le_max_left ..).trans ((le_max_right ..).trans fee)
  let B:=A^I.card
  have hB:0≤B:=pow_nonneg hA _
  have budget:(priceM (Hooks G) r (σ Z)+tiePay (Hooks G) r (σ Z/4)+1)*(Q.cash U j*B)+Q.cash U j*B≤z^(U.d+2)*B:=calc
    _=(cost Z)*(Q.cash U j)*B:=by dsimp [cost];ring
    _≤(z*z^(U.d+1))*B:=mul_le_mul_of_nonneg_right (mul_le_mul cpay rent
       (zero_le_one.trans (U.purchase (Q.depth _ a))) z0.le) hB
    _=_:=by rw [←pow_succ']
  rw [norm_sub_rev]
  apply (raw mark (div_nonneg (div_nonneg (strip Z).1.le (by norm_num)) (by norm_num)) x).trans
  exact mul_le_mul budget flat (catch_hot ..) (mul_nonneg (pow_nonneg z0.le _) hB)

end YM.Integration.WilsonMarkedIndependentMixedSeam
end
