import YM.Integration.WilsonPointChildQuoteWidth
import YM.Integration.WilsonMarkedIndependentNormalizedSeam
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildDigitGazette
open Function Filter Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open scoped Classical BigOperators
open WilsonPointChildScalarSlot
variable {G:Gauge}

abbrev born(d:ℕ):Unit→ℕ:=fun _=>d

private theorem paidAt {root:Unit → Cover}{X:Era G ℝ}{e:ℕ}{s A:ℝ}(hp:0≤A)
    (h:∀i≤e,∀r,Wig terrain root s A {()} (X.2 i r)):
    safeB root (roster X) {()} e s (‖inlet‖*A):=by
  intro J _ i hi r
  by_cases hj:J={⟨⟩}
  · subst J
    rw [full,Finset.card_singleton,pow_one]
    refine ⟨mul_nonneg (norm_nonneg inlet) hp,?_⟩
    intro z
    change ‖inlet (X.2 i r z)‖≤_
    exact (inlet.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ((h i hi r).2 z) (norm_nonneg inlet)).trans_eq
      (by ring))
  · rw [roster,dif_neg hj]
    exact Wig.zero.more (pow_nonneg (mul_nonneg (norm_nonneg inlet) hp) _)


/-- The fresh winding discrepancy is assessed on the before-test pointed row
at its actual fine support. The saved upper transfer may have any age. -/
theorem submitted (G:Gauge)(d e i r:ℕ)(hi:i≤e):
    ∃v σ:Gear G→ℝ,∃k:ℕ,(∀I,0<σ I ∧ (σ I)⁻¹≤v I) ∧
    ∀(Q:Realm G (e+1) Credit.leanC) j N (a:Q.anchor≤j),
      v (Q.mint j a).gear≤Q.cash Credit.leanC j → j<N → ∀(z:Site (loose Q.draws j).L)(n:Side)(X:Era G ℝ),Auth d X→∀A:ℝ,0≤A→
      (∀b≤e,∀t,Wig terrain (fun _:Unit=>lift z) (WilsonPointChildQuoteWidth.quote (Q.mint j a).gear)
        A {()} (X.2 b t))→
      let E:=roster X
      let flat:=(logO Q.draws Q.paid j N E (born d) {()}).2 i r
      let terms:=coilH Q.draws Q.paid j N n E (born d) (ratioHigh Q.draws Q.paid N j) {()} i r
      Wig (tor n) (fun _:Unit=>0) (σ (Q.mint j a).gear/32/2)
        ((Q.y j)^k*(‖inlet‖*A)*Real.exp (-(n.val:ℝ)/(512*Q.y j))) {()} (Carp.plume flat n-terms):=by
  obtain ⟨σ,c,U,strip,step⟩:=pledges G e i r hi Credit.leanC Credit.leanC WilsonPointChildQuoteWidth.quote
    WilsonPointChildQuoteWidth.positive (J:={()}) (Z:={()}) le_rfl grade (born d)
  let cost(I:Gear G):=priceM (Hooks G) r (σ I)+tiePay (Hooks G) r (σ I/4)+2
  let v(I:Gear G):=max (c I) (max (cost I) U.x)
  refine ⟨v,σ,U.d+2,fun I=>⟨(strip I).1,(strip I).2.trans (le_max_left ..)⟩,?_⟩
  intro Q j N a wallet live z n X authorized B hB earned
  let I:=(Q.mint j a).gear
  let y₀:=Q.y j
  let A:=‖inlet‖*B
  let y:Unit → Cover:=fun _=>0
  let b:Unit → Site (loose Q.draws j).L:=fun _=>z
  let E:=roster X
  have fee:v I≤y₀:=by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using wallet
  have Epos:0≤A:=mul_nonneg (norm_nonneg inlet) hB
  have approve:c I≤Q.cash Credit.leanC j:=(le_max_left ..).trans wallet
  have chart:chartIn (loose Q.draws j) y b=(fun _:Unit=>lift z):=by
    funext t; simp [chartIn,y,b]
  have entry:safeB (chartIn (loose Q.draws j) y b) E {()} e (WilsonPointChildQuoteWidth.quote I) A:=by
    rw [chart];exact paidAt hB earned
  have store:=step Q j N n a live approve E (legal authorized) (empty X) y b A Epos entry
  have he:(4*crestCard y {()})<n.val:=by
    have one:crestCard y {()}=0:=by
      apply Nat.eq_zero_of_le_zero;apply league_le;intro a b;exact (terrain.self _).le
    rw [one];simp
  have price:=markOrbit store (Finset.singleton_nonempty ()) he (strip I).1
  have atzero:wrap n ∘ y=(fun _:Unit=>0):=by funext t;simp [y]
  rw [atzero] at price
  apply price.more
  have reserve:0<y₀:=zero_lt_one.trans_le (Q.depth j a)
  have rate:1≤σ I*y₀:=calc
    _=σ I*(σ I)⁻¹:=(mul_inv_cancel₀ (strip I).1.ne').symm
    _≤_:=mul_le_mul_of_nonneg_left ((strip I).2.trans ((le_max_left ..).trans fee)) (strip I).1.le
  have flat:catchW (σ I/32/16) n ≤ Real.exp (-(n.val:ℝ)/(512*y₀)):=by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ (by positivity:0<512*y₀)).2
    change (-(σ I/32/16)*(n.val:ℝ))*(512*y₀) ≤ -(n.val:ℝ)
    nlinarith only [mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg n.val (α:=ℝ))]
  have rent:Q.cash U j≤y₀^(U.d+1):=by
    change U.x*y₀^U.d≤_
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right ((le_max_right ..).trans ((le_max_right ..).trans fee)) (pow_nonneg reserve.le _)
  have cpay:cost I≤y₀:=(le_max_left ..).trans ((le_max_right ..).trans fee)
  have nonneg:0≤Q.cash U j:=zero_le_one.trans (U.purchase (Q.depth j a))
  simp only [Finset.card_singleton,pow_one]
  have overhead:(priceM (Hooks G) r (σ I)+tiePay (Hooks G) r (σ I/4)+1)*(Q.cash U j*A)+Q.cash U j*A≤y₀^(U.d+2)*A:=calc
    _ = (cost I)*(Q.cash U j)*A:=by dsimp [cost];ring
    _ ≤ (y₀*y₀^(U.d+1))*A:=mul_le_mul_of_nonneg_right (mul_le_mul cpay rent nonneg reserve.le) Epos
    _ = _:=by rw [←pow_succ']
  exact mul_le_mul overhead flat (catch_hot ..) (mul_nonneg (pow_nonneg reserve.le _) Epos)



end YM.Integration.WilsonPointChildDigitGazette
