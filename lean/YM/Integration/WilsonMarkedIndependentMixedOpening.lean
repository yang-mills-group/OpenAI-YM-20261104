import YM.Integration.WilsonMarkedIndependentMixedLimit
import YM.WilsonCoeffUV.Emit.LayoutOpening

/-! For a booked finite source menu, both the actual separation gate and the
entire winding coefficient are polynomial in 1+log log hatβ. Thus the physical
reporting distance can be used before either regulator is chosen. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedOpening
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Layout
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentNormalizedHistory (planted)
open WilsonMarkedIndependentMixedStep (Entries)
open WilsonMarkedIndependentMixedHistory (Filed)
open WilsonMarkedIndependentMixedGeometry (room)
open WilsonMarkedIndependentMixedLimit (Heard)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

private def constant (c:ℝ):Credit:=⟨0,max 1 c,le_max_left ..⟩
private theorem covers (x c:ℝ):c≤(constant c).buy x:=by
  simpa only [constant,Credit.buy,pow_zero,mul_one] using le_max_right (1:ℝ) c

theorem prices (D k:Fin (a+1)→ℕ)(e:ℕ)(C W T:Credit):∃S:Credit,
    ∀(x:ℝ)(F:Fin (a+1)→ℝ),1≤x → (∀i,0≤F i) → (∀i,F i≤T.buy x) →
    let z:=x+∑i,C.buy x*F i
    W.buy z≤S.buy x ∧ galeGate G D k k e W Credit.leanC Credit.leanC z+12≤S.buy x:=by
  let aC:=constant (a+1)
  let U:=Credit.leanC.plus (aC.prodC (C.prodC T))
  let K:=iceBill G D k k e W Credit.leanC Credit.leanC
  let V:=(((constant 2).prodC K.behind).prodC Credit.leanC.behind).usingC U
  let S:=(W.usingC U).plus (V.plus (constant 12))
  refine ⟨S,?_⟩
  intro x F hx hp cap z
  have c:0≤C.buy x:=zero_le_one.trans (C.purchase hx)
  have t:0≤T.buy x:=zero_le_one.trans (T.purchase hx)
  have aw:(a:ℝ)+1≤aC.buy x:=covers _ _
  have z1:1≤z:=hx.trans (le_add_of_nonneg_right (sum_nonneg fun i _=>mul_nonneg c (hp i)))
  have sumprice:∑i,C.buy x*F i≤aC.buy x*(C.buy x*T.buy x):=calc
    _≤∑_i:Fin (a+1),C.buy x*T.buy x:=sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (cap i) c
    _=((a:ℝ)+1)*(C.buy x*T.buy x):=by simp [nsmul_eq_mul]
    _≤_:=mul_le_mul_of_nonneg_right aw (mul_nonneg c t)
  have aug:z≤U.buy x:=calc
    _≤x+aC.buy x*(C.buy x*T.buy x):=add_le_add le_rfl sumprice
    _≤_:=by simpa only [U,Credit.products,Credit.lean_cost] using Credit.fuel Credit.leanC (aC.prodC (C.prodC T)) hx
  have w:W.buy z≤(W.usingC U).buy x:=by simpa only [Credit.stock_up] using W.elder z1 aug
  have v:galeGate G D k k e W Credit.leanC Credit.leanC z≤V.buy x:=by
    rw [show V.buy x=((constant 2).buy (U.buy x)*K.behind.buy (U.buy x))*Credit.leanC.behind.buy (U.buy x) by
      simp only [V,Credit.stock_up,Credit.products]]
    change (2*K.behind.buy z)*Credit.leanC.behind.buy z≤_
    apply mul_le_mul _ (Credit.leanC.behind.elder z1 aug) (zero_le_one.trans (Credit.leanC.behind.purchase z1))
      (mul_nonneg (zero_le_one.trans ((constant 2).purchase (U.purchase hx)))
        (zero_le_one.trans (K.behind.purchase (U.purchase hx))))
    exact mul_le_mul (covers _ _) (K.behind.elder z1 aug) (zero_le_one.trans (K.behind.purchase z1))
      (zero_le_one.trans ((constant 2).purchase (U.purchase hx)))
  exact ⟨w.trans (Credit.thickens _ hx),(add_le_add v (covers _ _)).trans
    ((Credit.fuel V (constant 12) hx).trans (Credit.thickened _ hx))⟩

/-- Uniform enrollment on the entire reported source wallet. Any positive
multiple δ of the physical logarithmic distance separates all these histories.
The scalar receipt retains all proper marked subsets on the same occupied run. -/
theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(filed:Filed R l d h e)(T:Credit)(δ:ℝ)(hd:0<δ):
    let L:=R.family.path.levels
    let F:=deck (G:=G) l d h
    ∃S:Credit,∀ᶠm:ℕ in atTop,∀X:Herit F,(∀i,fee (F i) (X i) e≤T.buy (zz L m)) →
      ∀N p j:ℕ,m≤j → j≤N → ∀(q:Fin (a+1) → Cover)(I:Finset (Fin (a+1))),I.Nonempty →
      (∀i∈I,∀b∈I,i≠b → δ*longLog L m≤Bank.terrain.gap (carrierR L.S m j (q i)) (carrierR L.S m j (q b))) →
      room (R.family.side j p) q I →
      Heard R l d h m N j p X e q I ((S.buy (zz L m))^I.card*rate L j p):=by
  intro L F
  obtain ⟨C,W,hist⟩:=filed
  obtain ⟨S,toll⟩:=prices (G:=G) d l e C W T
  obtain ⟨_,_,rows⟩:=WilsonMarkedIndependentNormalizedSingleton.original R simple v funded l d h e
  refine ⟨S,?_⟩
  filter_upwards [hist,rows,exempt L simple S hd] with m teacher issued close
  obtain ⟨Q,level,scheme,clock,anchor,_,school⟩:=issued
  have warm:1≤zz L m:=by rw [←clock];exact Q.depth m anchor.le
  intro X tollX N p j low high q I wake separated fits
  let z:=zz L m+∑i,C.buy (zz L m)*fee (F i) (X i) e
  let B:=W.buy z
  let ρ:=galeGate G d l l e W Credit.leanC Credit.leanC z
  have fees:=toll (zz L m) (fun i=>fee (F i) (X i) e) warm
    (fun i=>(WilsonConditionalTaylorSeparatedPurchase.fee_pos _ _ _).le) tollX
  have enough:cleared L.S m j ρ q I:=fun i hi b hb ne=>fees.2.trans (close.trans (separated i hi b hb ne))
  have income:Wellness l (planted R l d h X m N):=by
    have r:=(school X N (low.trans high)).head
    rw [level,scheme] at r
    exact r
  have t:=teacher X
  have hooked:=WilsonMarkedIndependentMixedLimit.sampled R l d h m N j p simple v funded X e ρ B _
    high income (t.2 ρ le_rfl N p j low high) q I wake enough fits
  intro u tags loc A cap i r upper order x
  exact (hooked u tags loc A cap i r upper order x).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans t.1) fees.1 _)
      (Real.exp_pos _).le) (ContinuousLinearMap.opNorm_nonneg _))

end YM.Integration.WilsonMarkedIndependentMixedOpening
end
