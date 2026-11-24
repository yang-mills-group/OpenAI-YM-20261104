import YM.Integration.WilsonMarkedIndependentNormalizedSingleton
import YM.Integration.WilsonMarkedIndependentFoldedBirth

/-! Each normalized singleton born at the true ultraviolet top has a paid original
folded update at every age. The original attached root can be any cover site. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedSeam
open Function Filter Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{D k K:ι→ℕ}{e m j N:ℕ}

omit [Fintype ι] [DecidableEq ι] in
private theorem crest (x:ι → Cover)(s:ι):crestCard x {s}=0:=by
  apply Nat.eq_zero_of_le_zero
  apply league_le
  intro a b
  have ha:a.val=s:=Finset.mem_singleton.mp a.property
  have hb:b.val=s:=Finset.mem_singleton.mp b.property
  change terrain.gap (x a.val) (x b.val) ≤ 0
  rw [ha,hb,terrain.self]

omit [Fintype ι] in
/-- The estimate concerns the full uncut singleton on its own before-test rooted
width, including all changes in its normalization above the receiving date. -/
theorem paid (Q:Realm G (e+1) Credit.leanC)(w:Credit)(z:ℝ)(P:Outerm G D)
    (income:Borealis Q D k K P m N w z)(s:ι)(mj:m ≤ j)(live:j<N)
    (x:ι → Cover):
    let u:=Gears Q.draws Q.paid K k N N (j+1) P x
    let A:=w.buy (z+snowP Q.draws.S m (j+1))
    1≤A ∧ Eu k u ∧ u ∅=0 ∧ safeB x u {s} e (Q.mint j (income.main.trans mj)).gear.past A:=by
  intro u A
  have upper:=Cog Q.draws Q.paid (K':=K) le_rfl P income.head Q.hG Q.green (show j+1≤N from live)
  have born:m≤j+1:=by omega
  have available:1≤A:=w.purchase (((Q.depth _ income.main).trans income.yell).trans
    (le_add_of_nonneg_right (sub_nonneg.mpr (scales Q.draws.S born))))
  refine ⟨available,upper.level' x,upper.quiet' x,?_⟩
  intro S sub i hi r
  rcases Finset.subset_singleton_iff.mp sub with empty|same
  · subst S
    rw [show u ∅=0 from upper.quiet' x]
    exact Wig.zero.more (by simp)
  · subst S
    exact (income.sing (j+1) x born live s i hi r).shave (Q.crossing j (income.main.trans mj))

def Billed (Q:Realm G (e+1) Credit.leanC)(m N j:ℕ)(P:Outerm G D)(K k:ι→ℕ)(s:ι)
    (i r d:ℕ)(W:Credit)(z:ℝ)(n:Side)(y:ι → Cover)(b:ι→Site (loose Q.draws j).L)(σ:ℝ):Prop:=
  let E:=Gears Q.draws Q.paid K k N N (j+1) P (chartIn (loose Q.draws j) y b)
  let A:=W.buy (z+snowP Q.draws.S m (j+1))
  let out:=(logO Q.draws Q.paid j N E k {s}).2 i r
  let inlineFine:=coilH Q.draws Q.paid j N n E k (ratioHigh Q.draws Q.paid N j) {s} i r
  Wig (tor n) (wrap n ∘ y) (σ/32/2)
    ((Q.y j)^d*A*Real.exp (-(n.val:ℝ)/(512*Q.y j))) {s} (Carp.plume out n-inlineFine)

/-- One stage forecast and one covering exponent work for every true growing
history, every fine placement and every physical or auxiliary period. -/
theorem stage (s:ι)(D k:ι→ℕ)(e i r:ℕ)(hi:i≤e):
    ∃v σ:Gear G→ℝ,∃d:ℕ,(∀I,0<σ I ∧ (σ I)⁻¹≤v I) ∧
    ∀(Q:Realm G (e+1) Credit.leanC) m N j (a:Q.anchor≤j),
      v (Q.mint j a).gear≤Q.cash Credit.leanC j → m≤j → j<N → ∀K:ι→ℕ,∀P:Outerm G D,∀W z,
      Borealis Q D k K P m N W z→∀n y b,Billed Q m N j P K k s i r d W z n y b (σ (Q.mint j a).gear):=by
  obtain ⟨σ,c,U,strip,step⟩:=pledges G e i r hi Credit.leanC Credit.leanC (fun I=>I.past)
    (fun I=>I.depth) (J:={s}) (Z:={s}) le_rfl D k
  let cost(I:Gear G):=priceM (Hooks G) r (σ I)+tiePay (Hooks G) r (σ I/4)+2
  let v(I:Gear G):=max (c I) (max (cost I) U.x)
  refine ⟨v,σ,U.d+2,fun I=>⟨(strip I).1,(strip I).2.trans (le_max_left ..)⟩,?_⟩
  intro Q m N j a wallet mj live K P W z win n y b
  let I:=(Q.mint j a).gear
  let y₀:=Q.y j
  have fee:v I≤y₀:=by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using wallet
  let A:=W.buy (z+snowP Q.draws.S m (j+1))
  let p:=chartIn (loose Q.draws j) y b
  let E:=Gears Q.draws Q.paid K k N N (j+1) P p
  have entry:=paid Q W z P win s mj live p
  have Epos:0≤A:=zero_le_one.trans entry.1
  have approve:c I≤Q.cash Credit.leanC j:=(le_max_left ..).trans wallet
  have store:=step Q j N n a live approve E entry.2.1 entry.2.2.1 y b A Epos entry.2.2.2
  have he:(4*crestCard y {s})<n.val:=by rw [crest];simp
  have price:=markOrbit store (Finset.singleton_nonempty s) he (strip I).1
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


/-- The actual normalized field section and the complete folded Wick integral
on every date of its UV history, with one original preselection. -/
theorem original {a:ℕ}(s:Fin (a+1))(l d:Fin (a+1)→ℕ)(h:∀v,l v<d v)(e i r:ℕ)(hi:i≤e):
    ∃(v:ℕ→Gear G→ℝ)(σ:Gear G→ℝ)(b:ℕ),
    WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v) ∧
    ∀(R:Run G),G.Simple→FundedMarkedCoverRows.prices v R.kit→
      let L:=R.family.path.levels
      let F:=deck (G:=G) l d h
      ∃C W:Credit,∀ᶠ m:ℕ in atTop,∃(Q:Realm G (e+1) Credit.leanC)(a₀:Q.anchor=m),
        Q.draws=L ∧ Q.paid=R.metals.O ∧ Q.y=zz L ∧
        ∀N j:ℕ,∀(mj:m≤j),j<N→∀X:Herit F,
          let U:=normalized Q.draws Q.paid F X m N
          let P:=coatA Q.draws Q.paid N m F U
          let z:=zz L m+∑ a,C.buy (zz L m)*fee (F a) (X a) e
          let I:=(Q.mint j (a₀.le.trans mj)).gear
          0<σ I ∧ (σ I)⁻¹≤Q.y j ∧
          ∀n y rem,Billed Q m N j P l l s i r b W z n y rem (σ I):=by
  obtain ⟨v,σ,b,pos,step⟩:=stage (G:=G) s d l e i r hi
  let u:ℕ→Gear G→ℝ:=fun _=>v
  refine ⟨u,σ,b,FundedMarkedCoverRows.purchase u,?_⟩
  intro R simple funded L F
  obtain ⟨C,W,source⟩:=WilsonMarkedIndependentNormalizedSingleton.original R simple u funded l d h e
  refine ⟨C,W,?_⟩
  filter_upwards [source] with m stock
  obtain ⟨Q,level,ratio,clock,anchor,stamps,hist⟩:=stock
  refine ⟨Q,anchor,level,ratio,clock,?_⟩
  intro N j mj live X U P z I
  have wallet: v I≤Q.cash Credit.leanC j:=(stamps j mj (anchor.le.trans mj)).choose_spec.2
  have width:(σ I)⁻¹≤Q.y j:=by
    simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using (pos I).2.trans wallet
  refine ⟨(pos I).1,width,?_⟩
  exact step Q m N j (anchor.le.trans mj) wallet mj live l P W z (hist X N (mj.trans live.le))

end YM.Integration.WilsonMarkedIndependentNormalizedSeam
end
