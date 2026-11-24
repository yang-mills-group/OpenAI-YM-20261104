import YM.Integration.WilsonMarkedIndependentNormalizedRecursion
import YM.Integration.WilsonVacuumPreResetFiniteHeatHistory

/-! A single paid stage acts on the whole dated marked singleton, the
genuine previous finite action, and its folded substitute on that torus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedWallet
open Function Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic.Near AnalyticNext.QuarticMatch.Sheets
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι→ℕ}

def gap (e:ℕ)(X:Outerm G D)(s:ι)(n:Side)(δ:ℝ):Prop:=
  ∀y:ι → Cover,∀i≤e,∀r x,‖(X y {s}).1 n i r x-plume ((X y {s}).2 i r) n x‖≤δ

omit [DecidableEq ι] in
theorem raw {U V α:Type}[NormedAddCommGroup V]{loc:Distance U}{y:ι→U}{Z:Finset ι}
    {σ t:ℝ}{r:ℕ}{F:Ten V (U×α) r}(price:Wig loc y σ t Z F)(hs:0≤σ)(x):‖F x‖≤t:=by
  exact (price.2 x).trans (mul_le_of_le_one_right price.1 (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Nat.cast_nonneg _))))

/-- The complete independently filed upper singleton, including its scalar, has
the original before-test invoice also after period folding. -/
theorem folded {e j m N:ℕ}(Q:Realm G (e+1) Credit.leanC)(P:Outerm G D)
    (K:ι→ℕ)(W:Credit)(z:ℝ)(income:Borealis Q D k K P m N W z)(s:ι)(mj:m≤j)(live:j<N)
    (y:ι → Cover)(b:ι→Site (loose Q.draws j).L)(n:Side):
    let h:=income.main.trans mj
    let I:=(Q.mint j h).gear
    let L:=loose Q.draws j
    let f:=n*L.L
    let E:=Gears Q.draws Q.paid K k N N (j+1) P (chartIn L y b)
    let A:=W.buy (z+snowP Q.draws.S m (j+1))
    ∀i≤e,∀r x,‖plume ((E {s}).2 i r) f x‖≤diamond G e (mass k {s}) I.past*A:=by
  intro h I L f E A i hi r x
  have good:=WilsonMarkedIndependentNormalizedSeam.paid Q W z P income s mj live (chartIn L y b)
  let T:=flowOne Q {s} E j N h live I.past I.depth y b good.2.2.1 good.2.1 A
    (zero_le_one.trans good.1) good.2.2.2 n
  have hol:=T.shore {s} le_rfl i hi r
  change MarkU (chartIn L y b) {s} (plume ((E {s}).2 i r) f) ((E {s}).2 i r)
    (holt Q j h I.past I.depth).s ((diamond G e (mass k {s}) I.past*A)^({s}:Finset ι).card) at hol
  simp only [card_singleton,pow_one] at hol
  exact raw hol.bill (holt Q j h I.past I.depth).h.le x

/-- Actual signed inherited change and the genuine registered Gazette seam
in the same stored (pre-position-sum) component. -/
theorem stage [Fintype ι] (s:ι)(D k:ι→ℕ)(e i r:ℕ)(hi:i≤e):
    ∃(v:Gear G→ℝ)(d:ℕ),∀(Q:Realm G (e+1) Credit.leanC) m N j (a:Q.anchor≤j),
      v (Q.mint j a).gear≤Q.cash Credit.leanC j → m≤j → j<N →
      ∀K:ι→ℕ,∀P:Outerm G D,∀W z,Borealis Q D k K P m N W z→∀n:Side,
      let L:=loose Q.draws j
      let f:=n*L.L
      let old:=Gears Q.draws Q.paid K k N N (j+1) P
      let A:=W.buy (z+snowP Q.draws.S m (j+1))
      let B:=gross (Q.y j) f
      ∀η δ:ℝ,0<η → η≤1 → 0<δ → table Q.draws Q.paid e N (j+1) f η → gap e old s f δ →
      ∀(y:ι → Cover)(b:ι→Site L.L)(x),
        let E:=old (chartIn L y b)
        let result:=logO Q.draws Q.paid j N E k {s}
        ‖result.1 n i r x-plume (result.2 i r) n x‖≤
          B^d*(δ+A*η+A*Real.exp (-(n.val:ℝ)/(512*Q.y j))):=by
  let l:=mass k {s}
  let T:=Fin (i+1)
  choose u d C rich buy using fun b:T=>WilsonMarkedIndependentFiniteVectorSlope.original G e b.val l r (by omega)
  obtain ⟨w,k₀,reset⟩:=WilsonVacuumPreResetFiniteHeatCourse.reversion G e i r hi
  obtain ⟨t,σ,sh,valid,seam⟩:=WilsonMarkedIndependentNormalizedSeam.stage (G:=G) s D k e i r hi
  let v(I:Gear G):= |t I|+|w I|+diamond G e l I.past+∑b:T,(|u b I|+C b)
  let d₀:=∑b:T,d b
  let d₁:=max (k₀+d₀+2) sh
  refine ⟨v,d₁,?_⟩
  intro Q m N j a ticket mj live K P W z win n L f old A B η δ epos esmall dpos prior previous y b x E result
  let I:=(Q.mint j a).gear
  let Y:=Q.y j
  have y1:1≤Y:=Q.depth j a
  have bY:Y≤B:=by
    change Y≤Y*(1+(f.val:ℝ))^4
    exact le_mul_of_one_le_right (zero_le_one.trans y1) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) f.val]))
  have b1:=y1.trans bY
  have vn:v I≤Y:=by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using ticket
  have posD:1≤diamond G e l I.past:=diamond_nn G I.depth
  have comp(b:T): |u b I|+C b≤∑b:T,(|u b I|+C b):=Finset.single_le_sum (f:=fun b:T=>|u b I|+C b)
    (fun b _=>add_nonneg (abs_nonneg _) (zero_le_one.trans (rich b))) (mem_univ b)
  have cols:0≤∑b:T,(|u b I|+C b):=Finset.sum_nonneg (fun b _=>add_nonneg (abs_nonneg _) (zero_le_one.trans (rich b)))
  have uw(b:T):u b I≤v I ∧ C b≤B:=by
    dsimp [v] at vn ⊢
    constructor <;> linarith [comp b,rich b,abs_nonneg (u b I),le_abs_self (u b I),
      abs_nonneg (w I),abs_nonneg (t I)]
  have iv:diamond G e l I.past≤B:=by dsimp [v] at vn;linarith [abs_nonneg (t I),abs_nonneg (w I)]
  have stageCash:t I≤v I:=by dsimp [v];linarith [le_abs_self (t I),abs_nonneg (w I)]
  have resetCash:w I≤v I:=by dsimp [v];linarith [le_abs_self (w I),abs_nonneg (t I)]
  have booked:=WilsonMarkedIndependentNormalizedSeam.paid Q W z P win s mj live (chartIn L y b)
  have posA:0<A:=zero_lt_one.trans_le booked.1
  let T₀:=(E {s}).1 f
  let U:=(repaint E {s}).1 f
  let H:=stepAt L Q.draws.clock.kernel n
  let forest:=xree L Q.draws.clock.kernel n
  let marks:=reed H forest (freeForms Q.draws N (j+1)) (roam Q.draws N j n) Q.paid
    ((story Q.draws Q.paid N (j+1)).1 f) l T₀
  let lined:=reed H forest (freeForms Q.draws N (j+1)) (roam Q.draws N j n) Q.paid
    (emera (actionW Q.draws Q.paid N (j+1)) f) l U
  have readings (a':ℕ) (ha:a' ≤ i) (x':Fin r → Woods G n):
      ‖marks a' r x'-lined a' r x'‖≤B^(d₀+2)*(δ+A*η):=by
    let h:T:=⟨a',by omega⟩
    have hD:d h≤d₀:=Finset.single_le_sum (fun b _=>Nat.zero_le (d b)) (mem_univ h)
    have entry:=buy h Q j a ((uw h).1.trans ticket) N live n (Pen D {s}) T₀ U η δ
      (diamond G e l I.past*A) epos esmall dpos (mul_pos (zero_lt_one.trans_le posD) posA)
      (fun b hb t _ v'=>prior b hb t v') (fun b' hb t _ v'=>previous (chartIn L y b) b' hb t v')
      (fun b' hb t _ v'=>folded Q P K W z win s mj live y b n b' hb t v') x'
    change ‖marks a' r x'-lined a' r x'‖≤C h*B^(d h)*(δ+diamond G e l I.past*A*η) at entry
    apply entry.trans
    have fac:δ+diamond G e l I.past*A*η≤B*(δ+A*η):=by
      rw [mul_add]
      exact add_le_add (le_mul_of_one_le_left dpos.le b1)
        (by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right iv posA.le) epos.le)
    have cc:C h*B^(d h)≤B*B^d₀:=mul_le_mul (uw h).2 (pow_le_pow_right₀ b1 hD) (by positivity) (by linarith)
    calc _≤(B*B^d₀)*(B*(δ+A*η)):=mul_le_mul cc fac (by positivity) (by positivity)
         _=_:=by rw [show d₀+2=d₀+1+1 by omega,pow_succ,pow_succ];ring
  have Dcoin:=reset Q j a (resetCash.trans ticket) N live
  let beta:=ratioHigh Q.draws Q.paid N j
  have lesser:‖Blue.mix beta marks i r x-Blue.mix beta lined i r x‖≤B^d₁*(δ+A*η):=by
    apply (WilsonMarkedIndependentNormalizedRecursion.reversion beta marks lined i r _ readings x).trans
    have ypow:rimJ beta i r≤B^k₀:=Dcoin.trans (pow_le_pow_left₀ (zero_le_one.trans y1) bY _)
    calc _≤B^k₀*(B^(d₀+2)*(δ+A*η)):=mul_le_mul_of_nonneg_right ypow (by positivity)
         _ = B^(k₀+d₀+2)*(δ+A*η):=by rw [show k₀+d₀+2=k₀+(d₀+2) by omega,pow_add];ring
         _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ b1 (le_max_left ..)) (by positivity)
  let fold:=coilH Q.draws Q.paid j N n E k beta {s}
  have one:result.1 n=Blue.mix beta marks:=by
    rw [show result=verseI Q.draws Q.paid j N l (E {s}) from
      WilsonMarkedIndependentNormalizedRecursion.singleton _ _ _ _ live Q.hG Q.green E booked.2.1 booked.2.2.1 s]
    rfl
  have two:fold=Blue.mix beta lined:=WilsonMarkedIndependentFoldedBirth.singleton _ _ _ _ _ s E booked.2.1 booked.2.2.1 beta
  have err:=seam Q m N j a (stageCash.trans ticket) mj live K P W z win n y b
  let age:=Real.exp (-(n.val:ℝ)/(512*Y))
  have received:‖(plume (result.2 i r) n x)-fold i r x‖≤Y^sh*A*age:=by
    exact raw err (div_nonneg (div_nonneg (valid I).1.le (by norm_num)) (by norm_num)) x
  have restored:‖fold i r x-plume (result.2 i r) n x‖≤B^d₁*(A*age):=by
    rw [norm_sub_rev]
    apply received.trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (zero_le_one.trans y1) bY _).trans
      (pow_le_pow_right₀ b1 (le_max_right ..))) (mul_nonneg posA.le (Real.exp_pos _).le)
  rw [one]
  have triangle:=dist_triangle (Blue.mix beta marks i r x) (fold i r x) (plume (result.2 i r) n x)
  simp only [dist_eq_norm,two] at triangle
  rw [two] at restored
  apply triangle.trans
  rw [mul_add]
  exact add_le_add lesser restored

end YM.Integration.WilsonMarkedIndependentNormalizedWallet
end
