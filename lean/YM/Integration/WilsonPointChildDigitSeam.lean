import YM.Integration.WilsonPointChildDigitGazette
import YM.Integration.WilsonPointChildFiledSeam
import YM.Integration.WilsonMarkedIndependentNormalizedWallet
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDigitSeam
open Function Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic.Near AnalyticNext.QuarticMatch.Sheets
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open scoped Classical BigOperators
open WilsonPointChildScalarSlot
variable {G:Gauge}

theorem original (G:Gauge)(e i l r:ℕ)(hi:i ≤ e):
    ∃v:Gear G → ℝ,∃k:ℕ,∀(Q:Realm G (e+1) Credit.leanC) j N (a:Q.anchor ≤ j),
    v (Q.mint j a).gear ≤ Q.cash Credit.leanC j → j<N → ∀(z:Site (loose Q.draws j).L)(n:Side)(X:Era G ℝ),Auth l X → 
    let f:=n*(loose Q.draws j).L
    let B:=gross (Q.y j) f
    ∀η δ A:ℝ,0<η → η ≤ 1 → 0<δ → 0<A → 
    table Q.draws Q.paid e N (j+1) f η → 
    (∀b ≤ e,∀t x,|X.1 f b t x-plume (X.2 b t) f x| ≤ δ) → 
    (∀b ≤ e,∀t x,|plume (X.2 b t) f x| ≤ A) → 
    (∀b ≤ e,∀t,Wig terrain (fun _:Unit=>lift z) (WilsonPointChildQuoteWidth.quote (Q.mint j a).gear) A {()} (X.2 b t)) → 
    ∀x,let Y:=verseI Q.draws Q.paid j N l X
       ‖Y.1 n i r x-plume (Y.2 i r) n x‖ ≤ 
         B^k*(δ+A*η+A*Real.exp (-(n.val:ℝ)/(512*Q.y j))):=by
  let T:=Fin (i+1)
  choose u d C rich buy using fun b:T=>WilsonMarkedIndependentFiniteVectorSlope.original G e b.val l r (by omega)
  obtain ⟨w,k₀,reset⟩:=WilsonVacuumPreResetFiniteHeatCourse.reversion G e i r hi
  obtain ⟨t,σ,sh,valid,seam⟩:=WilsonPointChildDigitGazette.submitted G l e i r hi
  let cs:=‖outlet‖*‖inlet‖
  let v(I:Gear G):= |t I|+|w I|+cs+∑b:T,(|u b I|+C b)
  let d₀:=∑b:T,d b
  let D:=max (k₀+d₀+1) (sh+1)
  refine ⟨v,D,?_⟩
  intro Q j N a ticket live z n X auth f B η δ A epos esmall dpos Apos prior previous high support x Y
  let I:=(Q.mint j a).gear
  let y:=Q.y j
  have cs0:0 ≤ cs:=mul_nonneg (norm_nonneg outlet) (norm_nonneg inlet)
  have y1:1 ≤ y:=Q.depth j a
  have byy : y ≤ B := by
    change y ≤ y*(1+(f.val:ℝ))^4
    exact le_mul_of_one_le_right (zero_le_one.trans y1)
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) f.val]))
  have b1:=y1.trans byy
  have vn:v I ≤ B:=(show v I ≤ y from by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using ticket).trans byy
  have nonneg(z:T):0 ≤ |u z I|+C z:=add_nonneg (abs_nonneg _) (zero_le_one.trans (rich z))
  have sum0:0 ≤ ∑z:T,(|u z I|+C z):=Finset.sum_nonneg (fun z _=>nonneg z)
  have uw(z:T):u z I ≤ v I ∧ C z ≤ B:=by
    have part:=Finset.single_le_sum (f:=fun z:T=>|u z I|+C z) (fun z _=>nonneg z) (mem_univ z)
    dsimp [v] at vn ⊢
    constructor <;> linarith [abs_nonneg (t I),abs_nonneg (w I),le_abs_self (u z I),abs_nonneg (u z I),rich z]
  have small:cs ≤ B:=by dsimp [v] at vn;linarith [abs_nonneg (t I),abs_nonneg (w I)]
  have stage:t I ≤ v I:=by dsimp [v];linarith [le_abs_self (t I),abs_nonneg (w I)]
  have rest:w I ≤ v I:=by dsimp [v];linarith [le_abs_self (w I),abs_nonneg (t I)]
  let L:=loose Q.draws j
  let T₀:=X.1 f
  let U:Pal ℝ (Woods G f):=fun b h=>plume (X.2 b h) f
  let H:=stepAt L Q.draws.clock.kernel n
  let forest:=xree L Q.draws.clock.kernel n
  let marks:=reed H forest (freeForms Q.draws N (j+1)) (roam Q.draws N j n) Q.paid
    ((story Q.draws Q.paid N (j+1)).1 f) l T₀
  let model:=reed H forest (freeForms Q.draws N (j+1)) (roam Q.draws N j n) Q.paid
    (emera (actionW Q.draws Q.paid N (j+1)) f) l U
  have readings (g:ℕ)(hg:g ≤ i)(x':Fin r → Woods G n):
      ‖marks g r x'-model g r x'‖ ≤ B^(d₀+1)*(δ+A*η):=by
    let h:T:=⟨g,by omega⟩
    have hr:d h ≤ d₀:=Finset.single_le_sum (fun b _=>Nat.zero_le (d b)) (mem_univ h)
    have price:=buy h Q j a ((uw h).1.trans ticket) N live n ℝ T₀ U η δ A epos esmall dpos Apos
      (fun b hb t _ v'=>prior b hb t v') (fun b hb t _ v'=>by simpa only [Real.norm_eq_abs] using previous b hb t v')
      (fun b hb t _ v'=>by simpa only [Real.norm_eq_abs] using high b hb t v') x'
    change ‖marks g r x'-model g r x'‖ ≤ C h*B^(d h)*(δ+A*η) at price
    apply price.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc C h*B^(d h) ≤ B*B^d₀:=mul_le_mul (uw h).2 (pow_le_pow_right₀ b1 hr) (by positivity) (by linarith)
         _=B^(d₀+1):=by rw [pow_succ,mul_comm]
  let beta:=ratioHigh Q.draws Q.paid N j
  let F:=WilsonPointChildFiledSeam.folded Q.draws Q.paid j N l X n
  have inner:‖Y.1 n i r x-F i r x‖ ≤ B^D*(δ+A*η):=by
    have coin:=reset Q j a (rest.trans ticket) N live
    have cc:rimJ beta i r ≤ B^k₀:=coin.trans (pow_le_pow_left₀ (zero_le_one.trans y1) byy _)
    apply (WilsonMarkedIndependentNormalizedRecursion.reversion beta marks model i r _ readings x).trans
    calc _ ≤ B^k₀*(B^(d₀+1)*(δ+A*η)):=mul_le_mul_of_nonneg_right cc (by positivity)
         _=B^(k₀+d₀+1)*(δ+A*η):=by rw [show k₀+d₀+1=k₀+(d₀+1) by omega,pow_add];ring
         _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ b1 (le_max_left ..)) (by positivity)
  let tail:=Real.exp (-(n.val:ℝ)/(512*Q.y j))
  have granted:=seam Q j N a (stage.trans ticket) live z n X auth A Apos.le support
  have line:=WilsonMarkedIndependentNormalizedWallet.raw granted (by have h:0<σ I:=(valid I).1;positivity) x
  let E:=roster X
  let P:=(logO Q.draws Q.paid j N E (WilsonPointChildGazette.born l) {()}).2 i r
  let V:=coilH Q.draws Q.paid j N n E (WilsonPointChildGazette.born l) beta {()} i r
  let h:=(plume P n-V) x
  have num:outlet h=plume (Y.2 i r) n x-F i r x:=WilsonPointChildFiledSeam.read _ _ _ _ _ _ live Q.hG Q.green X auth i r x
  have actual:‖F i r x-plume (Y.2 i r) n x‖ ≤ B^D*(A*tail):=by
    rw [norm_sub_rev,←num]
    apply (outlet.le_opNorm h).trans
    calc _  ≤  ‖outlet‖*((Q.y j)^sh*(‖inlet‖*A)*tail):=mul_le_mul_of_nonneg_left line (norm_nonneg outlet)
         _=cs*(Q.y j)^sh*(A*tail):=by unfold cs;ring
         _ ≤ B^(sh+1)*(A*tail):=by
           apply mul_le_mul_of_nonneg_right _ (mul_nonneg Apos.le (Real.exp_pos _).le)
           rw [pow_succ,mul_comm (B^sh)]
           exact mul_le_mul small (pow_le_pow_left₀ (zero_le_one.trans y1) byy _) (by positivity) (by linarith)
         _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ b1 (le_max_right ..)) (mul_nonneg Apos.le (Real.exp_pos _).le)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add inner actual).trans_eq (by ring))

end YM.Integration.WilsonPointChildDigitSeam
