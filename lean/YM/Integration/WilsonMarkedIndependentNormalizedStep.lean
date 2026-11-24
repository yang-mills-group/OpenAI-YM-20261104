import YM.Integration.WilsonMarkedIndependentNormalizedWallet
import YM.Integration.WilsonMarkedIndependentNormalizedScale

/-! The original engineering return and its normalized old cofactor use a
single finite power of the physical fine side at every intermediate age. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedStep
open Function Filter Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]

theorem original (s:ι)(D k K:ι→ℕ)(e:ℕ):∃v:Gear G→ℝ,
    ∀(R:Run G),G.Simple→∀W:Credit,∀ᶠj:ℕ in atTop,
    ∀(Q:Realm G (e+1) Credit.leanC)(a:Q.anchor≤j),
      Q.draws=R.family.path.levels→Q.paid=R.metals.O→Q.y=zz R.family.path.levels →
      v (Q.mint j a).gear≤Q.cash Credit.leanC j → ∀m N p:ℕ,m≤j → j<N →
      ∀(P:Outerm G D)(z:ℝ),Borealis Q D k K P m N W z →
      let A:=R.family.path.levels
      let B:=W.buy z
      let f:=R.family.side (j+1) p
      let n:=R.family.side j p
      let X(i:ℕ):=Gears Q.draws Q.paid K k N N i P
      table A R.metals.O e N (j+1) f (WilsonVacuumPreResetFiniteHeatScale.rate A (j+1) p) →
      gap e (X (j+1)) s f (B*rate A (j+1) p) → gap e (X j) s n (B*rate A j p):=by
  let l:=mass k {s}
  let T:=Fin (e+1)×Fin (l+e+1)
  choose u d child using fun t:T=>WilsonMarkedIndependentNormalizedWallet.stage (G:=G) s D k e t.1.val t.2.val (by omega)
  let v(I:Gear G):=∑t:T,|u t I|
  let M:=∑t:T,d t
  let key:=mass K {s}
  refine ⟨v,?_⟩
  intro R simple W
  let A:=R.family.path.levels
  filter_upwards [WilsonMarkedIndependentNormalizedScale.original A simple (M+key+W.d+1),
    WilsonVacuumPreResetFiniteHeatScale.clock A simple] with j scale clock
  intro Q a level scheme stated wallet m N p mj live P z win _ M₀ f n X quiet source
  let Z:=Q.y j
  let H:=gross Z f
  let τ:=rate A (j+1) p
  let fresh:=Real.exp (-(n.val:ℝ)/(512*Z))
  let L:=loose Q.draws j
  have step:f=n*L.L:=by
    dsimp [L];rw [level]
    exact Subtype.ext (A.clock.op j p).sizes
  have hz:1≤z:=(Q.depth _ win.main).trans win.yell
  have real0:0<M₀:=zero_lt_one.trans_le (W.purchase hz)
  have yf:1≤Z:=Q.depth j a
  have fn:(1:ℝ)≤f.val:=by exact_mod_cast f.pos
  have grow:1+(f.val:ℝ)≤(1+(f.val:ℝ))^4:=by
    calc _=(1+(f.val:ℝ))^1:=(pow_one _).symm
         _≤_:=pow_le_pow_right₀ (by linarith) (by decide)
  have fee:1+(f.val:ℝ)≤H:=grow.trans (le_mul_of_one_le_left (by positivity) yf)
  have h2:2≤H:=by linarith
  have h1:1≤H:=by linarith
  have w0:0<zz A (j+1):=clock.2.1
  have tp:0<τ:=Real.exp_pos _
  have ts:τ≤1:=by apply Real.exp_le_one_iff.mpr;exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
  have tq:WilsonVacuumPreResetFiniteHeatScale.rate A (j+1) p≤τ:=by
    apply Real.exp_le_exp.mpr
    change -(f.val:ℝ)/(16*zz A (j+1))≤ -(f.val:ℝ)/(4096*zz A (j+1))
    apply (le_div_iff₀ (by positivity:0<4096*zz A (j+1))).2
    field_simp [w0.ne'];linarith
  have paid:table Q.draws Q.paid e N (j+1) (n*L.L) τ:=by
    rw [←step,level,scheme];exact fun a ha r x=>(quiet a ha r x).trans tq
  have enrolled:gap e (X (j+1)) s (n*L.L) (M₀*τ):=by rw [←step];exact source
  have oldA:W.buy (z+snowP Q.draws.S m (j+1))≤M₀*H^W.d:=by
    rw [level]
    exact (WilsonMarkedIndependentNormalizedScale.age W A.S m (j+1) p (by omega) hz).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) fee _) real0.le)
  let price:=W.buy (z+snowP Q.draws.S m (j+1))
  have a0:0≤price:=zero_le_one.trans (W.purchase (hz.trans (le_add_of_nonneg_right
    (sub_nonneg.mpr (scales Q.draws.S (show m≤j+1 by omega))))))
  have f0:0≤fresh:=(Real.exp_pos _).le
  have envelope:M₀*τ+price*τ+price*fresh≤M₀*H^(W.d+1)*(τ+fresh):=by
    have tr:M₀*τ ≤ (M₀*H^W.d)*τ:=mul_le_mul_of_nonneg_right (le_mul_of_one_le_right real0.le (one_le_pow₀ h1)) tp.le
    have fold:2*(M₀*H^W.d)≤M₀*H^(W.d+1):=by
      calc 2*(M₀*H^W.d) = (M₀*H^W.d)*2:=mul_comm _ _
           _ ≤ (M₀*H^W.d)*H:=mul_le_mul_of_nonneg_left h2 (mul_nonneg real0.le (pow_nonneg (zero_le_one.trans h1) _))
           _ = M₀*H^(W.d+1):=by rw [pow_succ,mul_assoc]
    have up:M₀*H^W.d≤M₀*H^(W.d+1):=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) real0.le
    calc _≤2*(M₀*H^W.d)*τ+(M₀*H^W.d)*fresh:=by
           nlinarith only [tr,mul_le_mul_of_nonneg_right oldA tp.le,mul_le_mul_of_nonneg_right oldA f0]
         _≤_:=by rw [mul_add];exact add_le_add (mul_le_mul_of_nonneg_right fold tp.le) (mul_le_mul_of_nonneg_right up f0)
  have cap:=Cog Q.draws Q.paid (K':=K) le_rfl P win.head Q.hG Q.green (show j≤N from live.le)
  intro y i hi r x
  by_cases kept:r≤l+i
  · let t:T:=(⟨i,by omega⟩,⟨r,by omega⟩)
    have use:u t (Q.mint j a).gear≤v (Q.mint j a).gear:=(le_abs_self _).trans
      (Finset.single_le_sum (fun t _=>abs_nonneg (u t (Q.mint j a).gear)) (mem_univ t))
    have deg:d t≤M:=Finset.single_le_sum (fun t _=>Nat.zero_le (d t)) (mem_univ t)
    let O:=fun y:ι → Cover=>logO Q.draws Q.paid j N (X (j+1) y) k
    have ok:Solo k O:=fun y'=>step_L _ _ _ _ _ _ live Q.hG Q.green
      ((Cog Q.draws Q.paid (K':=K) le_rfl P win.head Q.hG Q.green live).level' y')
    have piece (b:backRow L.L {s}) (x':Fin r → Woods G n):
      let Y:=O (splitQ L y {s} b) {s}
      ‖Y.1 n i r x'-plume (Y.2 i r) n x'‖≤H^M*(M₀*H^(W.d+1)*(τ+fresh)):=by
      intro Y
      have priced:=child t Q m N j a (use.trans wallet) mj live K P W z win n τ (M₀*τ) tp ts (mul_pos real0 tp)
        paid enrolled y (inflate L {s} b) x'
      change ‖Y.1 n i r x'-plume (Y.2 i r) n x'‖≤(gross Z (n*L.L))^(d t)*(M₀*τ+price*τ+price*fresh) at priced
      rw [←step] at priced
      exact priced.trans (mul_le_mul (pow_le_pow_right₀ h1 deg) envelope (by positivity) (by positivity))
    have all:=WilsonMarkedIndependentNormalizedRecursion.reindex L K k O ok y {s} n i r _ piece x
    have priceL:(L.L.val:ℝ)≤H:=by
      have sz:(L.L.val:ℕ)≤f.val:=by rw [step];exact Nat.le_mul_of_pos_left _ n.pos
      have d':(L.L.val:ℝ)≤f.val:=by exact_mod_cast sz
      linarith
    have numerical:=scale p
    change (zz A j*(1+(f.val:ℝ))^4)^(M+key+W.d+1)*(τ+Real.exp (-(n.val:ℝ)/(512*zz A j)))≤rate A j p at numerical
    have eqz:Z=zz A j:=congrFun stated j
    rw [←eqz] at numerical
    change H^(M+key+W.d+1)*(τ+fresh)≤rate A j p at numerical
    change ‖(Gears Q.draws Q.paid K k N N j P y {s}).1 n i r x-
      plume ((Gears Q.draws Q.paid K k N N j P y {s}).2 i r) n x‖≤_
    rw [gearUp Q.draws Q.paid P live]
    apply all.trans
    calc
      _≤H^key*(H^M*(M₀*H^(W.d+1)*(τ+fresh))):=mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) priceL _) (by positivity)
      _ = M₀*(H^(M+key+W.d+1)*(τ+fresh)):=by simp only [pow_add,pow_one];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left numerical real0.le
  · have hz':r>mass k {s}+i:=by dsimp [l] at kept;omega
    rw [(cap.level' y {s}).span n i r hz',(cap.level' y {s}).coverN i r hz',plume_zero]
    simp only [Pi.zero_apply,sub_self,norm_zero];exact mul_nonneg real0.le (Real.exp_pos _).le

end YM.Integration.WilsonMarkedIndependentNormalizedStep
end
