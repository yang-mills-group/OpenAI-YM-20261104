import YM.Integration.WilsonMarkedIndependentMixedWallet
import YM.Integration.WilsonMarkedIndependentNormalizedScale
import YM.Integration.WilsonMarkedIndependentNormalizedRecursion

/-! Signed transfer of the whole marked census on one unwrapped, genuinely
separated receiving date. All subsets share one cutoff-independent reserve. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedStep
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentMixedGeometry (room)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{D:ι→ℕ}

def Entries (X:Outerm G D)(S:Schedule)(m j p e:ℕ)(ρ B η:ℝ):Prop:=
  let n:=S.side j p
  ∀(I:Finset ι)(y:ι → Cover),I.Nonempty → cleared S m j ρ y I → room n y I → ∀i≤e,∀r x,
    ‖(X y I).1 n i r x-plume ((X y I).2 i r) n x‖≤B^I.card*η

theorem original (D k K:ι→ℕ)(e:ℕ):∃v:Gear G→ℝ,
    ∀(R:Run G),G.Simple → ∀W:Credit,∀ᶠj:ℕ in atTop,
    ∀(Q:Realm G (e+1) Credit.leanC)(a:Q.anchor≤j),
      Q.draws=R.family.path.levels → Q.paid=R.metals.O → Q.y=zz R.family.path.levels →
      v (Q.mint j a).gear≤Q.cash Credit.leanC j → ∀m N p:ℕ,m≤j → j<N →
      ∀(P:Outerm G D)(z ρ:ℝ),Borealis Q D k K P m N W z → Cloze D k Q Credit.leanC →
      galeGate G D k K e W Credit.leanC Credit.leanC z≤ρ →
      let A:=R.family.path.levels
      let B:=W.buy z
      let f:=R.family.side (j+1) p
      let X(i:ℕ):=Gears Q.draws Q.paid K k N N i P
      table A R.metals.O e N (j+1) f (WilsonVacuumPreResetFiniteHeatScale.rate A (j+1) p) →
      Entries (X (j+1)) A.S m (j+1) p e ρ B (rate A (j+1) p) →
      Entries (X j) A.S m j p e ρ B (rate A j p):=by
  let l:=mass k univ
  let T:={I:Finset ι // I.Nonempty} × Fin (e+1) × Fin (l+e+1)
  choose u d child using fun t:T=>WilsonMarkedIndependentMixedWallet.original (G:=G) D k t.1.val t.1.property
    e t.2.1.val t.2.2.val (by omega)
  let v(Z:Gear G):=∑t:T,|u t Z|
  let M:=∑t:T,d t
  let eng:=mass K univ
  let load:=Fintype.card ι
  refine ⟨v,?_⟩
  intro R simple W
  let A:=R.family.path.levels
  let power:=M+eng+(W.d+1)*load
  filter_upwards [WilsonMarkedIndependentNormalizedScale.original A simple power,
    WilsonVacuumPreResetFiniteHeatScale.clock A simple] with j scale clock
  intro Q a level scheme dated wallet m N p mj live P z ρ win cloze gate _ B f X quiet previous
  let n:=R.family.side j p
  let Z:=Q.y j
  let H:=gross Z f
  let τ:=rate A (j+1) p
  let fresh:=Real.exp (-(n.val:ℝ)/(512*Z))
  let L:=loose Q.draws j
  have step:f=n*L.L:=by dsimp [L];rw [level];exact Subtype.ext (A.clock.op j p).sizes
  have hz:1≤z:=(Q.depth _ win.main).trans win.yell
  have B0:0<B:=zero_lt_one.trans_le (W.purchase hz)
  have yf:1≤Z:=Q.depth j a
  have fn:(1:ℝ)≤f.val:=by exact_mod_cast f.pos
  have pow4:1+(f.val:ℝ)≤(1+(f.val:ℝ))^4:=(pow_one _).symm.le.trans (pow_le_pow_right₀ (by linarith) (by decide:1≤4))
  have fee:1+(f.val:ℝ)≤H:=pow4.trans (le_mul_of_one_le_left (by positivity) yf)
  have h2:2≤H:=by linarith
  have h1:1≤H:=by linarith
  have h0:0≤H:=zero_le_one.trans h1
  have tp:0<τ:=Real.exp_pos _
  have w0:0<zz A (j+1):=clock.2.1
  have ts:τ≤1:=by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
  have tq:WilsonVacuumPreResetFiniteHeatScale.rate A (j+1) p≤τ:=by
    apply Real.exp_le_exp.mpr
    change -(f.val:ℝ)/(16*zz A (j+1))≤ -(f.val:ℝ)/(4096*zz A (j+1))
    apply (le_div_iff₀ (by positivity:0<4096*zz A (j+1))).2
    field_simp [w0.ne'];linarith
  have paid:table Q.draws Q.paid e N (j+1) (n*L.L) τ:=by
    rw [←step,level,scheme];exact fun a ha r x=>(quiet a ha r x).trans tq
  let oldA:=W.buy (z+snowP Q.draws.S m (j+1))
  have paidA:oldA≤B*H^W.d:=by
    dsimp only [oldA];rw [level]
    exact (WilsonMarkedIndependentNormalizedScale.age W A.S m (j+1) p (by omega) hz).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) fee _) B0.le)
  have fold:oldA+B≤B*H^(W.d+1):=by
    have Bpaid:B≤B*H^W.d:=le_mul_of_one_le_right B0.le (one_le_pow₀ h1)
    calc oldA+B≤2*(B*H^W.d):=by linarith
         _=(B*H^W.d)*2:=mul_comm _ _
         _≤(B*H^W.d)*H:=mul_le_mul_of_nonneg_left h2 (mul_nonneg B0.le (pow_nonneg h0 _))
         _=B*H^(W.d+1):=by rw [pow_succ,mul_assoc]
  have old0:0≤oldA:=zero_le_one.trans (W.purchase (hz.trans (le_add_of_nonneg_right
    (sub_nonneg.mpr (scales Q.draws.S (show m≤j+1 by omega))))))
  have cap:=Cog Q.draws Q.paid (K':=K) le_rfl P win.head Q.hG Q.green (show j≤N from live.le)
  intro I y awake clear localRoom i hi r x
  have KI:mass k I≤l:=Finset.sum_le_sum_of_subset (Finset.subset_univ I)
  have ei:mass K I≤eng:=Finset.sum_le_sum_of_subset (Finset.subset_univ I)
  have card:I.card≤load:=Finset.card_le_univ I
  have cq:cleared Q.draws.S m j ρ y I:=by rw [level];exact clear
  by_cases kept:r ≤ mass k I+i
  · let t:T:=(⟨I,awake⟩,⟨i,by omega⟩,⟨r,by omega⟩)
    have use:u t (Q.mint j a).gear≤v (Q.mint j a).gear:=(le_abs_self _).trans
      (Finset.single_le_sum (fun t _=>abs_nonneg (u t (Q.mint j a).gear)) (mem_univ t))
    have deg:d t≤M:=Finset.single_le_sum (fun t _=>Nat.zero_le (d t)) (mem_univ t)
    let O:=fun y:ι → Cover=>logO Q.draws Q.paid j N (X (j+1) y) k
    have ok:Solo k O:=fun y'=>step_L _ _ _ _ _ _ live Q.hG Q.green
      ((Cog Q.draws Q.paid (K':=K) le_rfl P win.head Q.hG Q.green live).level' y')
    have piece (b:backRow L.L I)(x':Fin r → Woods G n):
      let Y:=O (splitQ L y I b) I
      ‖Y.1 n i r x'-plume (Y.2 i r) n x'‖≤H^M*(B*H^(W.d+1))^I.card*(τ+fresh):=by
      intro Y
      let b':=inflate L I b
      let y':=chartIn L y b'
      let E:=X (j+1) y'
      have funds:=WilsonMarkedIndependentMixedGeometry.paid Q P W z ρ win cloze gate mj live y b' I cq
      have price:=child t Q j N a (use.trans wallet) live y b' E oldA B old0 B0 funds.2.1 funds.2.2.1
        funds.2.2.2 n τ tp ts localRoom paid (by
          intro J sub present w hw s g
          have sep:=WilsonMarkedIndependentMixedGeometry.held Q.draws y b' mj sub cq
          have space:=WilsonMarkedIndependentMixedGeometry.chart L n y b' (Q.draws.S.block_large j) sub localRoom
          revert g
          rw [←step] at space ⊢
          have sep':cleared A.S m (j+1) ρ y' J:=
            Eq.mp (congrArg (fun Q':Levels G=>cleared Q'.S m (j+1) ρ y' J) level) sep
          exact previous J y' present sep' space w hw s) x'
      change ‖Y.1 n i r x'-plume (Y.2 i r) n x'‖≤(gross Z (n*L.L))^(d t)*(oldA+B)^I.card*(τ+fresh) at price
      rw [←step] at price
      apply price.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ h1 deg)
        (pow_le_pow_left₀ (add_nonneg old0 B0.le) fold _) (pow_nonneg (add_nonneg old0 B0.le) _) (pow_nonneg h0 _))
        (add_nonneg tp.le (Real.exp_pos _).le)
    have all:=WilsonMarkedIndependentNormalizedRecursion.reindex L K k O ok y I n i r _ piece x
    have priceL:(L.L.val:ℝ)≤H:=by
      have sz:(L.L.val:ℕ)≤f.val:=by rw [step];exact Nat.le_mul_of_pos_left _ n.pos
      have d':(L.L.val:ℝ)≤f.val:=by exact_mod_cast sz
      linarith
    have budget:M+mass K I+(W.d+1)*I.card≤power:=Nat.add_le_add (Nat.add_le_add_left ei M) (Nat.mul_le_mul_left _ card)
    have numerical:=scale p
    change (zz A j*(1+(f.val:ℝ))^4)^power*(τ+Real.exp (-(n.val:ℝ)/(512*zz A j)))≤rate A j p at numerical
    have eqz:Z=zz A j:=congrFun dated j
    rw [←eqz] at numerical
    change H^power*(τ+fresh)≤rate A j p at numerical
    change ‖(Gears Q.draws Q.paid K k N N j P y I).1 n i r x-
      plume ((Gears Q.draws Q.paid K k N N j P y I).2 i r) n x‖≤_
    rw [gearUp Q.draws Q.paid P live]
    apply all.trans
    calc
      _≤H^(mass K I)*(H^M*(B*H^(W.d+1))^I.card*(τ+fresh)):=mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) priceL _) (mul_nonneg
          (mul_nonneg (pow_nonneg h0 _) (pow_nonneg (mul_nonneg B0.le (pow_nonneg h0 _)) _))
          (add_nonneg tp.le (Real.exp_pos _).le))
      _=B^I.card*(H^(M+mass K I+(W.d+1)*I.card)*(τ+fresh)):=by rw [mul_pow,←pow_mul];simp only [pow_add];ring
      _≤B^I.card*(H^power*(τ+fresh)):=mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 budget) (add_nonneg tp.le (Real.exp_pos _).le)) (pow_nonneg B0.le _)
      _≤_:=mul_le_mul_of_nonneg_left numerical (pow_nonneg B0.le _)
  · have hz':mass k I+i<r:=lt_of_not_ge kept
    rw [(cap.level' y I).span n i r hz',(cap.level' y I).coverN i r hz',plume_zero]
    simp only [Pi.zero_apply,sub_self,norm_zero];exact mul_nonneg (pow_nonneg B0.le _) (Real.exp_pos _).le

end YM.Integration.WilsonMarkedIndependentMixedStep
end
