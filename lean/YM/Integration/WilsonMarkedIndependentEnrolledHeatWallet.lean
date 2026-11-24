import YM.Integration.WilsonVacuumPreResetFiniteHeatFinance
import YM.Integration.WilsonMarkedIndependentSelectedHeat

/-! The genuine folded old-action and finite-geometry bill on the elected
Scroll, used for every marked source and all original tori. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentEnrolledHeatWallet
open Bloch Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatWindow
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{I:Arch G}
open WilsonVacuumPreResetFiniteHeatSlope (gate)
open WilsonVacuumPreResetFiniteHeatFinance (geometry gross)
private theorem sites(n:Side):(Fintype.card (Site n):ℝ)=(n.val:ℝ)^4:=by exact_mod_cast Lattice.site_card n
private theorem woods(G:Gauge)(n:Side):
    (Fintype.card (Woods G n):ℝ)=(n.val:ℝ)^4*Fintype.card (Stationary.Loc G 1):=by
  change (Fintype.card (Site n × Stationary.Loc G 1):ℝ)=_
  simp only [Fintype.card_prod,Nat.cast_mul,sites]


theorem original(G:Gauge)(e r:ℕ):
    ∃v:Gear G→ℝ,∃D:ℕ,∀Q:Realm G (e+1) Credit.leanC,∀m (hm:Q.anchor ≤ m),
      v (Q.mint m hm).gear ≤ Q.cash Credit.leanC m → ∀N (live:m<N) n,
        let p:=cloVent Q m N n hm live 1 zero_lt_one
        ∃A:ℝ,0 ≤ A ∧ (∀i ≤ e,∀l ≤ horizon e r,∀x,|casePW p.wheel Q.paid p.cone p.W' i l x| ≤ A) ∧
          fee p A r ≤ (gross (Q.y m) (n*(loose Q.draws m).L))^D:=by
  classical
  obtain ⟨d,dated⟩:=WilsonVacuumPreResetFiniteHeatBaseline.original G e (horizon e r)
  let arch(I:Gear G)(p:WilsonVacuumPreResetFiniteHeatSlope.gate I):Arch G:=aerie 1 I e zero_lt_one p.1 p.2
  let a(I:Gear G):ℝ:=if p:WilsonVacuumPreResetFiniteHeatSlope.gate I then (dated (arch I p)).choose else 0
  have a_pos(I:Gear G):0 ≤ a I:=by
    dsimp only [a];split
    · next p=>exact (dated (arch I p)).choose_spec.1
    · exact le_rfl
  let T:=costXV G e Credit.leanC
  let c:ℝ:=Fintype.card (Stationary.Loc G 1)
  let H:=2+(T.d+2)*d
  let D:=2+H+3*horizon e r
  let v(I:Gear G):ℝ:=5+((horizon e r+2:ℕ):ℝ)+2*c+|a I|+nimbus I+admissionA I e+T.x
  refine ⟨v,D,?_⟩
  intro Q m hm enrolled N live n
  let I:=(Q.mint m hm).gear
  let f:=n*I.patch.L
  let y:=Q.y m
  let z:=gross y f
  let p:=cloVent Q m N n hm live 1 zero_lt_one
  have te:0 ≤ T.x:=zero_le_one.trans T.good
  have ae:1 ≤ admissionA I e:=admissionSeal _
  have mass:1 ≤ nimbus I:=(holt Q m hm 1 zero_lt_one).book
  have nn:0 ≤ c:=Nat.cast_nonneg _
  have widening:0 ≤ ((horizon e r+2:ℕ):ℝ):=Nat.cast_nonneg _
  have incomes:5+((horizon e r+2:ℕ):ℝ)+2*c+|a I|+nimbus I+admissionA I e+T.x ≤ y:=by
    simpa only [v,Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using enrolled
  have ab:=abs_nonneg (a I)
  have fy:5 ≤ y:=by linarith
  have yp:1 ≤ y:=by linarith
  have avail:y ≤ z:=by
    apply le_mul_of_one_le_right (zero_le_one.trans yp)
    apply one_le_pow₀;linarith [show (0:ℝ) ≤ f.val from Nat.cast_nonneg _]
  have zp:1 ≤ z:=yp.trans avail
  have nf:(n.val:ℝ) ≤ f.val:=by
    change (n.val:ℝ) ≤ (n.val*I.patch.L.val:ℕ)
    exact_mod_cast Nat.le_mul_of_pos_right _ I.patch.L.prop
  have fg:0 ≤ (f.val:ℝ):=Nat.cast_nonneg _
  have fp:(f.val:ℝ)^4 ≤ (1+(f.val:ℝ))^4:=pow_le_pow_left₀ fg (by linarith) _
  have np:(n.val:ℝ)^4 ≤ (f.val:ℝ)^4:=pow_le_pow_left₀ (Nat.cast_nonneg _) nf _
  have cpay:2*c*(f.val:ℝ)^4 ≤ z:=mul_le_mul (by linarith) fp (pow_nonneg fg _) (zero_le_one.trans yp)
  have size:(Fintype.card (Site n):ℝ) ≤ z:=by
    rw [sites]
    apply np.trans (fp.trans _)
    exact le_mul_of_one_le_left (by positivity) yp
  have fine:(Fintype.card (Woods G f):ℝ) ≤ z:=by
    rw [woods];change _*c ≤ _;apply le_trans _ cpay;nlinarith [mul_nonneg nn (pow_nonneg fg 4)]
  have joint:(Fintype.card (Joint G f n):ℝ) ≤ z:=by
    change (Fintype.card (Woods G f ⊕ Woods G n):ℝ) ≤ _
    rw [Fintype.card_sum,Nat.cast_add,woods,woods]
    change _*c+_*c ≤ _;apply le_trans _ cpay
    nlinarith only [mul_le_mul_of_nonneg_right np nn]
  have paid:Q.cash T m ≤ z^(T.d+1):=by
    change T.x*y^T.d ≤ _
    rw [pow_succ']
    exact mul_le_mul (by linarith) (pow_le_pow_left₀ (zero_le_one.trans yp) avail _) (pow_nonneg (zero_le_one.trans yp) _) (zero_le_one.trans zp)
  let coin:ℝ:=admissionA I e*Q.cash T m
  have cp:0 ≤ coin:=zero_le_one.trans p.paid
  have cash:coin ≤ z^(T.d+2):=by
    rw [pow_succ']
    exact mul_le_mul (by linarith) paid (zero_le_one.trans (Credit.purchase _ (Q.depth _ hm))) (zero_le_one.trans zp)
  let A:ℝ:=Fintype.card (Site n)*a I*coin^d
  have head:A ≤ z^H:=by
    have term: (Fintype.card (Site n):ℝ)*a I ≤ z*z:=
      (mul_le_mul_of_nonneg_left (show a I ≤ z from (le_abs_self _).trans (by linarith)) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right size (zero_le_one.trans zp))
    calc
      _ ≤ (z*z)*(z^(T.d+2))^d:=mul_le_mul term (pow_le_pow_left₀ cp cash _) (pow_nonneg cp _) (mul_nonneg (zero_le_one.trans zp) (zero_le_one.trans zp))
      _=_:=by simp only [H,pow_add,pow_mul,pow_two]
  have basic:=geometry p r H A z (fy.trans avail) (by linarith) joint fine (by change nimbus I ≤ z;linarith) head
  have a0:0 ≤ A:=mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (a_pos _)) (pow_nonneg cp _)

  have admit:WilsonVacuumPreResetFiniteHeatSlope.gate I:=⟨(Q.draws.blocks m 0).branches,Q.green⟩
  have prices:=(dated (arch I admit)).choose_spec
  have station:a I=(dated (arch I admit)).choose:=dif_pos admit
  refine ⟨A,a0,?_,basic⟩
  intro i hi l hl x
  change _≤(Fintype.card (Site n):ℝ)*a I*p.coin^d
  rw [station]
  exact prices.2 p i hi l hl x

theorem marked(G:Gauge)(e l r:ℕ):
    ∃v:Gear G→ℝ,∃D:ℕ,∀Q:Realm G (e+1) Credit.leanC,∀m (hm:Q.anchor ≤ m),
      v (Q.mint m hm).gear ≤ Q.cash Credit.leanC m → ∀N (live:m<N) n,
        let p:=cloVent Q m N n hm live 1 zero_lt_one
        let f:=p.n*(holt Q m hm 1 zero_lt_one).P.L
        ∀J T:PChart G f,∀η:ℝ,0<η →
        (∀i ≤ e,∀a ≤ horizon e (r+2*l),∀x,|J i a x| ≤ 1) →
        (∀i ≤ e,∀a ≤ horizon e (r+2*l),∀x,|T i a x| ≤ η) →
        ∀t:ℝ,|t| ≤ 1 → ∀i ≤ e,∀x,
        |reed p.wheel p.shadow p.H (p.T p.n) Q.paid (p.W'+t•J) l T i r x| ≤
          η*(gross (Q.y m) f)^D:=by
  obtain ⟨v,d,prepared⟩:=original G e (r+2*l)
  refine ⟨v,d*WilsonMarkedIndependentSelectedHeat.power e l r,?_⟩
  intro Q m hm cash N live n p f J T η hot quiet word t ht i hi x
  obtain ⟨A,positive,Aold,price⟩:=prepared Q m hm cash N live n
  have native:=WilsonMarkedIndependentSelectedHeat.original p A l r positive Aold J T η hot
    quiet word t ht i hi x
  apply native.trans
  rw [pow_mul]
  apply mul_le_mul_of_nonneg_left _ hot.le
  apply pow_le_pow_left₀ _ price
  unfold fee
  positivity [zero_le_one.trans (holt Q m hm 1 zero_lt_one).book]

end YM.Integration.WilsonMarkedIndependentEnrolledHeatWallet
end
