import YM.Integration.WilsonVacuumPreResetFiniteHeatReset

/-! A single enrolled stage quote pays the signed inherited Wilson
pre-reset sensitivity by a fixed power of the true side and clock. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatFinance
open Bloch Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatWindow
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{I:Arch G}

theorem geometry(p:ScrollV e I)(r d:ℕ)(A z:ℝ)(floor:5 ≤ z)(width:((horizon e r+2:ℕ):ℝ) ≤ z)
    (joint:(Fintype.card (Joint G (p.n*I.P.L) p.n):ℝ) ≤ z)
    (fine:(Fintype.card (Woods G (p.n*I.P.L)):ℝ) ≤ z)(mass:I.mass ≤ z)(old:A ≤ z^d):
    fee p A r ≤ z^(2+d+3*(horizon e r)):=by
  let h:=horizon e r
  let D:=1+d+3*h
  have b:1 ≤ z:=by linarith
  have zp:=zero_le_one.trans b
  have cell:1+(Fintype.card (Woods G (p.n*I.P.L)):ℝ)*I.mass ≤ z^3:=by
    calc
      _ ≤ 1+z*z:=add_le_add le_rfl (mul_le_mul fine mass (zero_le_one.trans I.book) zp)
      _ ≤ 2*z^2:=by nlinarith [one_le_pow₀ b (n:=2)]
      _ ≤ z*z^2:=mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg zp _)
      _=_:=by ring
  have cellpay: (1+(Fintype.card (Woods G (p.n*I.P.L)):ℝ)*I.mass)^h ≤ z^D:=by
    apply (pow_le_pow_left₀ (by positivity [zero_le_one.trans I.book]) cell h).trans
    rw [←pow_mul]
    exact pow_le_pow_right₀ b (by unfold D;omega)
  have scale:z ≤ z^D:=le_self_pow₀ b (by unfold D;omega)
  have principal:=old.trans (pow_le_pow_right₀ b (show d ≤ D by unfold D;omega))
  have budget:fee p A r ≤ 5*z^D:=by
    change ((horizon e r+2:ℕ):ℝ)+_+_+A+_^h ≤ _
    linarith only [width.trans scale,joint.trans scale,mass.trans scale,principal,cellpay]
  apply budget.trans
  calc
    _ ≤ z*z^D:=mul_le_mul_of_nonneg_right floor (pow_nonneg zp _)
    _=_:=by rw [←pow_succ'];congr 1;unfold D h;omega

private theorem sites(n:Side):(Fintype.card (Site n):ℝ)=(n.val:ℝ)^4:=by exact_mod_cast Lattice.site_card n
private theorem woods(G:Gauge)(n:Side):
    (Fintype.card (Woods G n):ℝ)=(n.val:ℝ)^4*Fintype.card (Stationary.Loc G 1):=by
  change (Fintype.card (Site n × Stationary.Loc G 1):ℝ)=_
  simp only [Fintype.card_prod,Nat.cast_mul,sites]

def gross(z:ℝ)(n:Side):ℝ:=z*(1+n.val:ℝ)^4

/-- The invoice is a published function of the original gear; its
exponent is independent of date, top, period, and size of the old action.
The time-dependent input is the actual raw signed discrepancy. -/
theorem original(G:Gauge)(e i r:ℕ)(hi:i ≤ e):
    ∃v:Gear G→ℝ,∃D:ℕ,∀Q:Realm G (e+1) Credit.leanC,∀m (hm:Q.anchor ≤ m),
      v (Q.mint m hm).gear ≤ Q.cash Credit.leanC m→∀ N (_live:m<N) n,
        let I:=(Q.mint m hm).gear
        let f:=n*I.patch.L
        ∀η:ℝ,0<η→η ≤ 1→
        (∀a ≤ e,∀l ≤ horizon e r,∀x,|(story Q.draws Q.paid N (m+1)).1 f a l x-
          emera (actionW Q.draws Q.paid N (m+1)) f a l x| ≤ η)→∀x,
        |unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r x-
          coil0 Q.draws Q.paid m N n i r x| ≤ (gross (Q.y m) f)^D*η:=by
  obtain ⟨d,a,M,a_pos,m_pos,grant⟩:=WilsonVacuumPreResetFiniteHeatSlope.booked G e i r hi Credit.leanC
  let T:=costXV G e Credit.leanC
  let c:ℝ:=Fintype.card (Stationary.Loc G 1)
  let H:=2+(T.d+2)*d
  let D:=2+H+3*horizon e r
  let v(I:Gear G):ℝ:=5+((horizon e r+2:ℕ):ℝ)+2*c+|a I|+nimbus I+admissionA I e+T.x+M
  refine ⟨v,1+D*power e r,?_⟩
  intro Q m hm enrolled N live n I f η lower upper data x
  let y:=Q.y m
  let z:=gross y f
  let p:=cloVent Q m N n hm live 1 zero_lt_one
  have te:0 ≤ T.x:=zero_le_one.trans T.good
  have ae:1 ≤ admissionA I e:=admissionSeal _
  have mass:1 ≤ nimbus I:=(holt Q m hm 1 zero_lt_one).book
  have nn:0 ≤ c:=Nat.cast_nonneg _
  have widening:0 ≤ ((horizon e r+2:ℕ):ℝ):=Nat.cast_nonneg _
  have incomes:5+((horizon e r+2:ℕ):ℝ)+2*c+|a I|+nimbus I+admissionA I e+T.x+M ≤ y:=by
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
  have fp0:0 ≤ fee p A r:=by unfold fee;positivity [zero_le_one.trans (holt Q m hm 1 zero_lt_one).book]
  have issued:=grant Q m hm N live n η lower upper data x
  apply issued.trans
  apply mul_le_mul_of_nonneg_right _ lower.le
  calc
    _ ≤ z*(z^D)^(power e r):=mul_le_mul (by linarith) (pow_le_pow_left₀ fp0 basic _)
      (pow_nonneg fp0 _) (zero_le_one.trans zp)
    _=_:=by simp only [pow_add,pow_one,pow_mul,z,y]

end YM.Integration.WilsonVacuumPreResetFiniteHeatFinance
end
