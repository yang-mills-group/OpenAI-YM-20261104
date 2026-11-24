import YM.Integration.WilsonVacuumPreResetFiniteHeatWindow

/-! On its one physical torus the change due to the actual signed fine
vacuum is linear in its unweighted discrepancy. The volume dependence
of its price is polynomial, uniformly in the selected ultraviolet top. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatSlope
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatWindow
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{E:Credit}

/-- The heat slope after the common affine drawing with the complete
old signed action at that same date. Constant normalization and the
kinetic input are both fixed during the variation. -/
theorem selected (e i r:ℕ)(hi:i ≤ e):∃C:ℝ,0 ≤ C ∧ ∀{G:Gauge}{I:Arch G}(p:ScrollV e I)
    (A:ℝ),0 ≤ A→
    (∀a ≤ e,∀l ≤ horizon e r,∀x,|casePW p.wheel I.R p.cone p.W' a l x| ≤ A)→
    ∀(T:PChart G (p.n*I.P.L))(η:ℝ),0<η→η ≤ 1→
    (∀a ≤ e,∀l ≤ horizon e r,∀x,|T a l x-p.W' a l x| ≤ η)→∀x,
    |winter p.wheel p.shadow p.H p.Y (p.T p.n) I.R T i r x-
      winter p.wheel p.shadow p.H p.Y (p.T p.n) I.R p.W' i r x| ≤
        C*(fee p A r)^(power e r)*η:=by
  obtain ⟨M,paid,nodes⟩:=WilsonVacuumPreResetWindingTransfer.observed i
  refine ⟨2*M,by positivity,?_⟩
  intro G I p A nonneg enters T η lower upper incoming x
  let D:PChart G (p.n*I.P.L):=η⁻¹•(T-p.W')
  have small(a:ℕ)(ha:a ≤ e)(l:ℕ)(hl:l ≤ horizon e r)(y):|D a l y| ≤ 1:=by
    change |η⁻¹*(T a l y-p.W' a l y)| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr lower)]
    exact (mul_le_mul_of_nonneg_left (incoming a ha l hl y) (inv_nonneg.mpr lower.le)).trans_eq
      (inv_mul_cancel₀ lower.ne')
  obtain ⟨P,order,evaluated⟩:=WilsonVacuumPreResetWindingPolynomial.original p.wheel p.shadow p.H p.Y
    (p.T p.n) I.R p.W' D i r x
  let R:=P-Polynomial.C (P.eval 0)
  have degree:R.natDegree ≤ i:=by apply (Polynomial.natDegree_sub_le ..).trans;simpa using order
  have base:p.W'+(0:ℝ)•D=p.W':=by simp
  have finish:p.W'+η•D=T:=by dsimp only [D];rw [smul_smul,mul_inv_cancel₀ lower.ne',one_smul];abel
  have re(t:ℝ):R.eval t=winter p.wheel p.shadow p.H p.Y (p.T p.n) I.R (p.W'+t•D) i r x-
        winter p.wheel p.shadow p.H p.Y (p.T p.n) I.R p.W' i r x:=by
    simp only [R,Polynomial.eval_sub,Polynomial.eval_C,evaluated,base]
  have zero:R.eval 0=0:=by simp [R]
  let K:ℝ:=(fee p A r)^(power e r)
  have actual(t:ℝ)(q:|t| ≤ 1):|R.eval t| ≤ 2*K:=by
    have first:=window p A r nonneg enters D small t q i hi x
    have last:=window p A r nonneg enters D small 0 (by simp) i hi x
    rw [base] at last
    rw [re t]
    change |(_-summer _ _ _ _ _ (p.W'+t•D) i r x+_)-(_-summer _ _ _ _ _ p.W' i r x+_)| ≤ 2*K
    have form(a b c d:ℝ):|(a-b+c)-(a-d+c)|=|d-b|:=by congr 1;ring
    rw [form]
    apply (abs_sub _ _).trans
    change _ ≤ 2*(fee p A r)^(power e r)
    linarith
  have good:0 ≤ K:=(abs_nonneg _).trans (window p A r nonneg enters D small 0 (by simp) i hi x)
  have priced:=nodes R (2*K) η degree (by positivity) lower.le upper actual
  rw [zero,sub_zero,re η,finish] at priced
  exact priced.trans_eq (by ring)

def gate(I:Gear G):Prop:=I.patch.Branches I.kernel G ∧ LocalRatio I.angle

/-- The original stage bills can be named from the gear before selecting
the course. Every period uses the upper face of the actual finite story. -/
theorem booked(G:Gauge)(e i r:ℕ)(hi:i ≤ e)(E:Credit):
    ∃d:ℕ,∃a:Gear G→ℝ,∃M:ℝ,(∀I,0 ≤ a I) ∧ 0 ≤ M ∧ ∀ Q:Realm G (e+1) E,∀m (hm:Q.anchor ≤ m) N (live:m<N) n,
      let I:=(Q.mint m hm).gear
      let p:=cloVent Q m N n hm live 1 zero_lt_one
      let A:ℝ:=Fintype.card (Site n)*a I*(admissionA I e*Q.cash (costXV G e E) m)^d
      ∀(η:ℝ),0<η→η ≤ 1→
      (∀v ≤ e,∀l ≤ horizon e r,∀x,|(story Q.draws Q.paid N (m+1)).1 (n*I.patch.L) v l x-
        emera (actionW Q.draws Q.paid N (m+1)) (n*I.patch.L) v l x| ≤ η)→∀x,
      |unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r x-
          coil0 Q.draws Q.paid m N n i r x| ≤ M*(fee p A r)^(power e r)*η:=by
  classical
  obtain ⟨d,dated⟩:=WilsonVacuumPreResetFiniteHeatBaseline.original G e (horizon e r)
  let arch(I:Gear G)(p:gate I):Arch G:=aerie 1 I e zero_lt_one p.1 p.2
  let a(I:Gear G):ℝ:=if p:gate I then (dated (arch I p)).choose else 0
  obtain ⟨M,paid,granted⟩:=selected e i r hi
  refine ⟨d,a,M,?_,paid,?_⟩
  · intro I;dsimp only [a];split
    · next p=>exact (dated (arch I p)).choose_spec.1
    · exact le_rfl
  intro Q m hm N live n I p A η lower upper data x
  have admit:gate I:=⟨(Q.draws.blocks m 0).branches,Q.green⟩
  have prices:=(dated (arch I admit)).choose_spec
  have station:a I=(dated (arch I admit)).choose:=dif_pos admit
  have positive:0 ≤ A:=by
    change 0 ≤ (Fintype.card (Site n):ℝ)*a I*p.coin^d
    rw [station]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) prices.1) (pow_nonneg (zero_le_one.trans p.paid) _)
  have shelf:∀v ≤ e,∀l ≤ horizon e r,∀y,|casePW p.wheel Q.paid p.cone p.W' v l y| ≤ A:=by
    intro v hv l hl y
    change _ ≤ (Fintype.card (Site n):ℝ)*a I*p.coin^d
    rw [station]
    exact prices.2 p v hv l hl y
  exact granted p A positive shelf ((story Q.draws Q.paid N (m+1)).1 _) η lower upper data x

theorem original(G:Gauge)(e i r:ℕ)(hi:i ≤ e)(E:Credit):
    ∃d:ℕ,∃a:Gear G→ℝ,∃M:ℝ,0 ≤ M ∧ ∀ Q:Realm G (e+1) E,∀m (hm:Q.anchor ≤ m) N (live:m<N) n,
      let I:=(Q.mint m hm).gear
      let p:=cloVent Q m N n hm live 1 zero_lt_one
      let A:ℝ:=Fintype.card (Site n)*a I*(admissionA I e*Q.cash (costXV G e E) m)^d
      ∀(η:ℝ),0<η→η ≤ 1→
      (∀v ≤ e,∀l ≤ horizon e r,∀x,|(story Q.draws Q.paid N (m+1)).1 (n*I.patch.L) v l x-
        emera (actionW Q.draws Q.paid N (m+1)) (n*I.patch.L) v l x| ≤ η)→∀x,
      |unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r x-
          coil0 Q.draws Q.paid m N n i r x| ≤ M*(fee p A r)^(power e r)*η:=by
  obtain ⟨d,a,M,_,paid,granted⟩:=booked G e i r hi E
  exact ⟨d,a,M,paid,granted⟩

end YM.Integration.WilsonVacuumPreResetFiniteHeatSlope
end
