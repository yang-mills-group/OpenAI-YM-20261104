import YM.Integration.WilsonVacuumPreResetMarkedSignedTransfer

/-! The measured finite recurrence with its actual old vacuum and whole
source table compared with the folded inlet on this identical Scroll. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedFiniteSourcePrice
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetMarkedOrdinaryBound
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open scoped Classical BigOperators
variable {ι:Type}[DecidableEq ι]

theorem original (G:Gauge)(D:ι→ℕ)(I:Finset ι)(k:ι→ℕ)(e i r:ℕ)(hi:i≤e):
    ∃v:Gear G→ℝ,∃M:ℝ,0≤M ∧ ∃d:ℕ,∀Q:Realm G (e+1) Credit.leanC,
    ∀m (hm:Q.anchor ≤ m),v (Q.mint m hm).gear≤Q.cash Credit.leanC m → ∀N (live:m < N) n,
    let p:=cloVent Q m N n hm live 1 zero_lt_one
    let f:=p.n*(holt Q m hm 1 zero_lt_one).P.L
    let cap:=horizon e (r+2*mass k I)
    let P:=(story Q.draws Q.paid N (m+1)).1 f
    ∀η:ℝ,0<η→η≤1→(∀j≤e,∀s≤cap,∀y,|P j s y-p.W' j s y|≤η)→
    ∀K B:family G D,Eu k K→∀a:ι→ℝ,(∀j,0<a j)→
    (∀J⊆I,J.Nonempty→∀j≤e,∀s≤cap,∀y,‖(B J).1 f j s y‖≤weights a J ∧
      ‖(K J).1 f j s y-(B J).1 f j s y‖≤η*weights a J)→
    ∀x,‖(logO Q.draws Q.paid m N K k I).1 n i r x-
      mist p.wheel p.shadow p.H (p.T p.n) Q.paid p.W' B (ratioHigh Q.draws Q.paid N m) k I i r x‖≤
          M*(gross (Q.y m) f)^d*weights a I*η:=by
  obtain ⟨v,M,Mpos,d,issued⟩:=WilsonVacuumPreResetMarkedSignedTransfer.original G D I k e i r hi
  refine ⟨v,M*2^I.card,mul_nonneg Mpos (by positivity),d,?_⟩
  intro Q m hm bought N live n p f cap P η hot small prior K B legal a positiveA faces x
  let V:PChart G f:=η⁻¹•(P-p.W')
  let E:family G D:=fun J=>η⁻¹•(K J-B J)
  let A(u:ι):=2*a u
  have fit(j:ℕ)(hj:j≤e)(s:ℕ)(hs:s≤cap)(y):|V j s y|≤1:=by
    change |η⁻¹*(P j s y-p.W' j s y)|≤1
    rw [abs_mul,abs_inv,abs_of_pos hot]
    exact (mul_le_mul_of_nonneg_left (prior j hj s hs y) (inv_nonneg.mpr hot.le)).trans_eq (inv_mul_cancel₀ hot.ne')
  have doubled(J:Finset ι):weights A J=2^J.card*weights a J:=by
    simp only [weights,A,Finset.prod_mul_distrib,Finset.prod_const]
  have stock(J:Finset ι)(inc:J⊆I)(used:J.Nonempty)(j:ℕ)(hj:j≤e)(s:ℕ)(hs:s≤cap)(y):
      ‖(B J).1 f j s y‖+‖(E J).1 f j s y‖≤weights A J:=by
    obtain ⟨base,change⟩:=faces J inc used j hj s hs y
    have dir:‖(E J).1 f j s y‖≤weights a J:=by
      change ‖η⁻¹•((K J).1 f j s y-(B J).1 f j s y)‖≤weights a J
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hot]
      exact (mul_le_mul_of_nonneg_left change (inv_nonneg.mpr hot.le)).trans_eq
        (by rw [←mul_assoc,inv_mul_cancel₀ hot.ne',one_mul])
    rw [doubled]
    apply (add_le_add base dir).trans
    rw [←two_mul]
    have earned:(2:ℝ)≤2^J.card:=by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) used.card_pos
    exact mul_le_mul_of_nonneg_right earned (positive a (fun u=>(positiveA u).le) J)
  have slip:=issued Q m hm bought N live n V fit B E A (fun u=>mul_pos (by norm_num) (positiveA u)) stock
    η hot.le small x
  have vac:p.W'+η•V=P:=by
    dsimp only [V]
    rw [smul_smul,mul_inv_cancel₀ hot.ne',one_smul];abel
  have occ:(fun J=>B J+η•E J)=K:=by
    funext J
    dsimp only [E]
    rw [smul_smul,mul_inv_cancel₀ hot.ne',one_smul];abel
  have ident: (logO Q.draws Q.paid m N K k I).1 n=
      mist p.wheel p.shadow p.H (p.T p.n) Q.paid P K (ratioHigh Q.draws Q.paid N m) k I:=
    feeleg Q.draws Q.paid m N K k live Q.hG Q.green legal n I
  rw [vac,occ,←ident,doubled] at slip
  apply slip.trans_eq
  ring

end YM.Integration.WilsonVacuumPreResetMarkedFiniteSourcePrice
end
