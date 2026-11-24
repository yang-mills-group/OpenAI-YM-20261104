import YM.Integration.WilsonVacuumPreResetFiniteHeatFinance
import YM.Integration.WilsonFiniteVacuumWindingReset
import YM.WilsonCoeffUV.VacuumUV

/-! The signed fresh winding charge, foil summability, and true kinetic
reversion have separate original suppliers on the same enrolled course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatCourse
open Bloch Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open ActualRunAdmissionScales Next.Foundations PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{E:Credit}

theorem shelf (Q:Realm G (e+1) E){m N:ℕ}(hm:Q.anchor ≤ m)(live:m<N)(a r:ℕ)(ha:a ≤ e):
    ∃V,Amber terrain (Q.mint m hm).σ V (freshet Q.draws Q.paid N m a r):=by
  obtain ⟨T,price⟩:=Fk.export_domain G E (e+1) a r 0 (by omega)
  have h:=((((price.money Q m hm).2 N N live.le le_rfl).2.2.2 live).1).pose
  exact ⟨_,h⟩

theorem reversion(G:Gauge)(e i l:ℕ)(hi:i ≤ e):∃v:Gear G→ℝ,∃d:ℕ,
    ∀Q:Realm G (e+1) Credit.leanC,∀m (hm:Q.anchor ≤ m),
      v (Q.mint m hm).gear ≤ Q.cash Credit.leanC m→∀N,m<N→
      rimJ (ratioHigh Q.draws Q.paid N m) i l ≤ Q.y m ^ d:=by
  obtain ⟨d,issued⟩:=rimMoney G i l e hi
  choose A positive paid using issued
  let T:=costXV G e Credit.leanC
  let v(I:Gear G):ℝ:=max (A I) T.x
  refine ⟨v,1+(T.d+1)*d,?_⟩
  intro Q m hm funded N live
  let y:=Q.y m
  let I:=(Q.mint m hm).gear
  have budget:v I ≤ y:=by simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using funded
  have rich:1 ≤ y:=Q.depth m hm
  have cp:=Credit.purchase T rich
  have fee:Q.cash T m ≤ y^(T.d+1):=by
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right ((le_max_right ..).trans budget) (pow_nonneg (zero_le_one.trans rich) _)
  have result:=paid I (ReelTime Q (i:=e) le_rfl hm live (le_refl N) (le_refl N))
  apply result.trans
  calc
    _ ≤ y*(y^(T.d+1))^d:=mul_le_mul ((le_max_left ..).trans budget)
      (pow_le_pow_left₀ (zero_le_one.trans cp) fee _) (pow_nonneg (zero_le_one.trans cp) _) (zero_le_one.trans rich)
    _=_:=by simp only [pow_add,pow_one,pow_mul,y]

theorem fresh(G:Gauge)(e i r:ℕ)(hi:i ≤ e):
    ∃v:ℕ→Gear G→ℝ,∃d:ℕ,∀(R:Run G),G.Simple→RG05Preconstruction.ReadoutPurchase R.b→
      ∀ᶠm:ℕ in atTop,∀(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m),
        Q.draws=R.family.path.levels→Q.paid=R.metals.O→Q.y=zz R.family.path.levels→
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m→
        ∀N p:ℕ,m<N→∀x,|RootedVacuumWinding.ground R.family.path.levels R.metals.O N m (R.family.side m p) i r x| ≤
          (admittedCost R.family.path.levels m)^d*
            Real.exp (-((R.family.side m p).val:ℝ)/(4*Q.y m)):=by
  obtain ⟨v,w,d,win,off,paid⟩:=RootedVacuumWinding.pricedOnWithRate (G:=G) e i r hi (fun _=>1) (fun _=>zero_lt_one)
  refine ⟨v,d,?_⟩
  intro R simple reading
  filter_upwards [paid R simple reading 0 0] with m invoice
  intro Q hm draws O clock budget N p live x
  let I:=(Q.mint m hm).gear
  let n:=R.family.side m p
  let y:=Q.y m
  have yp:0<y:=zero_lt_one.trans_le (Q.depth m hm)
  have wpos:=win I
  have wfee:(w I)⁻¹ ≤ y:=by
    simpa only [Realm.cash,Credit.leanC,Credit.buy,pow_one,one_mul] using (off _ I).trans budget
  have lower:1 ≤ w I*y:=by
    calc
      _=w I*(w I)⁻¹:=(mul_inv_cancel₀ wpos.ne').symm
      _ ≤ _:=mul_le_mul_of_nonneg_left wfee wpos.le
  obtain ⟨A,_,small,h⟩:=invoice Q hm draws O clock budget N p live
  have item:=WilsonVacuumPreResetFiniteHeatReset.entry wpos.le
    (RootedVacuumWinding.ground R.family.path.levels R.metals.O N m n i r) x
  apply (item.trans (h 0 (x 0))).trans (small.trans _)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans (admittedCost_one _ _)) _)
  apply Real.exp_le_exp.mpr
  change -(w I/4)*(n.val:ℝ) ≤ -(n.val:ℝ)/(4*y)
  apply (le_div_iff₀ (by positivity :0<4*y)).2
  nlinarith only [mul_le_mul_of_nonneg_right lower (show 0 ≤ (n.val:ℝ) from Nat.cast_nonneg _)]

end YM.Integration.WilsonVacuumPreResetFiniteHeatCourse
end
