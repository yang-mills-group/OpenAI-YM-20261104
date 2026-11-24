import YM.Integration.WilsonConditionalTaylorSeparatedPurchase
import YM.Integration.RootedVacuumWinding

/-! Every finite occupied vacuum coefficient and rooted rank has a posted
gear fee. A single diagonal purchase at the authentic bookkeeping depth
makes these available on the same original run. The requested incoming
width is the old gear's real incoming width, which its successor supplies. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorVacuumWindingDeposit
open Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonLimitConstruction
open scoped Classical BigOperators Topology
variable {G:Gauge}

abbrev Shape:= ℕ × ℕ × ℕ
def request (z:Shape):ℕ→Gear G→ℝ:=
  match z with
  | (e,i,r) => if hi:i≤e then (RootedVacuumWinding.pricedOnWithRate e i r hi
      (fun I:Gear G=>I.past) (fun I=>I.depth)).choose else fun _ _=>0

def sum (j:ℕ) (I:Gear G):ℝ:=
  ∑ t∈Finset.range (j+1), |((Encodable.decode t : Option Shape)).elim 0 (fun z=>request z j I)|

def Extra : FundedCompanySelection.Prediction G:=FundedMarkedCoverRows.prices sum
theorem prepaid : FundedPredictionSupply.AllPrices (@Extra G):=FundedMarkedCoverRows.purchase sum

private theorem included (A:Levels G) (z:Shape):∀ᶠ m:ℕ in atTop,∀I:Gear G,
    request z (A.clock.J (m+1)) I ≤ sum (A.clock.J (m+1)) I:=by
  have depth:Tendsto (fun m=>A.clock.J (m+1)) atTop atTop:=A.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [depth.eventually_ge_atTop (Encodable.encode z)] with m hm
  intro I
  let j:=A.clock.J (m+1)
  have h:=Finset.single_le_sum (s:=Finset.range (j+1))
    (f:=fun t=>|((Encodable.decode t : Option Shape)).elim 0 (fun a=>request a j I)|)
    (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  exact (le_abs_self _).trans (by simpa only [sum,j,Encodable.encodek,Option.elim_some] using h)

theorem original (R:Run G) (simple:G.Simple) (paid:Extra R.kit) (period:RG05Preconstruction.ReadoutPurchase R.b)
    (n:ℕ) (k D:Fin n→ℕ) (hk:∀i,k i<D i) (e i r:ℕ) (hi:i≤e):
    ∃(s:Gear G→ℝ)(degree:ℕ),(∀I,0<s I) ∧ ∀c q:ℕ,∀ᶠ m:ℕ in atTop,
    ∃(Q:Realm G (e+1) Credit.leanC) (here:Q.anchor≤ m),Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧
      Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧ Cloze D k Q Credit.leanC ∧ Insure n e Q Credit.leanC ∧
      Nonempty (Tribe Q (hol G) Credit.leanC Credit.leanC (WilsonConditionalTaylorSeparatedPurchase.decks (G:=G) k D hk)) ∧
      ∀t,∀mt:m≤t,let h:=here.trans mt
        (s (Q.mint t h).gear)⁻¹ ≤ Q.cash Credit.leanC t ∧
        RootedVacuumWinding.ReceiptOn R e i r c q degree s t Q h:=by
  let z:Shape:=(e,i,r)
  have offered:=RootedVacuumWinding.pricedOnWithRate e i r hi (fun I:Gear G=>I.past) (fun I=>I.depth)
  let v:=offered.choose
  have fixed:request (G:=G) z=v:=dif_pos hi
  obtain ⟨s,a,hs,rate,takes⟩:=offered.choose_spec
  refine ⟨s,a,hs,?_⟩
  intro c q
  obtain ⟨cut,holds⟩:=eventually_atTop.1 ((takes R simple period c q).and (included R.family.path.levels z))
  filter_upwards [FundedMarkedCoverRows.realm R simple sum paid n k D hk e n e,eventually_ge_atTop cut] with m can early
  obtain ⟨Q,levels,scheme,date,birth,cl,ins,fields,raised⟩:=can
  refine ⟨Q,birth.le,levels,scheme,date,birth,cl,ins,fields,?_⟩
  intro t mt
  have h:Q.anchor≤t:=birth.le.trans mt
  have quote:=holds t (early.trans mt)
  have bill:=quote.2 (Q.mint t h).gear
  rw [fixed] at bill
  have budget:=bill.trans ((raised t mt h).choose_spec.2)
  exact ⟨(rate _ _).trans budget,quote.1 Q h levels scheme date budget⟩

end YM.Integration.WilsonConditionalTaylorVacuumWindingDeposit
end

