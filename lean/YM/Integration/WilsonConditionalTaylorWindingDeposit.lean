import YM.Integration.WilsonConditionalTaylorSeparatedPurchase
import YM.Integration.FundedMarkedWindingWindow

/-! Every finite scalar/ordered-field/mixed-mask winding test has a posted
gear fee. A single diagonal purchase at the authentic bookkeeping depth
makes these available on the same original run. The requested incoming
width is the old gear's real incoming width, which its successor supplies. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWindingDeposit
open Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonLimitConstruction
open scoped Classical BigOperators Topology
variable {G:Gauge}

abbrev Shape:= Σ n:ℕ,Finset (Fin n) × Finset (Fin n) × Fin n × (Fin n→ℕ) × (Fin n→ℕ) × ℕ × ℕ × ℕ × ℕ
private noncomputable instance code : Encodable Shape:=Encodable.ofCountable Shape

def request (z:Shape):ℕ→Gear G→ℝ:=
  match z with
  | ⟨_,J,Z,o,D,k,e,i,r,d⟩ =>
    if h:J⊆Z∧o∈J∧i≤e then (FundedMarkedWindingWindow.pricedOnWithRate h.1 o h.2.1 D k e i r h.2.2
      (fun I:Gear G=>I.past) (fun I=>I.depth) d).choose else fun _ _=>0

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
    (n:ℕ) (J Z:Finset (Fin n)) (inside:J⊆Z) (o:Fin n) (anchor:o∈J)
    (k D:Fin n→ℕ) (hk:∀i,k i<D i) (e i r d:ℕ) (hi:i≤e):
    ∃(s:Gear G→ℝ)(degree:ℕ),(∀I,0<s I) ∧ ∀c q:ℕ,∀ᶠ m:ℕ in atTop,
    ∃(Q:Realm G (e+1) Credit.leanC) (here:Q.anchor≤ m),Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧
      Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧ Cloze D k Q Credit.leanC ∧ Insure n e Q Credit.leanC ∧
      Nonempty (Tribe Q (hol G) Credit.leanC Credit.leanC (WilsonConditionalTaylorSeparatedPurchase.decks (G:=G) k D hk)) ∧
      ∀t,∀mt:m≤t,FundedMarkedWindingWindow.ReceiptOn R J Z o D k e i r d c q degree (fun I=>I.past) s t Q (here.trans mt):=by
  let z:Shape:=⟨n,J,Z,o,D,k,e,i,r,d⟩
  have offered:=FundedMarkedWindingWindow.pricedOnWithRate inside o anchor D k e i r hi
    (fun I:Gear G=>I.past) (fun I=>I.depth) d
  let v:=offered.choose
  have fixed:request (G:=G) z=v:=dif_pos ⟨inside,anchor,hi⟩
  obtain ⟨s,a,hs,_,_,takes⟩:=offered.choose_spec
  refine ⟨s,a,hs,?_⟩
  intro c q
  obtain ⟨cut,holds⟩:=eventually_atTop.1 ((takes R simple period c q).and (included R.family.path.levels z))
  filter_upwards [FundedMarkedCoverRows.realm R simple sum paid n k D hk e n e,eventually_ge_atTop cut] with m can early
  obtain ⟨Q,levels,scheme,date,birth,cl,ins,fields,raised⟩:=can
  refine ⟨Q,birth.le,levels,scheme,date,birth,cl,ins,fields,?_⟩
  intro t mt
  have h:Q.anchor≤t:=birth.le.trans mt
  have quote:=holds t (early.trans mt)
  apply quote.1 Q h date
  have bill:=quote.2 (Q.mint t h).gear
  rw [fixed] at bill
  exact bill.trans ((raised t mt h).choose_spec.2)

end YM.Integration.WilsonConditionalTaylorWindingDeposit
end

