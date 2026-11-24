import YM.Integration.WilsonMovingSensorOriginal
import YM.Integration.FundedMarkedCoverRows

/-! Admit the original winding supplier for every positive-valence finite
sensor on the one Wilson reserve before choosing a sensor or its cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSensorReserve
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue
open scoped Classical Topology BigOperators

open FullVolume WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G : Gauge}

open WilsonLimitConstruction WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Patrol
abbrev Shape:=ℕ×ℕ×ℕ

def request (z:Shape):ℕ→Gear G→ℝ:=
  match z with
  | (e,i,r) => if hi:i≤e then fun _ =>
      (WilsonMovingSensorOriginal.quoted (G:=G) e i r hi).choose_spec.choose else fun _ _=>0

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

/-- One admitted independent width and stepped Wilson field work on every
later date and each finite sensor circumference, including circumference
chosen independently of the physical period. -/
theorem original (e i r:ℕ) (hi:i≤e) :
    ∃ (s:Gear G→ℝ) (U:Credit), (∀I,0<s I) ∧ ∀ (R:Run G), G.Simple → Extra R.kit →
    ∀ᶠ m:ℕ in atTop, ∃ (Q:Realm G (e+1) Credit.leanC) (start : Q.anchor ≤ m),
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
      ∀ t, ∀ mt:m≤ t, let I :=(Q.mint t (start.trans mt)).gear
        (perchA (s I) r)⁻¹ ≤ Q.cash Credit.leanC t ∧
        ∀ (N:ℕ) (n:Side), t<N → let A :=windPay (s I) (Q.cash U t) r
          ∀ (H:ℕ) (b:ℝ), 0<b →
        (H:ℝ)*Real.log b + (r+1:ℕ)*Real.log (Fintype.card (Co n (Hooks G)):ℝ) +
          Real.log (2*A) ≤ (perchA (s I) r/16)*n.val → ∀ w:stars G r n→ℝ, (∀x,‖w x‖≤1) →
        2*‖∑ x:stars G r n,w x*(lagoon (freshet R.family.path.levels R.metals.O N t i (r+1)) n x-
          coil0 R.family.path.levels R.metals.O t N n i (r+1) x)‖≤ b^(-(H:ℝ)) := by
  let z:Shape:=(e,i,r)
  have offered:=WilsonMovingSensorOriginal.quoted (G:=G) e i r hi
  let s:=offered.choose
  let c:=offered.choose_spec.choose
  obtain ⟨U,hs,take⟩:=offered.choose_spec.choose_spec
  refine ⟨s,U,fun I=>(hs I).1,?_⟩
  intro R simple paid
  let degrees:Fin 0→ℕ:=fun i=>i.elim0
  have inside:=included R.family.path.levels z
  obtain ⟨cut,holds⟩:=eventually_atTop.mp inside
  filter_upwards [FundedMarkedCoverRows.realm R simple sum paid 0 degrees degrees (fun i=>i.elim0) e 0 e,
    eventually_ge_atTop cut] with m booked early
  obtain ⟨Q,levels,scheme,date,birth,_,_,_,raised⟩:=booked
  refine ⟨Q,birth.le,levels,scheme,date,birth,?_⟩
  intro t mt
  let here:=birth.le.trans mt
  let I :=(Q.mint t here).gear
  have selected:request (G:=G) z (R.family.path.levels.clock.J (t+1)) I=c I:=by
    simp only [request,z,dif_pos hi,c]
  have charge:=holds t (early.trans mt) I
  rw [selected] at charge
  have actual:=charge.trans ((raised t mt here).choose_spec.2)
  exact ⟨(hs I).2.trans actual,fun N n date=>take R Q levels scheme t N n here date actual⟩

end YM.Integration.WilsonMovingSensorReserve
end
