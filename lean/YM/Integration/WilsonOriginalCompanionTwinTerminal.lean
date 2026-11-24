import YM.Integration.WilsonOriginalCompanionPepperAll
import YM.Integration.WilsonOriginalCompanionGroupToll
import YM.Integration.WilsonThermometerCorridorCash
import YM.Integration.WilsonThermometerMixedBooked

/-! Paid earlier original readings of every proper face with its individual incoming radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionTwinTerminal
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Ribbons
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records Harvest
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open Trace.Physical.GermGraph WilsonThermometerPepperFace
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "A" => R.family.path.levels
local notation "FamilyR" => R.family
local notation "X" => Unit×I
local notation "β" => (A).clock.hatBeta

theorem original (simple:G.Simple)(cater:Cater R.family R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀ N p f (edge:j+1<N) (_:j+2≤f) (anchor:(X)) (l age:ℕ),
    let top:=(FamilyR).path.rep N p (j+2)
    let mid:=(FamilyR).path.rep N p (j+1)
    let step:=(A).clock.op (j+1) p
    ∀(raw:(X)→Three G ((FamilyR).side (j+2) p))(down:(X)→Three G ((FamilyR).side (j+1) p))
      (o:(X)→Site ((FamilyR).side (j+2) p))(w w₀ cost:(X)→ℝ)
      (F:Config G ((FamilyR).side (j+2) p)→Poly (Stock.census (X)))(a:ℝ),
    MenuBoard top raw F o w a 1 → ((A).budget (j+2)).supportExponent-4≤a →
    (∀i,0<w i) → (∀i,0<w₀ i) → (∀i,(w i)⁻¹≤β f^age*(w₀ i)⁻¹) →
    (∀i,Ride step (o i) (step.ratio.parent (o i)) (R.doors N p (j+1) edge) 1 (raw i) (down i) (cost i)) →
    Occupancy o (apron (A) (j+1)) → Occupancy (step.ratio.parent ∘ o) (apron (A) (j+1)) →
    (∀i,2*w i*cost i≤1) →
    (∀i,coverNumber mid.p.B ({step.ratio.parent (o anchor),step.ratio.parent (o i)}:
      Support ((FamilyR).side (j+1) p))≤l) → ((A).clock.op j p).ratio.parent (step.ratio.parent (o anchor))=0 →
    ∀u:ℕ,(FamilyR).ref 0≤u → ∀uj:u≤j,Opened (FamilyR) 0 u p → Opened (FamilyR) 0 j p →
    let m:=Fintype.card (X)
    let price:=(25+24*((A).params j).columns)*(β j)^4*4
    ∀s:(Stock.census (X)).Mode,‖WilsonOriginalCompanionPepperAll.pay R (N:=N) uj
      (fun U=>(step.push top.beta F U).part s)‖≤
      price*4^m*(((m:ℝ)*β f^(4+6*l))^m*β f^(age*s.val.card)/(∏i∈s.val,w₀ i)):=by
  filter_upwards [WilsonThermometerPepperLastRead.original (I:=(X)) (J:=Unit) R simple cater bank wage]
    with j hear N p f edge span anchor l age
  dsimp only
  intro raw down o w w₀ cost F a board wide pos origin metered rides load seated cash close home u ref uj ou oj
  let mid:=(FamilyR).path.rep N p (j+1)
  let top:=(FamilyR).path.rep N p (j+2)
  let step:=(A).clock.op (j+1) p
  let η:=renal (A) (j+1)
  let h:=β (j+2)
  let x:=β f
  let m:=Fintype.card (X)
  let fees:=WilsonThermometerWeakMixedGrouping.radius (atSite anchor) mid m l η (fun i=>η*w i) ()
  let price:=(25+24*((A).params j).columns)*(β j)^4*4
  have hot:1≤x:=((A).fits.delayed f).le
  have prior:1≤h:=((A).fits.delayed (j+2)).le
  have increasing:h≤x:=Many.beta_le' (C:=(FamilyR)) simple span
  have hpos:0<h:=zero_lt_one.trans_le prior
  have stage:η=(h^2)⁻¹:=by unfold η renal probe;rw [Real.rpow_neg hpos.le];norm_num
  have ep:0<η:=by rw [stage];positivity
  have small:η≤1:=by rw [stage];exact inv_le_one_of_one_le₀ (one_le_pow₀ prior)
  have income:η⁻¹≤x^2:=by rw [stage,inv_inv];gcongr
  have priced:=(WilsonThermometerMixedBooked.original R cater edge a raw down o w cost F board wide
    pos rides load seated cash).2 anchor
  have parms:mid.p=(A).budget (j+1):=(R.makes.wilson.represents N p (j+1) edge.le).vac
  have strip:Real.exp (mid.p.supportExponent+1/2)≤x^6:=by
    rw [parms]
    exact (WilsonThermometerCorridorCash.aperture prior (pos anchor) ep small priced).trans
      (pow_le_pow_left₀ hpos.le increasing 6)
  have amount : 0 < m :=Fintype.card_pos_iff.mpr ⟨anchor⟩
  have within(v:Unit):((atSite anchor).contents v).card ≤ m :=Finset.card_le_univ _
  have funds:0<fees:=Finset.prod_pos fun i _=>div_pos
    (mul_pos (div_pos ep (Nat.cast_pos.mpr amount)) (mul_pos ep (pos i))) (Real.exp_pos _)
  have full (d:(X)→ℂ)(admit:∀i,η*w i*‖d i‖≤1/2):
      ‖WilsonOriginalCompanionPepperAll.pay R (N:=N) uj (fun U=>(Poly.pass (Mach (Stock.census (X)) d)*
        step.push top.beta F U).part (whole (X)))‖≤price*(1/fees):=by
    have grant:=hear N p edge (atSite anchor) m l amount within raw down o w cost F a board wide pos
      rides load seated cash close d admit () home u ref uj ou oj
    simpa only [WilsonThermometerPepperFace.home,WilsonOriginalCompanionPepperAll.pay,price,mul_assoc] using grant
  have positive : 0≤price := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (full (fun _=>0) (by simp))) (one_div_pos.mpr funds)
  have reads:=WilsonOriginalCompanionPepperAll.original R (N:=N) uj (fun i=>η*w i)
    (fun i=>mul_pos ep (pos i)) (price*(1/fees)) _
    (StepData.push_integrable ((A).transition_mass (j+1) p top.beta) F board.cleared) full
  intro s
  let other:=Finset.univ\s.val
  have roofs:(∏i∈other,4*(η*w i))≤(4:ℝ)^m*(∏i∈other,w i):=by
    calc _≤ ∏i∈other,(4*w i):=Finset.prod_le_prod
            (fun i _=>mul_nonneg (by norm_num) (mul_nonneg ep.le (pos i).le)) (fun i _=>by gcongr;exact mul_le_of_le_one_left (pos i).le small)
         _=4^other.card*(∏i∈other,w i):=by rw [Finset.prod_mul_distrib,prod_const]
         _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _))
           (Finset.prod_nonneg fun i _=>(pos i).le)
  have fee:=WilsonOriginalCompanionGroupToll.restored mid anchor m l age η x w w₀ s.val
    hot ep pos origin metered income strip
  calc _≤(∏i∈other,4*(η*w i))*(price*(1/fees)):=reads s
       _≤((4:ℝ)^m*(∏i∈other,w i))*(price*(1/fees)):=
         mul_le_mul_of_nonneg_right roofs (mul_nonneg positive (one_div_nonneg.mpr funds.le))
       _=price*4^m*((∏i∈other,w i)/fees):=by ring
       _≤_:=mul_le_mul_of_nonneg_left fee (mul_nonneg positive (by positivity))

end YM.Integration.WilsonOriginalCompanionTwinTerminal
end
