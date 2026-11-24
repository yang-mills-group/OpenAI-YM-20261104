import YM.Integration.WilsonSeparatedPrefixCanonicalClear
import YM.Integration.WilsonSeparatedPrefixCanonicalFlat

/-! A finite optical interval from the actual positive-weight canonical post to
each globally clear terminal field. The denominator is its original density. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearPost
open QuadraticLocal QuadraticLocal.Earn Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonOriginalCompanionLinearFiling
open WilsonThermometerCorridorRoster
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "T" => Unit×I
local notation "J" => Stock.census I

def fare (I:Type)[Fintype I][DecidableEq I]:ℝ:=Real.exp (Fintype.card (Stock.census (Unit×I)).Mode:ℝ)

theorem original (simple:G.Simple)(cater:Cater (C) R.doors):
    ∀ᶠ b:ℕ in atTop,∀ N p k (bk:b≤k+1) (_kn:k<N) (o:I → Site ((C).side (k+1) p))
      (w:I → ℝ)(F:Config G ((C).side (k+1) p) → Poly (J))(route:∀t,T → Site ((C).side t p)),
    (∀i,0<w i) → route (k+1)=o ∘ Prod.snd →
    (∀t,b≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    Served ((C).path.rep N p (k+1)) (fun (_:I) _=>0) (fun (_:I) _ _=>0) F o w
      (((A).budget (k+1)).supportExponent-1) 1 →
    2≤((A).budget b).supportExponent → ∀U:Config G ((C).side b p),
    flags ((C).path.rep N p b).p.threshold U=∅ → ∀s:(J).Mode,
    ‖(((C).path.rep N p b).eval U:ℂ)⁻¹*gust (C).path N p (k+1) (fun Q=>(F Q).part s) b bk U‖≤
      fare I*(H (k+1))^(6*(k+1-b)*s.val.card)/Poly.toll w s:=by
  filter_upwards [(A).fits.deep.eventually_ge_atTop (Fintype.card T),eventually_ge_atTop 1] with b enough first N p k bk kn o w F route wp home parent stock alpha U clear s
  have jp(t)(bt:b≤t+1):Fintype.card T≤(A).clock.J (t+1)+2:=
    (enough.trans ((A).fits.mono bt)).trans (Nat.le_add_right _ _)
  have vac:=WilsonSeparatedPrefixCanonicalFlat.occupancy R
    (show Fintype.card I≤(A).clock.J (k+1)+2 by simpa only [Fintype.card_prod,Fintype.card_unit,one_mul] using jp k bk) o
  have load(t)(bt:b≤t)(tf:t<k+1):Occupancy (route (t+1)) (apron (A) t) ∧ Occupancy (route t) (apron (A) t):=
    ⟨WilsonSeparatedPrefixCanonicalFlat.occupancy R (jp t (by omega)) _,
      WilsonSeparatedPrefixCanonicalFlat.occupancy R (jp t (by omega)) _⟩
  have posts:=WilsonSeparatedPrefixCanonicalWalk.original R simple cater first kn wp vac stock route home parent load
  obtain ⟨wallet,paid,down⟩:=posts b le_rfl bk
  obtain ⟨_,_,top⟩:=posts (k+1) bk le_rfl
  let X:=fun Q=>lift (F Q)
  have inlet:Integrable X (prior G _):=by simpa only [gust_base,X] using top.1
  have held:=WilsonSeparatedPrefixCanonicalClear.original down (fun i=>(paid i).1) (by linarith) U clear (mask s)
  have field:(gust (C).path N p (k+1) X b bk U).part (mask s)=
      gust (C).path N p (k+1) (fun Q=>(F Q).part s) b bk U:=by
    rw [congrFun (WilsonThermometerCorridorFiling.projected R X inlet (mask s) bk) U]
    have readout:(fun Q=>(X Q).part (mask s))=fun Q=>(F Q).part s:=funext (fun Q=>read (F Q) s)
    rw [readout]
  let value:=‖(((C).path.rep N p b).eval U:ℂ)⁻¹*gust (C).path N p (k+1) (fun Q=>(F Q).part s) b bk U‖
  have cost:Poly.toll wallet (mask s)*value≤fare I:=by
    change Poly.toll wallet (mask s)*‖(((C).path.rep N p b).eval U:ℂ)⁻¹ • (gust (C).path N p (k+1) X b bk U).part (mask s)‖≤fare I at held
    simpa only [field,smul_eq_mul,value] using held
  let W:T → ℝ:=w ∘ Prod.snd
  have base:(∏i∈(mask s).val,W i)=Poly.toll w s:=by
    unfold mask Poly.toll
    rw [Finset.prod_image (fun i _ j _ h=>congrArg Prod.snd h)]
    rfl
  have count:(mask s).val.card=s.val.card:=by
    change (s.val.image place).card=s.val.card
    exact Finset.card_image_of_injective _ (fun _ _ same=>congrArg Prod.snd same)
  let charge:=(H (k+1))^(6*(k+1-b))
  have balance:(Poly.toll wallet (mask s))⁻¹≤(H (k+1))^(6*(k+1-b)*s.val.card)/Poly.toll w s:=by
    have changeBill:∏i∈(mask s).val,(wallet i)⁻¹≤∏i∈(mask s).val,charge*(W i)⁻¹:=
      Finset.prod_le_prod (fun i _=>inv_nonneg.mpr (paid i).1.le) (fun i _=>(paid i).2.2)
    rw [Finset.prod_mul_distrib,Finset.prod_const] at changeBill
    simp only [Finset.prod_inv_distrib] at changeBill
    rw [base,count] at changeBill
    simpa only [Poly.toll,charge,←pow_mul,div_eq_mul_inv] using changeBill
  have unscaled:value≤fare I*(Poly.toll wallet (mask s))⁻¹:=by
    rw [←div_eq_mul_inv,le_div_iff₀ (Poly.worth (fun i=>(paid i).1) (mask s)),mul_comm]
    exact cost
  calc value ≤ _:=unscaled
       _ ≤ fare I*((H (k+1))^(6*(k+1-b)*s.val.card)/Poly.toll w s):=
         mul_le_mul_of_nonneg_left balance (show 0≤fare I from (Real.exp_pos _).le)
       _ = _:=by ring

end YM.Integration.WilsonSeparatedPrefixCanonicalClearPost
end
