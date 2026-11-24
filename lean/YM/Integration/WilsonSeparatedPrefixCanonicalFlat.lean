import YM.Integration.WilsonSeparatedPrefixCanonicalWalk
import YM.Integration.WilsonOriginalCompanionTwinTerminal
import YM.Integration.WilsonOriginalCompanionLinearFiling

/-! At all sufficiently old common captures, one topped original numerical menu pays every
ordinary subface at every earlier flat on the same physical period. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalFlat
open QuadraticLocal QuadraticLocal.Earn Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonOriginalCompanionLinearFiling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "X" => Unit×I
local notation "J" => Stock.census I

theorem occupancy {T:Type} [Fintype T] {j m p:ℕ} (fit:Fintype.card T≤(A).clock.J (j+1)+2)
    (o:T → Site ((C).side m p)): Occupancy o (apron (A) j) := by
  intro y
  refine (Finset.card_le_univ _).trans ?_
  change Fintype.card T≤((A).clock.J (j+1)+2)*((C).S.block j).val^4
  exact fit.trans (Nat.le_mul_of_pos_right _ (pow_pos ((C).S.block j).property 4))

theorem original (simple:G.Simple)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j+2≤k+1) (kn:k<N) (l:ℕ),
    ∀(o:I → Site ((C).side (k+1) p))(F:Config G ((C).side (k+1) p) → Poly J)(w:I → ℝ)
      (route:∀t,X → Site ((C).side t p))(anchor:X),
    (∀i,0<w i) → route (k+1)=o ∘ Prod.snd →
    (∀t,j+1≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    Served ((C).path.rep N p (k+1)) (fun (_:I) _=>0) (fun (_:I) _ _=>0)
      F o w (((A).budget (k+1)).supportExponent-1) 1 →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p →
    let m:=Fintype.card X
    ∀s:(J).Mode,‖(amount R (N:=N) F (uj.trans (by omega))).part s‖ ≤
      (25+24*((A).params j).columns)*(H j)^4*4*4^m*
        (((m:ℝ)*(H (k+1))^(4+6*l))^m * (H (k+1))^(6*(k+1-(j+2))*s.val.card)/Poly.toll w s) := by
  filter_upwards [WilsonOriginalCompanionTwinTerminal.original (I:=I) R simple cater bank wage,
    (A).fits.deep.eventually_ge_atTop (Fintype.card X)] with j hear enough
  intro N p k height kn l o F w route anchor wp home parent stock close fixed u ref uj ou oj
  dsimp only
  have jp(t)(jt:j≤t+1):Fintype.card X ≤ (A).clock.J (t+1)+2:=by
    exact (enough.trans ((A).fits.mono jt)).trans (Nat.le_add_right _ _)
  have vac:Occupancy o (apron (A) k):=occupancy R (by simpa only [Fintype.card_prod,Fintype.card_unit,one_mul] using jp k (by omega)) _
  have load (t)(jt:j+1≤t)(tk:t<k+1):Occupancy (route (t+1)) (apron (A) t) ∧ Occupancy (route t) (apron (A) t):=
    ⟨occupancy R (jp t (by omega)) _,occupancy R (jp t (by omega)) _⟩
  let W:X → ℝ:=w ∘ Prod.snd
  let lifted:=fun U=>WilsonThermometerCorridorRoster.lift (F U)
  let below:=gust (C).path N p (k+1) lifted (j+2) height
  obtain ⟨wallet,paid,post⟩:=WilsonSeparatedPrefixCanonicalWalk.original R simple cater
    (by omega:0<j+1) kn wp vac stock route home parent load (j+2) (by omega) height
  have restore:((A).clock.op (j+1) p).ratio.parent ∘ route (j+2)=route (j+1):=(parent _ le_rfl (by omega)).symm
  intro s
  have cut:=hear N p (k+1) (by omega) height anchor l (6*(k+1-(j+2))) (fun _=>0) (fun _=>0)
    (route (j+2)) wallet W (fun _=>0) below _ post (by linarith) (fun i=>(paid i).1)
    (fun i=>wp _) (fun i=>(paid i).2.2) (fun _=>Ride.vac) (load _ le_rfl (by omega)).1
    (by rw [restore];exact (load _ le_rfl (by omega)).2) (by simp)
    (fun i=>by simpa only [←restore,Function.comp_apply] using (close i))
    (by simpa only [←restore,Function.comp_apply] using fixed) u ref uj ou oj (WilsonThermometerCorridorRoster.mask s)
  have B:=WilsonSeparatedPrefixCanonicalWalk.board R cater kn wp vac stock
  have copy:Integrable lifted (prior G _):=(WilsonThermometerCorridorRoster.admit _ B
    ((R.T.sticks N p).prices (k+1) (Nat.zero_le _) kn).1.valid wp wp (fun _=>le_rfl)).1
  have seed:=credited R (N:=N) F s copy height uj
  change ‖_‖≤_ at cut
  rw [seed,←coordinate R _ B.1 s] at cut
  have weight:(∏i∈(WilsonThermometerCorridorRoster.mask s).val,W i)=Poly.toll w s:=by
    unfold WilsonThermometerCorridorRoster.mask Poly.toll
    rw [Finset.prod_image (fun i _ j _ h=>congrArg Prod.snd h)]
    rfl
  have count:(WilsonThermometerCorridorRoster.mask s).val.card=s.val.card:=by
    change (s.val.image WilsonThermometerCorridorRoster.place).card=s.val.card
    exact Finset.card_image_of_injective _ (fun _ _ same=>congrArg Prod.snd same)
  rw [weight,count] at cut
  exact cut

end YM.Integration.WilsonSeparatedPrefixCanonicalFlat
end
