import YM.Integration.WilsonOriginalCompanionLinearFiling
import YM.Integration.WilsonOriginalGalleryTwinWalk
import YM.Integration.WilsonOriginalCompanionTwinTerminal
import YM.Integration.WilsonThermometerCorridorQuote

/-! The actual canonical earlier credit of the doubled, still masked, entire incoming gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionTwinCredit
open QuadraticLocal QuadraticLocal.Earn Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonOriginalGalleryTwins WilsonOriginalCompanionLinearFiling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){T I:Type}[Countable I]
local notation "FamilyR" => R.family
local notation "A" => (FamilyR).path.levels
local notation "H" => (A).clock.hatBeta
local notation "V" => Fin 3
local notation "X" => Unit×((V)×Bool)

def fare (f j l:ℕ):ℝ:=(25+24*(H f))*(H f)^4*4*4^6*(6*(H f)^(4+6*l))^6*(H f)^(36*(f-(j+2)))

private theorem full_load {j m p:ℕ}(four:4≤(A).clock.J (j+1))(o:(X)→Site ((FamilyR).side m p)):
    Occupancy o (apron (A) j):=by
  intro y
  refine (Finset.card_le_univ _).trans ?_
  change Fintype.card (X)≤((A).clock.J (j+1)+2)*((FamilyR).S.block j).val^4
  simp only [Fintype.card_prod,Fintype.card_unit,Fintype.card_fin,Fintype.card_bool,one_mul]
  calc 3*2≤(A).clock.J (j+1)+2:=by omega
       _≤_:=Nat.le_mul_of_pos_right _ (pow_pos ((FamilyR).S.block j).property 4)

theorem original (simple:G.Simple)(cater:Cater (FamilyR) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f) (fn:f≤N)(l:ℕ),
    ∀(o:(V)→Site ((FamilyR).side f p))(D:Gallery T I o ((FamilyR).path.rep N p f) (Marks (V)))(x:T)(w:(V)→ℝ)
      (route:∀k,(X)→Site ((FamilyR).side k p))(anchor:(X)),
    (∀i,0<w i) → route f=(o ∘ Prod.fst) ∘ Prod.snd →
    (∀k,j+1≤k → k<f → route k=((A).clock.op k p).ratio.parent ∘ route (k+1)) →
    0≤((A).budget f).supportExponent-2 →
    D.E.Paid (fun v=>w v^2) ((FamilyR).path.rep N p f).p.B (((A).budget f).supportExponent-2) 1 →
    D.K.Paid (fun v=>w v^2) ((FamilyR).path.rep N p f).p.B (((A).budget f).supportExponent-2) 1 →
    Integrable (D.density x) (prior G _) →
    (∀i,coverNumber ((FamilyR).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(FamilyR).ref 0≤u → ∀uj:u≤j,Opened (FamilyR) 0 u p → Opened (FamilyR) 0 j p →
    ∀s:(Marks ((V)×Bool)).Mode,Poly.toll (w ∘ Prod.fst) s*
      ‖(amount R (N:=N) (entered D x) (uj.trans (by omega))).part s‖≤fare R f j l:=by
  filter_upwards [WilsonOriginalCompanionTwinTerminal.original (I:=(V)×Bool) R simple cater bank wage,
    WilsonThermometerCorridorQuote.columns R simple,(A).fits.deep.eventually_ge_atTop 4] with j hear cols four
  intro N p f height fn l o D x w route anchor pos home parent expo reg forced earned close fixed u ref uj ou oj s
  have edge:j+1<N:=by omega
  have occupies (k)(jk:j+1≤k)(kf:k<f):
      Occupancy (route (k+1)) (apron (A) k) ∧ Occupancy (route k) (apron (A) k):=by
    have funded:=four.trans ((A).fits.mono (show j≤k+1 by omega))
    exact ⟨full_load R funded _,full_load R funded _⟩
  let W:(X)→ℝ:=(w ∘ Prod.fst) ∘ Prod.snd
  let lifted:=fun U=>WilsonThermometerCorridorRoster.lift (entered D x U)
  let F:=gust (FamilyR).path N p f lifted (j+2) height
  obtain ⟨wallet,paid,post⟩:=WilsonOriginalGalleryTwinWalk.original R simple cater (by omega :0<j+1) fn
    D x w pos route home parent occupies expo reg forced earned (j+2) (by omega) height
  have restore:((A).clock.op (j+1) p).ratio.parent ∘ route (j+2)=route (j+1):=(parent _ le_rfl (by omega)).symm
  have cut:=hear N p f edge height anchor l (6*(f-(j+2))) (fun _=>0) (fun _=>0) (route (j+2)) wallet W
    (fun _=>0) F _ post (by linarith) (fun i=>(paid i).1) (fun i=>pos _) (fun i=>(paid i).2.2)
    (fun _=>Ride.vac) (occupies _ le_rfl (by omega)).1
    (by rw [restore];exact (occupies _ le_rfl (by omega)).2) (by simp)
    (fun i=>by simpa only [←restore,Function.comp_apply] using (close i))
    (by simpa only [←restore,Function.comp_apply] using fixed) u ref uj ou oj (WilsonThermometerCorridorRoster.mask s)
  have B:=WilsonOriginalGalleryTwinBoard.original D x w pos expo reg forced earned
  have wp(i:(V)×Bool):0<(w ∘ Prod.fst) i:=pos _
  have copy:Integrable lifted (prior G _):=(WilsonThermometerCorridorRoster.admit _ B
    ((R.T.sticks N p).prices f (Nat.zero_le _) fn).1.valid wp wp (fun _=>le_rfl)).1
  have seed:=credited R (N:=N) (entered D x) s copy height uj
  change ‖_‖≤_ at cut
  rw [seed,←coordinate R _ B.1 s] at cut
  have weight:(∏i∈(WilsonThermometerCorridorRoster.mask s).val,W i)=Poly.toll (w ∘ Prod.fst) s:=by
    unfold WilsonThermometerCorridorRoster.mask Poly.toll
    rw [Finset.prod_image (fun i _ j _ h=>congrArg Prod.snd h)]
    rfl
  have positive:=Poly.worth wp s
  have large:1≤H f:=((A).fits.delayed f).le
  have jle:H j≤H f:=Many.beta_le' (C:=(FamilyR)) simple (by omega)
  have jpos:0≤H j:=zero_le_one.trans ((A).fits.delayed j).le
  have a0:0≤25+24*(H f):=by linarith
  have pf:(25+24*((A).params j).columns)*(H j)^4*4≤(25+24*(H f))*(H f)^4*4:=by
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    exact (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg jpos 4)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ jpos jle _) a0)
  have m:Fintype.card (X)=6:=by decide
  rw [m,weight,←mul_div_assoc] at cut
  have cash:=(le_div_iff₀ positive).mp cut
  rw [mul_comm] at cash
  refine cash.trans ?_
  have tail:6*(f-(j+2))*(WilsonThermometerCorridorRoster.mask s).val.card≤36*(f-(j+2)):=by
    have le:=(Finset.card_le_univ (WilsonThermometerCorridorRoster.mask s).val)
    rw [m] at le
    nlinarith [Nat.mul_le_mul_left (6*(f-(j+2))) le]
  dsimp only [fare]
  rw [mul_assoc _ ((6*(H f)^(4+6*l))^6)]
  exact mul_le_mul (mul_le_mul_of_nonneg_right pf (by norm_num)) (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ large tail) (by positivity)) (by positivity) (by positivity)

end YM.Integration.WilsonOriginalCompanionTwinCredit
end
