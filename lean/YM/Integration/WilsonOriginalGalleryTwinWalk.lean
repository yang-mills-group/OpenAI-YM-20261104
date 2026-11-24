import YM.Integration.WilsonOriginalGalleryTwinBoard
import YM.Integration.WilsonThermometerCorridorWalk
import YM.Integration.WilsonThermometerCorridorRoster

/-! The original physical doubled gallery re-enters every earlier canonical mixed step with zero unary source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGalleryTwinWalk
open Filter Finset Lattice Wilson RG Ac Marker Push QuadraticLocal MergeProof MergeProof.Accent MeasureTheory
open RG05Readout.Many RG05Readout.Address RG05Readout.Pantry Lodestar Extra.Multi Extra.Trajectories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Lotus
open WilsonOriginalGalleryTwins
open scoped BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}(R:Run G)(simple:G.Simple){V T I:Type}[Fintype V][DecidableEq V][Countable I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "X" => Unit×(V×Bool)

include simple in
theorem original (cater:Cater (C) R.doors){b f N p:ℕ}(first:0<b)(fn:f≤N)
    {o:V → Site ((C).side f p)}(D:Gallery T I o ((C).path.rep N p f) (Marks V))(x:T)(w:V→ℝ)(pos:∀i,0<w i)
    (routes:∀j,X→Site ((C).side j p))(home:routes f=(o ∘ Prod.fst) ∘ Prod.snd)
    (same:∀j,b≤j → j<f → routes j=((A).clock.op j p).ratio.parent ∘ routes (j+1))
    (load:∀j,b≤j → j<f → Occupancy (routes (j+1)) (apron (A) j) ∧ Occupancy (routes j) (apron (A) j))
    (expo:0≤((A).budget f).supportExponent-2)
    (reg:D.E.Paid (fun v=>w v^2) ((C).path.rep N p f).p.B (((A).budget f).supportExponent-2) 1)
    (forced:D.K.Paid (fun v=>w v^2) ((C).path.rep N p f).p.B (((A).budget f).supportExponent-2) 1)
    (actual:Integrable (D.density x) (prior G _)):
    let W: X → ℝ := (w ∘ Prod.fst) ∘ Prod.snd
    let F:=fun U=>WilsonThermometerCorridorRoster.lift (entered D x U)
    ∀j,b≤j → ∀jf:j≤f,∃wallet:X→ℝ, (∀i,0<wallet i ∧ wallet i≤W i ∧
      (wallet i)⁻¹≤((A).clock.hatBeta f)^(6*(f-j))*(W i)⁻¹) ∧
      MenuBoard ((C).path.rep N p j) (fun _:X=>0) (gust (C).path N p f F j jf) (routes j) wallet
        (((A).budget j).supportExponent-2) 1:=by
  let W:X→ℝ:= (w ∘ Prod.fst) ∘ Prod.snd
  have wp(i:V×Bool):0<(w ∘ Prod.fst) i:=pos _
  have B:=WilsonOriginalGalleryTwinBoard.original D x w pos expo reg forced actual
  have law:=((R.T.sticks N p).prices f (Nat.zero_le _) fn).1.valid
  have T:=WilsonThermometerCorridorRoster.admit _ B law wp wp (fun _=>le_rfl)
  rw [←home] at T
  apply WilsonThermometerCorridorWalk.original (I:=V×Bool) R simple cater first fn
    (fun j _=>(0:Three G ((C).side j p))) routes (fun _ _=>0) W _ T (fun i=>pos _) same
  · intro j hj jf y
    exact Ride.vac
  · exact load
  · intros
    simp

end YM.Integration.WilsonOriginalGalleryTwinWalk
end
