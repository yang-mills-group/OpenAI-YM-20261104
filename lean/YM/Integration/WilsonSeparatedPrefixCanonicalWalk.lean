import YM.Integration.WilsonOriginalGalleryTwinWalk
import YM.Integration.WilsonAllDateHarvestEndpointIntegrability

/-! The original zero-ride corridor on a canonical numerical tap. The valuation can be any
finite original census, including one formed by duplicating the labels on the same forced keys. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalWalk
open Filter Finset Lattice Wilson RG Ac Marker Push QuadraticLocal MergeProof MergeProof.Accent MeasureTheory
open RG05Readout.Many RG05Readout.Address RG05Readout.Pantry Lodestar Extra.Multi Extra.Trajectories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Lotus
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "J" => Stock.census I

theorem board (cater:Cater (C) R.doors){k N p:ℕ}(kn:k<N)
    {o:I → Site ((C).side (k+1) p)} {w:I → ℝ} (wp:∀i,0<w i)
    {F:Config G ((C).side (k+1) p) → Poly J} (occupied:Occupancy o (apron (A) k))
    (served:Served ((C).path.rep N p (k+1)) (fun (_:I) _=>0) (fun (_:I) _ _=>0) F o w
      (((A).budget (k+1)).supportExponent-1) 1):
    MenuBoard ((C).path.rep N p (k+1)) (fun _:I=>0) F o w (((A).budget (k+1)).supportExponent-2) 1 := by
  let P:=(C).path.rep N p (k+1)
  let raw:I → Three G ((C).side (k+1) p):=0
  have issued:Served P (fun i=>(raw i).2.1) (fun i=>profile P.activities (raw i).2.2)
      F o w (((A).budget (k+1)).supportExponent-1) 1 := by
    have none:(fun i=>profile P.activities (raw i).2.2)=fun (_:I) _ _=>0:=by
      ext i b U
      simp [raw,profile,cram]
    rw [none]
    exact served
  obtain ⟨_,_,course,_⟩:=cater.tiers k N p kn
  have bought:=WilsonAllDateHarvestEndpointIntegrability.original (I:=raw)
    (Q:=fun _:I=>0) (l:=fun _=>0) course R.makes.wilson kn wp (fun _=>Ride.vac)
    occupied (by intros; simp) issued
  rcases bought with ⟨integr,single,H,K,c,regular,hard,eq⟩
  exact ⟨integr,single,H,K,c,regular.shrink (by linarith) le_rfl wp,
      hard.shrink (by linarith) le_rfl wp,eq⟩

theorem original (simple:G.Simple)(cater:Cater (C) R.doors){b k N p:ℕ}(first:0<b)(kn:k<N)
    {o:I → Site ((C).side (k+1) p)} {w:I → ℝ}(wp:∀i,0<w i)
    {F:Config G ((C).side (k+1) p) → Poly J} (occupied:Occupancy o (apron (A) k))
    (served:Served ((C).path.rep N p (k+1)) (fun (_:I) _=>0) (fun (_:I) _ _=>0) F o w
      (((A).budget (k+1)).supportExponent-1) 1)
    (routes:∀j,Unit×I → Site ((C).side j p))(home:routes (k+1)=o ∘ Prod.snd)
    (same:∀j,b≤j → j<k+1 → routes j=((A).clock.op j p).ratio.parent ∘ routes (j+1))
    (load:∀j,b≤j → j<k+1 → Occupancy (routes (j+1)) (apron (A) j) ∧ Occupancy (routes j) (apron (A) j)):
    let W:Unit×I → ℝ:=w ∘ Prod.snd
    let X:=fun U=>WilsonThermometerCorridorRoster.lift (F U)
    ∀j,b≤j → ∀jf:j≤k+1,∃wallet:Unit×I → ℝ, (∀i,0<wallet i ∧ wallet i≤W i ∧
      (wallet i)⁻¹≤((A).clock.hatBeta (k+1))^(6*(k+1-j))*(W i)⁻¹) ∧
      MenuBoard ((C).path.rep N p j) (fun (_:Unit×I)=>0) (gust (C).path N p (k+1) X j jf)
         (routes j) wallet (((A).budget j).supportExponent-2) 1:=by
  let sale:=board R cater kn wp occupied served
  have law:=((R.T.sticks N p).prices (k+1) (Nat.zero_le _) kn).1.valid
  have lifted:=WilsonThermometerCorridorRoster.admit _ sale law wp wp (fun _=>le_rfl)
  rw [←home] at lifted
  apply WilsonThermometerCorridorWalk.original (I:=I) R simple cater first kn
    (fun j _=>(0:Three G ((C).side j p))) routes (fun _ _=>0) (w ∘ Prod.snd) _ lifted (fun i=>wp _) same
  · intros
    exact Ride.vac
  · exact load
  · intros
    simp

end YM.Integration.WilsonSeparatedPrefixCanonicalWalk
end
