import YM.Integration.WilsonSeparatedPrefixCanonicalFlat
import YM.Integration.WilsonSeparatedPrefixCanonicalPolynomial
import YM.Integration.WilsonOriginalOccupiedSource
import YM.Integration.WilsonOriginalOccupiedTransport

/-! Signed withdrawal on the physical canonical law for a whole arbitrary finite original
inventory. Both regular mixed modes and all nonempty hard owners are tapped only at the top. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalHeard
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "X" => Unit×I
local notation "J" => Stock.census I

def roof (w:I → ℝ)(s:(J).Mode)(k j l:ℕ):ℝ:=
  let m:=Fintype.card X
  (25+24*((A).params j).columns)*(H j)^4*4*4^m*
    (((m:ℝ)*(H (k+1))^(4+6*l))^m*(H (k+1))^(6*(k+1-(j+2))*s.val.card)/Poly.toll w s)

theorem original (simple:G.Simple)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j+2≤k+1) (kn:k<N) (l n:ℕ)
      (o:I → Site ((C).side (k+1) p))(w:I → ℝ)(route:∀t,X → Site ((C).side t p))(anchor:X),
    let P:=(C).path.rep N p (k+1)
    ∀H₀ H₁:Support ((C).side (k+1) p) → Config G ((C).side (k+1) p) → Poly J,
    ∀K₀ K₁:Box ((C).side (k+1) p) → Config G ((C).side (k+1) p) → Poly J,
    let F:=WilsonSeparatedPrefixCanonicalPolynomial.source P H₀ H₁ K₀ K₁
    (∀Z U,(H₁ Z U).part (J).quiet=0) → (∀b U,(K₁ b U).part (J).quiet=0) →
    ∀T q:ℂ,T*q=1 → ‖q‖≤1 →
    (∀z∈nodes n T,Served P (fun (_:I) _=>0) (fun (_:I) _ _=>0) (F z) o w
      (((A).budget (k+1)).supportExponent-1) 1) →
    (∀i,0<w i) → route (k+1)=o ∘ Prod.snd →
    (∀t,j+1≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p →
    ∀s:(J).Mode,s.val.card≤n →
      ‖(amount R (N:=N) (F 1) (uj.trans (by omega))).part s-
       (amount R (N:=N) (F 0) (uj.trans (by omega))).part s‖ ≤
        ‖q‖*WilsonOriginalOccupiedStencil.price n*roof R w s k j l := by
  filter_upwards [WilsonSeparatedPrefixCanonicalFlat.original (I:=I) R simple cater bank wage,
    (A).fits.deep.eventually_ge_atTop (Fintype.card I)] with j pay enough
  intro N p k height kn l n o w route anchor P H₀ H₁ K₀ K₁ F zh zk T q inverse small served wp home parent close fixed u ref uj ou oj s size
  have occ:Occupancy o (apron (A) k):=WilsonSeparatedPrefixCanonicalFlat.occupancy R
    ((enough.trans ((A).fits.mono (by omega:j≤k+1))).trans (Nat.le_add_right _ _)) _
  have integr z (h:z∈nodes n T):Integrable (F z) (prior G _):=
    (WilsonSeparatedPrefixCanonicalWalk.board R cater kn wp occ (served z h)).1
  have atNode(i:Fin (n+1)):T*node i∈nodes n T:=by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact mem_image_of_mem _ (mem_univ i)
  let Jn:=fun i:Fin (n+1)=>T*node i
  have same:=WilsonOriginalOccupiedTransport.original R (N:=N) (F 1) (F 0) (fun i=>F (Jn i)) (WilsonOriginalOccupiedStencil.weight q)
    s (uj.trans (by omega)) (integr 1 (by simp [nodes])) (integr 0 (by simp [nodes]))
    (fun i=>integr _ (atNode i))
    (WilsonSeparatedPrefixCanonicalPolynomial.taps P H₀ H₁ K₀ K₁ zh zk s n size T q inverse) 1
  let Y:=fun z:ℂ=>(amount R (N:=N) (F z) (uj.trans (by omega))).part s
  have response:Y 1-Y 0=∑i:Fin (n+1),WilsonOriginalOccupiedStencil.weight q i*Y (Jn i):=by
    dsimp only [Y,WilsonOriginalCompanionLinearFiling.amount]
    simp only [Poly.part_smul]
    rw [←mul_sub,same,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have bill(i:Fin (n+1)):‖Y (Jn i)‖≤roof R w s k j l:=pay N p k height kn l o (F (Jn i)) w route anchor
    wp home parent (served _ (atNode i)) close fixed u ref uj ou oj s
  have cash:0≤roof R w s k j l:=(norm_nonneg _).trans (bill 0)
  change ‖Y 1-Y 0‖≤_
  rw [response]
  calc _ ≤ ∑i,‖WilsonOriginalOccupiedStencil.weight q i*Y (Jn i)‖ := norm_sum_le ..
       _ ≤ ∑i,‖WilsonOriginalOccupiedStencil.weight q i‖*roof R w s k j l:=Finset.sum_le_sum (fun i _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (bill i) (norm_nonneg _))
       _ = (∑i,‖WilsonOriginalOccupiedStencil.weight q i‖)*roof R w s k j l:=(sum_mul ..).symm
       _ ≤ _:=mul_le_mul_of_nonneg_right (earned n q small) cash

end YM.Integration.WilsonSeparatedPrefixCanonicalHeard
end
