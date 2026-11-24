import YM.Integration.WilsonSeparatedPrefixCanonicalHeard
import YM.Integration.WilsonSeparatedPrefixCanonicalClearPost

/-! Signed withdrawal of the original nonquiet portfolio on a genuine earlier clear field. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearHeard
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

def held {f b N p:ℕ}{J₁:Census I}(F:Config G ((C).side f p)→Poly J₁)(bf:b≤f)
    (U:Config G ((C).side b p)):Poly J₁:=
  (((C).path.rep N p b).eval U:ℂ)⁻¹ • gust (C).path N p f F b bf U

def roof (w:I→ℝ)(s:(J).Mode)(f b:ℕ):ℝ:=
  WilsonSeparatedPrefixCanonicalClearPost.fare I*(H f)^(6*(f-b)*s.val.card)/Poly.toll w s

theorem original (simple:G.Simple)(cater:Cater (C) R.doors):
    ∀ᶠ b:ℕ in atTop,∀N p k (bk:b≤k+1) (_kn:k<N) (n:ℕ)
      (o:I → Site ((C).side (k+1) p))(w:I → ℝ)(route:∀t,X → Site ((C).side t p)),
    let P:=(C).path.rep N p (k+1)
    ∀H₀ H₁:Support ((C).side (k+1) p) → Config G ((C).side (k+1) p) → Poly J,
    ∀K₀ K₁:Box ((C).side (k+1) p) → Config G ((C).side (k+1) p) → Poly J,
    let F:=WilsonSeparatedPrefixCanonicalPolynomial.source P H₀ H₁ K₀ K₁
    (∀Z U,(H₁ Z U).part (J).quiet=0) → (∀h U,(K₁ h U).part (J).quiet=0) →
    ∀T q:ℂ,T*q=1 → ‖q‖≤1 →
    (∀z∈nodes n T,Served P (fun (_:I) _=>0) (fun (_:I) _ _=>0) (F z) o w
      (((A).budget (k+1)).supportExponent-1) 1) →
    (∀i,0<w i) → route (k+1)=o ∘ Prod.snd →
    (∀t,b≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    2≤((A).budget b).supportExponent → ∀U:Config G ((C).side b p),
    flags ((C).path.rep N p b).p.threshold U=∅ → ∀s:(J).Mode,s.val.card≤n →
      ‖(held R (N:=N) (F 1) bk U).part s-(held R (N:=N) (F 0) bk U).part s‖≤
        ‖q‖*WilsonOriginalOccupiedStencil.price n*roof R w s (k+1) b:=by
  filter_upwards [WilsonSeparatedPrefixCanonicalClearPost.original (I:=I) R simple cater,
    (A).fits.deep.eventually_ge_atTop (Fintype.card I)] with b pay enough
  intro N p k bk kn n o w route P H₀ H₁ K₀ K₁ F zh zk T q inverse small served wp home parent alpha U clear s size
  have occ:Occupancy o (apron (A) k):=WilsonSeparatedPrefixCanonicalFlat.occupancy R
    ((enough.trans ((A).fits.mono bk)).trans (Nat.le_add_right _ _)) _
  have integr z (h:z∈nodes n T):Integrable (F z) (prior G _):=
    (WilsonSeparatedPrefixCanonicalWalk.board R cater kn wp occ (served z h)).1
  have atNode(i:Fin (n+1)):T*node i∈nodes n T:=by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact mem_image_of_mem _ (mem_univ i)
  let Jn:=fun i:Fin (n+1)=>T*node i
  have same:=WilsonOriginalOccupiedTransport.original R (N:=N) (F 1) (F 0) (fun i=>F (Jn i)) (WilsonOriginalOccupiedStencil.weight q)
    s bk (integr 1 (by simp [nodes])) (integr 0 (by simp [nodes]))
    (fun i=>integr _ (atNode i))
    (WilsonSeparatedPrefixCanonicalPolynomial.taps P H₀ H₁ K₀ K₁ zh zk s n size T q inverse) U
  let Y:=fun z:ℂ=>(held R (N:=N) (F z) bk U).part s
  have response:Y 1-Y 0=∑i:Fin (n+1),WilsonOriginalOccupiedStencil.weight q i*Y (Jn i):=by
    dsimp only [Y,held]
    simp only [Poly.part_smul]
    rw [←mul_sub,same,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have bill(i:Fin (n+1)):‖Y (Jn i)‖≤roof R w s (k+1) b:=by
    have sold:=pay N p k bk kn o w (F (Jn i)) route wp home parent (served _ (atNode i)) alpha U clear s
    have visit:=congrFun (WilsonOriginalOccupiedTransport.projected R (N:=N) (F (Jn i)) (integr _ (atNode i)) s bk) U
    dsimp only [Y,held]
    rw [Poly.part_smul]
    change ‖_*(gust (C).path N p (k+1) (F (Jn i)) b bk U).part s‖≤_
    rw [visit]
    exact sold
  have cash:0≤roof R w s (k+1) b:=(norm_nonneg _).trans (bill 0)
  change ‖Y 1-Y 0‖≤_
  rw [response]
  calc _ ≤ ∑i,‖WilsonOriginalOccupiedStencil.weight q i*Y (Jn i)‖ := norm_sum_le ..
       _ ≤ ∑i,‖WilsonOriginalOccupiedStencil.weight q i‖*roof R w s (k+1) b:=Finset.sum_le_sum (fun i _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (bill i) (norm_nonneg _))
       _ = (∑i,‖WilsonOriginalOccupiedStencil.weight q i‖)*roof R w s (k+1) b:=(sum_mul ..).symm
       _ ≤ _:=mul_le_mul_of_nonneg_right (earned n q small) cash

end YM.Integration.WilsonSeparatedPrefixCanonicalClearHeard
end
