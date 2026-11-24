import YM.Integration.WilsonPublicForkSelected
import YM.Integration.WilsonPublicForkDirections

/-! A selected finite family of literal physical inputs and the full measured
output, in the original order, on the matrix ticket of the original extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkMixed
open Function Finset Filter Set Table Spec Climb OPE OPE.Orbits OPE.Prescription OPE.Log EveryPhase OPE.Nesting
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open Next.UVStress Trace.Terrace WilsonPublicForkLabels WilsonThermometerWeakPairClock
open YM.Integration.WilsonLimitConstruction
open scoped Classical Topology BigOperators
universe u
variable {I:Type} [Fintype I] {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}
  {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)

theorem original {simple:G.Simple}{κ:ℝ}(fund:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(done':Completed F L)(fac:Facilities R.family f S)
    {𝓛:Ultrafilter (ℕ×ℕ)}{arc:Arch R.family}{Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arc Y)(ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(book:Foundation F Q)
    (J:ℝ → tower S)(V:Store G)(lead:Leading F J)(g:ℝ → ℝ)(hg:Coupling G g)
    (d:I → ℕ)(e h:ℕ){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(E:ℕ)(C:ℝ),0≤C ∧ ∀B:ℕ,∀ᶠ r in trail,let t:=scale g B r
      ∀(x:I → E4)(z:E4),(∀i,‖x i‖≤M) → ‖z‖≤M → 2*δ≤‖z‖ → (∀i j,i≠j → δ≤‖x i-x j‖) → r*M≤t*δ →
      Injective (beside (fun i=>r • x i) (sole (t • z))) → Injective (beside (sole (0:E4)) (sole (t • z))) →
      ∀(v:∀i,Free R.family (d i))(w:Free R.family e),
      let u:=fun i=>J r (d i) (v i)
      ‖defect e h (fun i=>r • x i) u (Q.packet h (fun i=>r • x i) u 0) (t • z) (J t e w)‖≤
        C*(∏i,‖v i‖)*‖w‖*((r/t)^(h+1)/(g r)^E):=by
  let A:=fun i=>Fin (Module.finrank ℂ (Free R.family (d i)))
  let b:=fun i=>Module.finBasis ℂ (Free R.family (d i))
  let b₀:=Module.finBasis ℂ (Free R.family e)
  let u: (∀i,A i) → ∀i,Free R.family (d i):=fun j i=>b i (j i)
  choose D C pos paid using fun (j:∀i,A i) k=>WilsonPublicForkSelected.original F fund L done' fac bliss ticket Q book J V lead g hg d e h (u j) (b₀ k) mn dp
  let E:=∑j,∑k,D j k
  let T:=fun j=>∑k,‖(b₀.coord k).toContinuousLinearMap‖*C j k
  let N:=∑j:∀i,A i,(∏i,‖((b i).coord (j i)).toContinuousLinearMap‖)*T j
  have posT(j):0≤T j:=Finset.sum_nonneg fun k _=>mul_nonneg (norm_nonneg ((b₀.coord k).toContinuousLinearMap)) (pos j k)
  have posN:0≤N:=Finset.sum_nonneg fun j _=>mul_nonneg (Finset.prod_nonneg fun i _=>norm_nonneg (((b i).coord (j i)).toContinuousLinearMap)) (posT j)
  refine ⟨E,N,posN,fun B=>?_⟩
  have all:=eventually_all.mpr (fun j=>eventually_all.mpr (fun k=>paid j k B))
  filter_upwards [all,hg.positive,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin]
    with r tab gp g1 (rp:0<r)
  let t:=scale g B r
  have tp:0<t:=div_pos rp (pow_pos gp _)
  let fee:=(r/t)^(h+1)/(g r)^E
  dsimp only;intro x z hx hz sz sep wide inner outer v w
  let X:=fun i=>r • x i
  let near (a:∀i,Free R.family (d i)):=fun i=>J r (d i) (a i)
  let op:MultilinearMap ℂ (fun i=>Free R.family (d i)) ℂ:=
    (forms F Q e h X (t • z) (J t e w)).compLinearMap fun i=>(J r (d i)).toLinearMap
  have act(a:∀i,Free R.family (d i)):op a=defect e h X (near a) (Q.packet h X (near a) 0) (t • z) (J t e w):=
    WilsonPublicForkLabels.actual F Q _ _ _ _ inner outer
  change ‖defect e h X (near v) (Q.packet h X (near v) 0) (t • z) (J t e w)‖ ≤ _
  rw [←act]
  have cb(j:∀i,A i):‖op (u j)‖≤T j*(‖w‖*fee):=by
    rw [act];let Φ:Free R.family e →ₗ[ℂ] ℂ:=
      (defect e h X (near (u j)) (Q.packet h X (near (u j)) 0) (t • z)).comp (J t e).toLinearMap
    change ‖Φ w‖≤_
    apply (WilsonPublicForkDirections.one b₀ Φ w (C j) fee ?_).trans_eq (by ring)
    intro k
    have dj:(D j k)≤E:=le_trans (Finset.single_le_sum (f:=D j) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k))
      (Finset.single_le_sum (f:=fun p=>∑a,D p a) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j))
    have grow:C j k/(g r)^(D j k)≤C j k/(g r)^E:=div_le_div_of_nonneg_left (pos j k) (pow_pos gp _) (pow_le_pow_of_le_one gp.le g1 dj)
    exact ((tab j k x z hx hz sz sep wide inner outer).trans (mul_le_mul_of_nonneg_right grow
      (pow_nonneg (div_nonneg rp.le tp.le) _))).trans_eq (by dsimp [fee];ring)
  exact (WilsonPublicForkDirections.many b op v T (‖w‖*fee) cb).trans_eq (by change N*_*(‖w‖*fee)=_;ring)
end YM.Integration.WilsonPublicForkMixed
