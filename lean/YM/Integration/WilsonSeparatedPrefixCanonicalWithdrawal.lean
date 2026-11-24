import YM.Integration.WilsonSeparatedPrefixCanonicalConvolution

/-! A before-cutoff, arbitrary-roster receipt on the authentic canonical carrier. The
left side is the complete original submitted ordinary face minus the masked peer product,
with every old quiet and all admissible occupied owners in the physical numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalWithdrawal
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

theorem original (simple:G.Simple)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j+2≤k+1) (kn:k<N) (l:ℕ)
      (o:V → Site ((C).side (k+1) p))(w₀ w:V → ℝ)(route:∀t,X → Site ((C).side t p))(anchor:X),
    let P:=(C).path.rep N p (k+1)
    let e:=((A).budget (k+1)).supportExponent-1
    let n:=Fintype.card V₂
    let W:=w ∘ Prod.fst (β:=Bool)
    ∀(φ:V → Config G ((C).side (k+1) p) → ℂ)(h:V → Box ((C).side (k+1) p) → Config G ((C).side (k+1) p) → ℂ)
      (F:Config G ((C).side (k+1) p) → Poly S₀)
      (M:V → Support ((C).side (k+1) p) → Config G ((C).side (k+1) p) → Poly S₀)
      (c:V → Poly S₀)(m r cap:V → ℝ) (T q:ℂ),
    Served P φ h F o w₀ (e+1) 1 →
    (∀v,0<w₀ v) → (∀v,0<w v) → (∀v,w v^2≤w₀ v) → 5≤P.p.B →
    (∀a b:V,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    (∀v Z,Burns o Z (M v Z) P.p.threshold) →
    (∀v b,Flow o b (fun U=>Poly.send ((S₀).fire v) (h v b U)) P.p.threshold) →
    (∀v,Towed (fun i=>w i^2) id (M v) P.p.B e (m v)) →
    (∀v,Towed (fun i=>w i^2) Prod.fst (fun b U=>Poly.send ((S₀).fire v) (h v b U)) P.p.B e (r v)) →
    (∑v,m v)+1/4≤1 → (∀v,(c v).part (S₀).quiet=0) →
    (∀v,Poly.price (fun i=>w i^2) (c v)≤cap v) →
    (∀v U,Poly.send ((S₀).fire v) (φ v U)=c v+∑Z,M v Z U) →
    T*q=1 → ‖q‖≤1 →
    (∀z∈nodes n T,4*‖z‖≤Real.exp ((P.p.B/8:ℕ):ℝ) ∧ (∑v,‖z‖*r v)+1/4≤1) →
    (∃a b:ℝ,P.activities.Valid P.p a b) →
    route (k+1)=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j+1≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p → ∀s:(S₀).Mode,
    Poly.toll (fun i=>w i^2) s*
      ‖reading R (N:=N) (fun U=>(F U).part s) u (uj.trans (by omega))-
       reading R (N:=N) (fun U=>(P.eval U:ℂ)*(∏v∈s.val,φ v U)) u (uj.trans (by omega))‖≤
      Real.exp (∑v,cap v)*(‖q‖*WilsonOriginalOccupiedStencil.price n)*
      (∑t:(S₂).Mode,Poly.toll W t*WilsonSeparatedPrefixCanonicalHeard.roof R W t k j l) := by
  filter_upwards [WilsonSeparatedPrefixCanonicalHeard.original (I:=V₂) R simple cater bank wage,
    (A).fits.deep.eventually_ge_atTop (Fintype.card V₂)] with j signed enough
  intro N p k height kn l o w₀ w route anchor P e n W φ h F M c m r cap T q stock positive wp within wide apart loc flag wages keys soft cq caps split inverse small paid valid home parent close fixed u ref uj ou oj s
  obtain ⟨a,b,genuine⟩:=valid
  obtain ⟨H,K,cart,upper,zeroH,zeroK,issue⟩:=WilsonSeparatedPrefixCanonicalTapBook.original P o φ h F w₀ w e 1 M m r
    stock wp positive within (by norm_num) wide apart loc flag wages keys soft
  let L:=WilsonSeparatedPrefixCanonicalDifference.test P h H K M
  have issued(z:ℂ)(hz:z∈nodes n T):Served P (fun (_:V₂) _=>0) (fun (_:V₂) _ _=>0) (L z) (o∘Prod.fst) W e 1:=
    issue z (by simpa only [one_mul] using (paid z hz).1) (paid z hz).2
  have pieces(U):=WilsonSeparatedPrefixCanonicalDifference.original P φ h H K c M genuine
    (fun Z U=>hop _ _ ((cart.exp Z).2 U)) cq (fun v Z U=>(loc v Z).sil U) split U
  let ζ:=Poly.pass (∑v,c v)
  have top(U):(F U).part s=(duplicate V ζ*L 1 U).part (two s):=by rw [upper,←(pieces U).1,seal_part]
  have bottom(U):(P.eval U:ℂ)*(∏v∈s.val,φ v U)=(duplicate V ζ*L 0 U).part (two s):=by
    rw [←(pieces U).2,seal_part,WilsonSeparatedPrefixCanonicalDifference.masked_part]
  have wpos(x:V₂):0<W x:=wp x.1
  have occ:Occupancy (o∘Prod.fst (β:=Bool)) (apron (A) k):=WilsonSeparatedPrefixCanonicalFlat.occupancy R
    ((enough.trans ((A).fits.mono (by omega:j≤k+1))).trans (Nat.le_add_right _ _)) _
  have integr z (hz:z∈nodes n T):Integrable (L z) (prior G _):=
    (WilsonSeparatedPrefixCanonicalWalk.board R cater kn wpos occ (issued z hz)).1
  let fee:=fun t:(S₂).Mode=>‖q‖*WilsonOriginalOccupiedStencil.price n*WilsonSeparatedPrefixCanonicalHeard.roof R W t k j l
  have rate(t:(S₂).Mode):‖(amount R (N:=N) (L 1) (uj.trans (by omega))).part t-
    (amount R (N:=N) (L 0) (uj.trans (by omega))).part t‖≤fee t:=
    signed N p k height kn l n (o∘Prod.fst) W route anchor
      (fun Z U=>WilsonSeparatedPrefixCanonicalTapBook.reg M U Z) (fun Z U=>duplicate V (H Z U)) 0
      (WilsonSeparatedPrefixCanonicalTapBook.hard h K) zeroH zeroK T q inverse small issued wpos home parent close fixed u ref uj ou oj t (card_le_univ _)
  have compare:=WilsonSeparatedPrefixCanonicalConvolution.original R w wp ζ (L 1) (L 0) _ _ s
    (integr 1 (by simp [nodes])) (integr 0 (by simp [nodes])) top bottom (uj.trans (by omega)) fee rate
  have square(i):0<w i^2:=sq_pos_of_pos (wp i)
  have gross:Poly.price (fun i=>w i^2) ζ≤Real.exp (∑v,cap v):=(Poly.pass_budget square _).trans
    (Real.exp_le_exp.mpr ((Poly.batch square univ c).trans (Finset.sum_le_sum (fun v _=>caps v))))
  let B:=∑t:(S₂).Mode,Poly.toll W t*fee t
  have bn:0≤B:=Finset.sum_nonneg (fun t _=>mul_nonneg (Poly.worth wpos t).le ((norm_nonneg _).trans (rate t)))
  refine compare.trans ((mul_le_mul_of_nonneg_right gross bn).trans_eq ?_)
  have scaled:(∑t,Poly.toll W t*fee t)=(‖q‖*WilsonOriginalOccupiedStencil.price n)*
      (∑t:(S₂).Mode,Poly.toll W t*WilsonSeparatedPrefixCanonicalHeard.roof R W t k j l):=by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _=>by dsimp [fee];ring)
  change Real.exp (∑v,cap v)*(∑t,Poly.toll W t*fee t)=_
  simp only [scaled,mul_assoc]

end YM.Integration.WilsonSeparatedPrefixCanonicalWithdrawal
end
