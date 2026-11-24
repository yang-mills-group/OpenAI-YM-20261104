import YM.Integration.WilsonMarkedUltravioletReportingReserve
import YM.Integration.WilsonMarkedUltravioletMixedWallet
import YM.Integration.WilsonMixedTaggedWeightedReserve

/-! Recover both actual fine arrays at the exact reporting reserve D, retaining
the remaining income to unweight every lower represented array. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedCaptureEntries
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open RG05Readout RG05Readout.Many PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem spend {n:Side} {V I:Type} [DecidableEq V] [Fintype I] {J:Census V}
    {o:V → Site n} {S:I → Support n} {F:I → Config G n → Poly J} {w:V → ℝ} {B D:ℕ} {α t M:ℝ}
    (bank:Towed w S F B α 1) (wp:∀v,0 < w v) (mp:0 ≤ M)
    (sizes:∀s:J.Mode,1 ≤ M*Poly.toll w s) (scope:∀i,Borne o (S i) (F i) t)
    (occupied:∀i U,rises (F i U))
    (apart:∀s:J.Mode,2 ≤ s.val.card → ∃a∈s.val,∃b∈s.val,D*(4*B+2)+2*B < separation (o a) (o b)) :
    Towed (fun _:V=>(1:ℝ)) S F B (α-1) (M*Real.exp (-(D:ℝ))) := by
  have reach:=WilsonMarkedUltravioletMixedWallet.reach scope
    (fun i U s nz=>apart s (occupied i U s nz))
  simpa only [neg_one_mul,mul_one] using
    WilsonMarkedUltravioletMixedWallet.purchase bank wp (σ:=1) zero_le_one mp
      (fun _ _ s _=>sizes s) reach

/-- All-field identity for the very same physical H and K acquired at
the tuning date, with an explicit, common positive amplification. -/
theorem initial (R:Run G) {m N per d k h L D:ℕ} (mn:m ≤ N)
    (room:D*(4*(R.family.path.levels.budget m).B+2)+2*(R.family.path.levels.budget m).B ≤ 
      (R.family.path.levels.budget m).B^2) :
    let C:=R.family
    let P:=C.path.rep N per m
    let A:=C.path.levels
    let α:=(A.budget m).supportExponent
    let δ:=(A.clock.hatBeta m)^((k+h)*L)*Real.exp (-(D:ℝ))
    ∀ {V:Type} [DecidableEq V] [Fintype V] {J:Census V} (Q:V → ℝ)
      (o:V → Site (C.side m per)) (rows:V → RG05Readout.Address.Three G (C.side m per))
      (Z:Config G (C.side m per) → Poly J), (∀v,0 < Q v) → 
      (∀v,Q v ≤ (A.clock.hatBeta m)^h) → 
      MenuBoard P rows Z o (fun v=>envelope C m d k (Q v) m) α 1 → 
      (∀s:J.Mode,s.val.card ≤ L) → (∀s:J.Mode,2 ≤ s.val.card → ∃a∈s.val,∃b∈s.val,
       (A.budget m).B^2+1 ≤ separation (o a) (o b)) → 
      ∃ H K, Carton o H K P.p.threshold ∧ 
       Z=restore P (fun v=>(rows v).2.1) (fun v=>profile P.activities (rows v).2.2) H K ∧ 
       Towed (fun _:V=>(1:ℝ)) id H P.p.B (α-1) δ ∧ 
       Towed (fun _:V=>(1:ℝ)) (fun i:Box (C.side m per)=>i.1) K P.p.B (α-1) δ ∧ 
       Towed (fun v=>envelope C m d k (Q v) m) id H P.p.B (α-1) (Real.exp (-(D:ℝ))) ∧ 
       Towed (fun v=>envelope C m d k (Q v) m) (fun i:Box (C.side m per)=>i.1)
         K P.p.B (α-1) (Real.exp (-(D:ℝ))) := by
  intro C P A α δ V de fi J Q o rows Z qp qh bank cap dist
  let M:=(A.clock.hatBeta m)^((k+h)*L)
  let w:=fun v=>envelope C m d k (Q v) m
  have wp(v:V):0 < w v:=by
    unfold w envelope west
    rw [rust_above (le_refl m),one_mul]
    exact grantw (totalpos (qp v) m)
  have mp:0 ≤ M:=pow_nonneg (zero_lt_one.trans (A.fits.delayed m)).le _
  have fees(s:J.Mode):1 ≤ M*Poly.toll w s:=
    WilsonMarkedUltravioletReportingReserve.weights C m d k h L Q qp qh s (cap s)
  have eq : P.p=A.budget m := (R.T.choice.represents N per m mn).vac
  have apart(s:J.Mode)(two:2 ≤ s.val.card) :
      ∃a∈s.val,∃b∈s.val,D*(4*P.p.B+2)+2*P.p.B < separation (o a) (o b) := by
    obtain ⟨a,ha,b,hb,paid⟩:=dist s two
    refine ⟨a,ha,b,hb,?_⟩
    rw [eq]
    exact lt_of_le_of_lt room (Nat.lt_of_succ_le paid)
  obtain ⟨H,K,here,regular,forced,all⟩:=bank.grants
  refine ⟨H,K,here,all,
    spend regular wp mp fees (fun i=>(here.exp i).1.toBorne) (fun i=>(here.exp i).2) apart,
    spend forced wp mp fees (fun i=>(here.flag i).1.toBorne) (fun i=>(here.flag i).2) apart,?_,?_⟩
  · have span:=WilsonMarkedUltravioletMixedWallet.reach (fun i=>(here.exp i).1.toBorne)
      (fun i U s nz=>apart s ((here.exp i).2 U s nz))
    simpa only [mul_one] using WilsonMixedTaggedWeightedReserve.original regular wp span
  · have span:=WilsonMarkedUltravioletMixedWallet.reach (fun i=>(here.flag i).1.toBorne)
      (fun i U s nz=>apart s ((here.flag i).2 U s nz))
    simpa only [mul_one] using WilsonMixedTaggedWeightedReserve.original forced wp span

end YM.Integration.WilsonMixedTaggedCaptureEntries
