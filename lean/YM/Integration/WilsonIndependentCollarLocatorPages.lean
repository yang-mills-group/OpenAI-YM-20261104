import YM.Integration.WilsonIndependentCollarIssuedCopies

/-! Keep the true relative-front weight of every paid page when summing the
actual lamp array. The radial address and its original Ink are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarLocatorPages
open Function Finset Lattice Laurent RG Wilson Precision Push Push.AbsoluteSums Push.Local
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Address FundedMarkedPathSelection OriginalIssuedMarkedRows
open WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedRoll WilsonOlderFreshConnectedLamp
open scoped Classical BigOperators
variable {G:Gauge}{n e m:ℕ}{D k:Fin n→ℕ}{S J:Finset (Fin n)}{A:ℝ}
  (V:Realm G (e+1) Credit.leanC)(hm:V.anchor ≤ m)(X:Input V hm S k D A)
  (c:Fin n)(l N:ℕ)(o:Cover)(v:Case D)

theorem original (j:ℕ){M w:ℝ}(issued:∀r:Fin (l+j+1),Rooted V hm X J c l N w M o j r):
    SumBudget (fun z:Page (G:=G) J c l j=>
      Real.exp (w*feeH (toe J c o z.2.1.1) c J)*((roll V hm X J c l N o v j).leg z).money w)
      (cost J l j v M):=by
  let B:=∏i∈J,‖v i‖
  have b0:0≤B:=prod_nonneg fun i _=>norm_nonneg _
  apply sumBudget_sigma (a:=fun _:Fin (l+j+1)=>B*M)
  · intro r
    obtain ⟨μ,born,_,raw,_⟩:=issued r
    let W:=packet V hm X J c l N o j r
    let Z:=fun x:Words (G:=G) J c r.val=>Real.exp (w*feeH (toe J c o x.1) c J)
    let P:=fun x:Words (G:=G) J c r.val=>Z x*lease (W x) (μ x) w
    have bought:SumBudget P M:=raw
    apply sumBudget_sigma (a:=fun x:Words (G:=G) J c r.val=>B*P x)
    · intro x
      change SumBudget (fun a=>Z x*(lamp (W x) v a).money w) (B*P x)
      refine ⟨fun a=>mul_nonneg (Real.exp_pos _).le ((lamp (W x) v a).fee_nn w),(hasSum_fintype _).summable,?_⟩
      rw [tsum_fintype,←Finset.mul_sum]
      have score:=WilsonOlderFreshConnectedLamp.paid (W x) v (μ x) (born x) w
      exact (mul_le_mul_of_nonneg_left score (Real.exp_pos _).le).trans_eq (by dsimp [P,B,Z]; ring)
    · exact sumBudget_mul_left bought b0
  · have hM:0≤M:=by
      obtain ⟨_,_,_,h,_⟩:=issued ⟨0,by omega⟩
      exact (tsum_nonneg h.1).trans h.2.2
    refine ⟨fun _=>mul_nonneg b0 hM,(hasSum_fintype _).summable,?_⟩
    rw [tsum_fintype]
    simp only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul]
    rfl

end YM.Integration.WilsonIndependentCollarLocatorPages
end
