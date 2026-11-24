import YM.Integration.WilsonSeparatedPrefixMovingLaterJoin

/-! Finish the no-crossing branch on this same normalized older law. The
full ordinary product still contains the product of the conditional means. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingUnjoined
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}

private theorem own {δ:ℝ}(Q:SealR G)(X:Q.Rider)(e:ℕ)(hd:0≤δ):
    0≤WilsonSeparatedPrefixMovingOwnDate.fee Q e X ∧
    Terms e Q (WilsonSeparatedPrefixMovingOwnDate.fee Q e X) δ X X:=by
  refine ⟨Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _,?_⟩
  intro j hj v
  apply twain.one _ _ hd
  exact (Finset.single_le_sum (f:=fun n:Fin (e+1)=>‖coeff n.val (X v)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ (⟨j,by omega⟩:Fin (e+1)))).trans
    (Finset.single_le_sum (f:=fun v:Alma Q.F=>∑n:Fin (e+1),‖coeff n.val (X v)‖)
      (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ v))

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(Q:SealR G)(v:Rails h k u e)
    (E W K U V L:Credit):
    ∃C₀ C₁:Credit,∀Y:CutsP H T p v E W K U,let R:=Y.vesselsC
      ∀(_far:PassportC H R Q W V),Dormitory R (k+Q.h) u L →
      ∀z≤Y.i,let t:=Y.m+z
      ∀ older (η:ℕ→ℝ)(Z Z₁:ℝ),Escort R older t η → η t=1 → PadRank R older t Z →
      Compar R.draws.S R.y t t≤Z₁ → ∀(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y Bφ Bψ:ℝ)(o:CellR),
      ψ.radius≤Z₁ → |y|≤Z₁ → Amplitude φ Bφ → Amplitude ψ Bψ →
      let ratio:=paceT R.draws.S t Y.ceilC
      let near:=word (ratio^h • Y.springP z) φ 1 y o h
      let far:=locale o (Q.spins R.draws R.paid ψ t t Y.N y X)
      let arrived:=cruises R.draws R.paid Y.N (k+Q.h) t older (agateV near far)
      let nearFee:=BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^u*(Bφ*WilsonIndependentMatchedCoverProfile.price Y C₀ z 1))
      let farFee:=(hardCash e u E W V H Q).buy Z₁*(Bψ*WilsonSeparatedPrefixMovingOwnDate.fee Q e X)
      let salary:=ratio^h*(C₁.buy Z*(coinMat (k+Q.h) e*nearFee*farFee))
      Flush e u (η older) arrived salary ∧ ∀grade≤e,∀ω:Fin 0→YForest G,
        ‖arrived.2 grade 0 ω‖≤salary:=by
  obtain ⟨C₀,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  obtain ⟨C₁,olderPay⟩:=waveSeen G (k+Q.h) e u E L
  refine ⟨C₀,C₁,?_⟩
  intro Y R outer dorm z hz t older η Z Z₁ route endScale room clock φ ψ X y Bφ Bψ o
    radius shift nearPrice farPrice ratio near far arrived nearFee farFee salary
  let δ:=max 0 (R.tempC t t)
  have hd:0≤δ:=le_max_left ..
  have closed:t≤Y.N:= (Nat.add_le_add_left hz Y.m).trans (Y.hc.trans Y.hn)
  have live:R.anchor≤t:=Y.ha.trans (Nat.le_add_right ..)
  have hp:=own Q X e hd
  have keepFar:Fringed Q.h e u 1 farFee δ far far:=by
    have co:= (capLife outer live le_rfl le_rfl closed closed clock hp.1 (le_max_right _ _) X X hp.2
      ψ radius u o shift farPrice).1
    simpa only [pace_self,one_pow,inv_one,mul_one] using co
  let word₀:=ratio^h • Y.springP z
  let wage:=WilsonIndependentMatchedCoverProfile.price Y C₀ z (ratio^h)
  have acts:= (Y.onward hz).μ (ratio^h)
  have emit:∀j≤e,∀r, YieldP 0 1 u wage δ (word₀.2 j r) (word₀.2 j r):=
    fun j hj r=>YieldP.same (((paid Y).2.2 j hj z hz r).μ (ratio^h)) hd
  have nearPay:= census_br word₀ word₀ φ 1 y acts acts o u zero_lt_one le_rfl nearPrice emit hd h
  have cash:BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^u*(Bφ*wage))=ratio^h*nearFee:=by
    dsimp only [wage,nearFee,WilsonIndependentMatchedCoverProfile.price]
    rw [abs_of_pos (pow_pos (pace_pos ..) _),abs_one]
    ring
  rw [cash] at nearPay
  have nearEnd:Fringed k e u 1 (ratio^h*nearFee) δ near near:=nearPay
  let fee:=coinMat (k+Q.h) e*(ratio^h*nearFee)*farFee
  have combined:Fringed (k+Q.h) e u (η t) fee δ (agateV near far) (agateV near far):=by
    rw [endScale];exact fringedMat nearEnd keepFar zero_le_one (le_refl (k+Q.h))
  have arrival:Flush e u (η older) arrived (C₁.buy Z*fee):=(olderPay R dorm older t η t Y.N Y.N _ δ Z route room le_rfl closed closed
    (le_max_right _ _) _ _ combined).f_l
  have equation:C₁.buy Z*(coinMat (k+Q.h) e*(ratio^h*nearFee)*farFee)=salary:=by dsimp only [salary];ring
  change C₁.buy Z*fee=salary at equation
  rw [equation] at arrival
  exact ⟨arrival,fun j hj i=>WilsonIndependentMatchedCoverJoined.unit arrival j hj i⟩

end YM.Integration.WilsonSeparatedPrefixMovingUnjoined
