import YM.Integration.WilsonPositionProgramTrialPublicJointScalarCourse

/-! The full unperiodized measured scalar on the inherited cutoff, with its exact test address. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointScalarProjection
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{D k h:ℕ}{F:Frame G h}{T:SectionData F}{p:h<D}{H:Hol G}

open WilsonPositionProgramTrialPublicJointScalarCourse (seed scalar Given)
open WilsonIndependentMatchedFourUnitCourse (held)
def unitAt (i:Alma F):Alma F:=
  ⟨(0,notar F i),by rw [F.zero_degree];simpa only [Prod.fst,Prod.snd,Nat.zero_add,rankS] using (notar F i).property⟩

theorem printed (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k m j:ℕ)(before:m+j≤N)(four:4≤k)(enough:h≤k)(T:SectionData F)(fit:h<D)
    (sound:T.Sound H)(pop:Bid.pop T)(a i:Alma F)(lit:Cosmos.sheet F a=0):
    ∃c:ℝ,∀q,coeff q (opal F (spools A O' N k h m j (vein (starting T fit) a)) i)=
      c * lineS (1:Coil F) q i (unitAt i):=by
  let start:=starting T fit
  let P:=spools A O' N k h m j (vein start a)
  have health:Shimmer start:=freshly T H fit sound pop
  obtain ⟨Z,paid⟩:=WilsonPositionProgramTrialPublicJointScalarCourse.original A O' simple valid N k m j before four T fit sound pop a lit
  let X:=testa D (notar F i).val
  let c:=Z X
  refine ⟨c,?_⟩
  have one:crease X (knurl (notar F (unitAt i))) 0=1:=by
    change crease (testa D (notar F i).val) (knurl (notar F i)) 0=1
    rw [coinage,knurls,if_pos rfl]
  have hn (n:Side):jot (page D X) (P.1 n)=jot (page D X) (c • start.1 n (unitAt i)):=by
    rw [map_smul,seed (unitAt i) rfl X sound pop n,one,scalar,mul_one]
    exact paid n X
  have born:On k P:=spoolEnd before simple valid (hailed start health a ((valence_cap ..).trans enough))
  have covered:jot (page D X) P.2=jot (page D X) (c • start.2 (unitAt i)):=by
    funext z r
    have hu:=solo_bend born (page D X) z r
    have hs:=solo_bend ((hailed start health (unitAt i) (valence_cap ..)).μ (k:=h) c) (page D X) z r
    apply hu.exten
    exact hs.congr (Filter.Eventually.of_forall fun n=>congr_fun (congr_fun (hn n).symm z) r)
  have he z r:jot (brow F i D) P.2 z r=jot (brow F i D) (c • start.2 (unitAt i)) z r:=
    congr_fun (congr_fun covered z) r
  intro q
  rw [opal,coeff_mk,←health.era,coined,←smul_eq_mul,←glean_mu]
  change glean F P.2 q i=_
  unfold glean
  apply Finset.sum_congr rfl
  intro r _
  split
  · unfold echoS trellis arret
    simp_rw [←jot_here,he]
  · rfl

theorem original (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k m j:ℕ)(before:m+j≤N)(four:4≤k)(enough:h≤k)(T:SectionData F)(fit:h<D)
    (sound:T.Sound H)(pop:Bid.pop T)(a i:Alma F)(lit:Cosmos.sheet F a=0)
    (positive:Cosmos.sheet F i≠0):
    opal F (spools A O' N k h m j (vein (starting T fit) a)) i=0:=by
  obtain ⟨c,row⟩:=printed A O' simple valid N k m j before four enough T fit sound pop a i lit
  have ne:i≠unitAt i:=fun eq=>positive (congrArg (Cosmos.sheet F) eq)
  apply PowerSeries.ext
  intro q
  rw [map_zero,row q]
  simp [lineS,Matrix.one_apply,ne]

end YM.Integration.WilsonPositionProgramTrialPublicJointScalarProjection
