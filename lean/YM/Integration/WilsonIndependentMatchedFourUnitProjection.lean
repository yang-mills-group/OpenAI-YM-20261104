import YM.Integration.WilsonIndependentMatchedFourUnitCourse

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedFourUnitProjection
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{D k:ℕ}{F:Frame G 4}{T:SectionData F}{p:4<D}{H:Hol G}

open WilsonIndependentMatchedFourUnitCourse
variable {e m N:ℕ}{E W:Credit}

/-- The actual unit address with the same complete multiset of test derivatives. -/
def unitAt (i:Alma F):Alma F:=
  ⟨(0,notar F i),by rw [F.zero_degree];simpa only [Prod.fst,Prod.snd,Nat.zero_add,rankS] using (notar F i).property⟩

theorem solo (L:Theatre H T p e E W)(live:m≤N)(i:Alma F):
    On 4 (Shard.vein (RootLaw.bare L.V.draws L.V.paid T p N m) i):=by
  let A:=L.V
  induction live using Nat.decreasingInduction with
  | self=>
    unfold RootLaw.bare
    rw [Nat.sub_self,walkY]
    exact hailed _ (freshly T H p L.spin L.bold) i (valence_cap ..)
  | of_succ m lt ih=>
    rw [RootLaw.bare,show N-m=N-(m+1)+1 by omega,walkY]
    have ht:=ShedG A.draws A.paid (h:=4) lt L.V.hG L.V.green ih le_rfl
    unfold Spout at ht
    rwa [grade_base,one_smul] at ht

private theorem held_one (n:Side)(c:ℝ):held (G:=G) n c=c • held n 1:=by
  ext a r y
  by_cases hr:0=r
  · subst r
    by_cases ha:a=0
    · subst a
      simp [held,uband,shine_lit]
    · simp [held,uband,shine_lit,PowerSeries.coeff_C,ha]
  · simp [held,uband,shine_dark hr]

theorem preimage (L:Theatre H T p e E W)(live:m≤N)(i j:Alma F)(lit:Cosmos.sheet F j=0)
    (X:Scroll D)(one:crease X (knurl (notar F (unitAt i))) 0=1):
    let A:=L.V.draws
    let c:=returned A j m (N-m) X
    let raw:=RootLaw.bare A L.V.paid T p N m
    jot (page D X) (raw.2 j)=jot (page D X) (c • (starting T p).2 (unitAt i)):=by
  intro A c raw
  have hn (n:Side):
      jot (page D X) (raw.1 n j)=jot (page D X) (c • (starting T p).1 n (unitAt i)):=by
    rw [map_smul,seed (unitAt i) (by rfl) _ L.spin L.bold,one,←held_one n c]
    exact WilsonIndependentMatchedFourUnitCourse.original j lit _ _ L.spin L.bold .. 
  funext a r
  have hu:=solo_bend (solo L live j) (page D X) a r
  have hs:=solo_bend ((hailed _ (freshly T H p L.spin L.bold) (unitAt i) (valence_cap ..)).μ (k:=4) c) (page D X) a r
  apply hu.exten
  exact hs.congr (Filter.Eventually.of_forall fun n=>congr_fun (congr_fun (hn n).symm a) r)

theorem original (L:Theatre H T p e E W)(live:m≤N)(i j:Alma F)(lit:Cosmos.sheet F j=0)(z:ℕ):
    let A:=L.V.draws
    let X:=testa D (notar F i).val
    let c:=returned A j m (N-m) X
    lineS (prismata F (RootLaw.bare A L.V.paid T p N m).2) z i j=
      c * lineS (1:Coil F) z i (unitAt i):=by
  intro A X c
  let raw:=RootLaw.bare A L.V.paid T p N m
  let start:=starting T p
  have one:crease X (knurl (notar F (unitAt i))) 0=1:=by
    change crease (testa D (notar F i).val) (knurl (notar F i)) 0=1
    rw [coinage,knurls,if_pos rfl]
  have hv:=preimage L live i j lit X one
  have he a r:jot (brow F i D) (raw.2 j) a r=
      jot (brow F i D) (c • start.2 (unitAt i)) a r:=congr_fun (congr_fun hv a) r
  change lineS (prismata F raw.2) z i j=_
  rw [coined,←(freshly T H p L.spin L.bold).era,coined,←smul_eq_mul,←glean_mu]
  unfold glean
  apply Finset.sum_congr rfl
  intro r hr
  split
  · unfold echoS trellis arret
    simp_rw [←jot_here,he]
    rfl
  · rfl

end YM.Integration.WilsonIndependentMatchedFourUnitProjection
