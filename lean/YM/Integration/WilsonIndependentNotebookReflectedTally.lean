import YM.Integration.WilsonIndependentNotebookReflectedSource

/-! Equivariance of the full native tally, including every stable-to-primary feed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedTally
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Wheel.Motion
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentNotebookReflectedSource (Paired projection minus transferred)
open scoped BigOperators Classical
variable {G:Gauge}{h k e D N m c:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h < D}{A B:Credit}

theorem residue (L:Theatre H T p e A B)(s:Signed)(hm:L.V.anchor ≤ m)(hn:m ≤ N)
    (keeps:h ≤ k){P Q:TowerS G D}(left:On k P)(right:On k Q)(pair:Paired s P Q):
    let K:=Peaks L.V.draws L.V.paid T p N m
    On k (Silt K P) ∧ On k (Silt K Q) ∧ Paired s (Silt K P) (Silt K Q):=by
  intro K
  have well:= (production L hn hm).1
  refine ⟨(sifted K well left keeps).1,(sifted K well right keeps).1,?_⟩
  unfold Silt
  apply minus s left right (Shrine_on K well _ keeps) (Shrine_on K well _ keeps) pair
  rw [projection H s p left right pair]
  exact fun n=>senses L hm hn _

theorem step (L:Theatre H T p e A B)(s:Signed)(hm:L.V.anchor ≤ m)(hn:m < N)
    (keeps:h ≤ k){P Q:TowerS G D}(left:On k P)(right:On k Q)(pair:Paired s P Q):
    let K:=Sink L.V.draws L.V.paid T p N m k
    On k (K P) ∧ On k (K Q) ∧ Paired s (K P) (K Q):=by
  intro K
  exact residue L s hm hn.le keeps (ShedG _ _ (h:=h) hn L.V.hG L.V.green left le_rfl)
    (ShedG _ _ (h:=h) hn L.V.hG L.V.green right le_rfl) (transferred _ _ L.V.hG L.V.green hn s left right pair)

theorem inherited (L:Theatre H T p e A B)(s:Signed)(hm:L.V.anchor ≤ m)(mc:m ≤ c)(cn:c ≤ N)
    (keeps:h ≤ k){P Q:TowerS G D}(left:On k P)(right:On k Q)(pair:Paired s P Q):
    let K:=breaths L.V.draws L.V.paid T p N k c m
    On k (K P) ∧ On k (K Q) ∧ Paired s (K P) (K Q):=by
  dsimp only
  induction mc using Nat.decreasingInduction with
  | self=>rw [breath_top,breath_top]; exact ⟨left,right,pair⟩
  | of_succ j hj ih=>
    obtain ⟨b,d,w⟩:=ih (hm.trans j.le_succ)
    rw [breath_step _ _ T p _ hj,breath_step _ _ T p _ hj]
    exact step L s hm (hj.trans_le cn) keeps b d w

/-- Equality in the full coupling series, for every component of the true
projection at the target m. Both sources use the same original N and c. -/
theorem original (L:Theatre H T p e A B)(s:Signed)(hm:L.V.anchor ≤ m)(mc:m ≤ c)(cn:c ≤ N)
    (keeps:h ≤ k){P Q:TowerS G D}(left:On k P)(right:On k Q)(pair:Paired s P Q):
    let K:=tallyV L.V.draws L.V.paid T p N k c m
    K Q=Cosmos.paintC F s *ᵥ K P:=by
  intro K
  let A₀:=L.V.draws
  let O:=L.V.paid
  let Δ (Z:TowerS G D):=Silt (Peaks A₀ O T p N c) Z
  let U:=Cosmos.paintC F s
  obtain ⟨l,r,gap⟩:=residue L s (hm.trans mc) cn keeps left right pair
  have coarse (j:ℕ)(hj:j∈range (c-m)):
      barley A₀ O T p N k c (Δ Q) (m+j)=U*ᵥ barley A₀ O T p N k c (Δ P) (m+j):=by
    have v:=mem_range.mp hj
    have age:m+j+1 ≤ c:=by omega
    obtain ⟨l',r',hit⟩:=inherited L s (hm.trans (show m ≤ m+j+1 by omega)) age cn keeps l r gap
    have live:m+j < N:=by omega
    exact projection H s p (ShedG A₀ O (h:=h) live L.V.hG L.V.green l' le_rfl)
      (ShedG A₀ O (h:=h) live L.V.hG L.V.green r' le_rfl)
      (transferred A₀ O L.V.hG L.V.green live s l' r' hit)
  change opal F Q+boot A₀ O T p N k c m (c-m) (Δ Q)=U*ᵥ(opal F P+boot A₀ O T p N k c m (c-m) (Δ P))
  rw [Matrix.mulVec_add,projection H s p left right pair]
  apply congrArg (fun x:Verse F=>U*ᵥ(opal F P)+x)
  unfold boot
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coarse j hj]
  exact tuneSpin (σ:=s) L (hm.trans (Nat.le_add_right ..)) (show m+j+(c-m-j) ≤ N by have:=mem_range.mp hj;omega) _

end YM.Integration.WilsonIndependentNotebookReflectedTally
