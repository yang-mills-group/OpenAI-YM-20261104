import YM.Integration.WilsonOriginalPublicTrialPhaseUncutEar
import YM.Integration.WilsonOriginalPublicTrialPhaseUncutOpening
import YM.Integration.WilsonOriginalPublicTrialPhaseCampusRoom
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyRoom
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyTrueRoots

/-! Independent K-cell placements of every physical arm, with the original finite Gibbs and fixed-ear estimates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseUncutCells
open Function Finset Filter MeasureTheory Lattice Wilson RG Source Labels Cells OPE.Therm
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign Extra.Multi Extra.Histories
open RG16 RG16.Literal RG05Readout RG05Readout.Many Push.GridApprox Push.Local
open WilsonOriginalNullOriginGridRoster (ancestry)
open WilsonOriginalPublicTrialPhaseGrant (Grant)
open WilsonOriginalPublicTrialPhaseTrace (word)
open WilsonOriginalPublicTrialPhaseRay (guard)
open WilsonMeasuredPublicEntranceTransferSubmittedPhase (site)
open private singleton from YM.Integration.WilsonForcedReplicaDistance
open scoped Topology Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G)
local notation "C" => R.family
local notation "S" => (C).S
local notation "A" => (C).path
local notation "H" i:arg => (A).levels.clock.hatBeta i

set_option maxHeartbeats 3200000 in
theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(simple:G.Simple)
    (purchase:RG05Preconstruction.ReadoutPurchase R.b)(storage:RG05Readout.Many.Storage (C) R.doors)
    (cater:Cater (C) R.doors)(tabs:Stock.Tabs (A).levels)(d:I→ℕ)(anchor:I)
    (T:I→ℝ)(tp:∀k,0≤T k)(e:I→ℕ)(j q aperture:ℕ)
    (ceiling:∀i,((A).levels.budget i).supportExponent=100):
    ∀ᶠ u:ℕ in atTop,∀ᶠ c:ℕ in atTop,∀f K N per:ℕ,c≤f → f≤K → c+1<K → K≤N →
    H K≤2*H c → (S).a c/(S).a K≤(H c)^aperture →
    ∀z:I → Cover,(∀k,‖(S).gridPoint K (z k)‖≤(S).a (c+1)/8) →
    ∀v:∀k,(C).label (d k),(∀k,((C).labels.level (d k)).coeffSize (v k)≤T k*(H K)^(e k)) →
    let pins:=fun k=>wrap ((C).side K per) (z k)
    let M:=word R (N:=N) d pins v
    ∃uk:u≤K, (∃g:Grant R (N:=N) d pins v uk (1/(H f)^q),g.station=j) ∧
       ‖(∫U,M U ∂scene (A) N per K)-actualTransport (C) (N:=N) M uk 1‖≤1/(H f)^q:=by
  classical
  obtain ⟨base,jb,loc⟩:=WilsonOriginalPublicTrialPhaseCampusRoom.opened R simple storage tabs j
  obtain ⟨stage,opens⟩:=eventually_atTop.mp (WilsonOriginalPublicTrialPhaseUncutOpening.original R simple d)
  let radius:=∑k:I,stencilRadius (C) (d k)
  have span(k:I):stencilRadius (C) (d k)≤radius:=single_le_sum (f:=fun t:I=>stencilRadius (C) (d t)) (fun _ _=>Nat.zero_le _) (mem_univ k)
  obtain ⟨ε,ep,cut,space⟩:=WilsonMeasuredPublicEntranceTransferCopyRoom.original R j radius 0
  have shrinking:Tendsto (fun c:ℕ=>(S).a (c+1)/8) atTop (𝓝 0):=by
    simpa using (((S).shrinks.comp (tendsto_add_atTop_nat 1)).div_const (8:ℝ))
  filter_upwards [eventually_ge_atTop base,eventually_ge_atTop stage] with u bu su
  have ju:=jb.trans bu
  filter_upwards [eventually_gt_atTop u,eventually_ge_atTop cut,shrinking.eventually (gt_mem_nhds ep),
    WilsonOriginalPublicTrialPhaseUncutEar.original R book simple purchase storage cater d anchor T tp e j u ju q aperture 1 ceiling]
    with c uc cutoff small paid
  intro f K N per cf fk ck live heat optical z reach v measured pins M
  let o(i:ℕ)(k:I):=ancestry R per K (pins k) i
  have start:o K=pins:=funext fun k=>WilsonOriginalNullOriginGridRoster.starts R per K (pins k)
  have birth(k:I):o (c+1) k=0:=
    WilsonSeparatedPrefixScreenedParents.original R (by omega:c+2≤K) z ((S).a (c+1)/8) reach (by linarith) k
  have null(m:ℕ)(mc:m≤c+1)(k:I):o m k=0:=
    WilsonMeasuredPublicEntranceTransferCopyTrueRoots.older R mc ck.le (pins k) (birth k)
  have homes(i:ℕ)(ik:i<K):((A).levels.clock.op i per).ratio.parent ∘ o (i+1)=o i:=
    funext fun k=>WilsonOriginalNullOriginGridRoster.route R per K (pins k) ik
  have area:=space (n:=1) (p:=per) (show K≤K from le_rfl) (cutoff.trans (cf.trans fk))
     (div_pos ((S).a_pos _) (by norm_num)) small
  let size:=((S).toDepth (show K≤K from le_rfl) per).count.val*WilsonMeasuredPublicEntranceTransferCopyRoom.reach R K ((|(0:ℝ)+1|+1)*((S).a (c+1)/8))+radius
  have fit(k:I):window (pins k) (stencilRadius (C) (d k))⊆window 0 size :=by
    have yes:=area.2 (fun _:Fin 1=>d k) (fun _=>span k) (fun _:Fin 1=>z k)
      (fun _=>by simpa using reach k) 0
    simpa only [site,RG05Readout.Records.like_embed,pins] using yes
  have boundK:=opens K (by omega) |>.2.2 N per live
  have floors(i:ℕ)(ui:u ≤ i):stage ≤ i :=su.trans ui
  have room(i:ℕ)(ui:u ≤ i)(ic:i<c)(ji : j ≤ i):
      pdist (o i anchor)+pdist (o i anchor)+((A).levels.budget i).B*guard (S) i (Bandage.renal (A).levels i)<
        ((S).toDepth ji per).count.val:=by
    apply loc i (bu.trans ui) per (o i anchor)
    rw [null i (by omega)]
    have zero:pdist (0:Site ((C).side i per))=0:=by
      simpa only [separation,sub_zero] using separation_self (0:Site ((C).side i per))
    rw [zero,Nat.cast_zero,mul_zero]
    exact div_nonneg ((S).a_pos _).le ((S).a_pos _).le
  obtain ⟨g,same⟩:=paid f K N per uc cf fk ck live heat optical o (fun i _ hi=>homes i hi) v measured
    (fun k=>boundK.2.2.2 k _) boundK.2.2.1 _ (fun k=>start.symm ▸ fit k) area.1
    (fun k=>by rw [birth anchor,birth k,Finset.insert_eq_of_mem (Finset.mem_singleton_self _)];exact singleton _ _)
    (fun i ci _=>(opens i (by omega)).2.1) (fun i ui _=>(opens i (floors i ui)).1)
    (fun i ui ic=>(opens i (floors i ui)).2.2 N per (by omega)|>.1)
    (fun i ui ic=>(opens i (floors i ui)).2.2 N per (by omega)|>.2.1) room
  have uk:u≤K:=by omega
  have sponsored:∃g:Grant R (N:=N) d pins v uk (1/(H f)^q),g.station=j:=by
    rw [←start]
    exact ⟨g,same⟩
  obtain ⟨grant,sold⟩:=sponsored
  exact ⟨uk,⟨grant,sold⟩,WilsonOriginalPublicTrialPhaseGrant.original R d pins v uk live grant⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseUncutCells
end
