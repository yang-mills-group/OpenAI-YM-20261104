import YM.Integration.WilsonPhysicalStationSubtractedPosts
import YM.Integration.WilsonPhysicalStationCofinalBasis
import YM.Integration.WilsonPhysicalStationCoincidentBasis

/-! Select the genuine earlier-image terminals on the very same physical regulator election and read the signed two-reporter response. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationElectedEars
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonMovingForkReporterBothArms (Filed)
open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations Work.G08 Trace.Physical.GermGraph Next.Rank.Price
open WilsonPhysicalStationKineticLimit (transit)
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationSubtractedPosts (heard)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
  (fac:Facilities R.family f S)(F:Spec.Final R.family f S){ℓ:Ultrafilter (ℕ×ℕ)}
  (J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
  {H:(Bel R.family.book).Hierarchy}{I:Type*}[Fintype I]{m k h e:ℕ}
local notation "rows" => R.family.labels.level h

def Reads (hm:h ≤ m)(hk:h ≤ k)(w:I→(ℕ×ℕ)→R.family.label h)(v:I→R.family.label h):Prop:=
  ∀(c:I→ℂ)(u z:(Bel R.family.book).Field h)(j:ℕ)(o:Fin 2 → Cover),Extraction.Order.grid R.family j o∈conf 2 →
    Tendsto (heard R V hm hk c w ((J.U k h).symm (J₀ (V k).wheel.r h u))
      ((J.U m h).symm (J₀ (V m).wheel.r h z)) j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>h) (Extraction.Order.grid R.family j o)
        ![J₀ (V k).wheel.r h u-S.project h (∑i,c i • v i),J₀ (V m).wheel.r h z]))

theorem ready (below:(ℓ:Filter _) ≤ f.fuse)(j:ℕ):∀ᶠp:ℕ×ℕ in (ℓ:Filter _),j<p.1:=by
  have h:∀ᶠp:ℕ×ℕ in f.fuse,j<p.1:=by
    rw [Extraction.Order.fused]
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually (eventually_gt_atTop j)
  exact h.filter_mono below

include L fac in
theorem adjacent (hm:h ≤ m)(hk:h ≤ k)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {am bm ak bk:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(coarse:Filed (f:=f) (l:=ℓ) J₀ J V h m am bm)
    (ca:(V m).checked f H m)(cb:(V k).checked f H k)(dates:(V k).k=(V m).k+1)(horizon:h=e+1)
    (gate:((R.family.path.levels.params (V m).k).columns)*err R (V m).k ≤ 1/2)
    (next:((R.family.path.levels.params (V k).k).columns)*err R (V k).k ≤ 1/2)
    (a:I→(rows).Index)(grades:∀i,((rows).grades (a i)).1=h)
    (bracket:∀N p:ℕ,(V m).k < N → 1/8 ≤ transit R (V m).k ((V m).k+1) (N,p) ∧ transit R (V m).k ((V m).k+1) (N,p) ≤ 12)
:
    ∃w:I→(ℕ×ℕ)→R.family.label h,(∀i p,∀t:(V k).k < p.1,
      WilsonPhysicalStationSelectedLower.Receipt R (V m) (V k) h e (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk)
        (p:=p.2) ca cb t (a i) (w i p)) ∧
      ∃g:ℝ,1/8 ≤ g ∧ g ≤ 12 ∧ Tendsto (transit R (V m).k (V k).k) (ℓ:Filter _) (𝓝 g) ∧
      ∃v:I→R.family.label h,(∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w i p)) (ℓ:Filter _) (𝓝 (v i)) ∧
        S.project h (v i)∈LinearMap.range (F.sector.derivatives.rise (show e ≤ h by omega))) ∧
        Reads R (ℓ:=ℓ) J₀ J V hm hk w v:=by
  have late:=ready below (V k).k
  have cost:∀ᶠp:ℕ×ℕ in (ℓ:Filter _),1/8 ≤ transit R (V m).k (V k).k p ∧ transit R (V m).k (V k).k p ≤ 12:=by
    filter_upwards [late] with p high
    rw [dates]
    exact bracket p.1 p.2 (by omega)
  obtain ⟨w,registered,b,sub,proper,slope,sl,sh,thermal,v,limits⟩:=WilsonPhysicalStationCofinalBasis.original R L fac (V m) (V k) h e (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk) F simple ca cb dates horizon gate next a grades below late cost
  have eq:=ℓ.unique sub proper
  subst b
  refine ⟨w,registered,slope,sl,sh,thermal,v,limits,?_⟩
  intro c u z j o safe
  exact WilsonPhysicalStationSubtractedPosts.original R F J₀ J V hm hk simple below fine coarse c w v
    (fun i=>(limits i).1) u z j o safe

include fac in
theorem coincident (hm:h ≤ m)(hk:h ≤ k)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {am bm ak bk:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(coarse:Filed (f:=f) (l:=ℓ) J₀ J V h m am bm)
    (ca:(V m).checked f H m)(cb:(V k).checked f H k)(dates:(V k).k=(V m).k)(horizon:h=e+1)
    (gate:((R.family.path.levels.params (V m).k).columns)*err R (V m).k ≤ 1/2)
    (next:((R.family.path.levels.params (V k).k).columns)*err R (V k).k ≤ 1/2)
    (a:I→(rows).Index)(grades:∀i,((rows).grades (a i)).1=h)
:
    ∃w:I→(ℕ×ℕ)→R.family.label h,(∀i p,∀t:(V k).k < p.1,
      WilsonPhysicalStationCoincidentLower.Receipt R (V m) (V k) h e (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk)
        (p:=p.2) ca cb t (a i) (w i p)) ∧
      ∃v:I→R.family.label h,(∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w i p)) (ℓ:Filter _) (𝓝 (v i)) ∧
        S.project h (v i)∈LinearMap.range (F.sector.derivatives.rise (show e ≤ h by omega))) ∧
        Reads R (ℓ:=ℓ) J₀ J V hm hk w v:=by
  have late:=ready below (V k).k
  obtain ⟨w,registered,b,sub,proper,v,limits⟩:=WilsonPhysicalStationCoincidentBasis.original R fac (V m) (V k) h e (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk) F ca cb dates horizon gate next a grades below late
  have eq:=ℓ.unique sub proper
  subst b
  refine ⟨w,registered,v,limits,?_⟩
  intro c u z j o safe
  exact WilsonPhysicalStationSubtractedPosts.original R F J₀ J V hm hk simple below fine coarse c w v
    (fun i=>(limits i).1) u z j o safe

end YM.Integration.WilsonPhysicalStationElectedEars
end
