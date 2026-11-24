import YM.GradedFar.Floor
import YM.GradedFar.Snow
import YM.GradedFar.Weekday
/-!
# Deliver C5 projection receipts at declared cap, from arbitrary larger horizon

Record here in particular how to exercise the grid hypothesis with the
appointment meshes and spacing price. In r units even on Far. (Assumes the prices on this earlier
PoseFit/JointLater input, won't assert their physical construction.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Finset Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Tariff Tariff.Sunshine Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Ballot Auth Neighbor
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (P: ℝ→tower S)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "V"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "g∴"=> strength G
variable {n m h d:ℕ}
local notation "X"=> Points n
include H
lemma projected {u:ListInput G n d} (hd:d≤h)(x:Points n) : sent V d x u=sent V h x (GradedFar.raised (fun _=>hd) u):=by
 ext1 k; by_cases hx:x∈conf n
 · rw [cashed _ _ hx, cashed _ _ hx]; have hb:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born; exact Scale.Measure.inherited Z.scheme Z.criterion 0 M σ hG hb.Taylor hb.still hb.base hd n _ _ _
 rw [sent,coeff_mk,sent,coeff_mk,declared,dif_neg hx,declared,dif_neg hx]; rfl
-- e.g., apply on a given high horizon plus restricted D as in text. No claim creates Pose receipts.
open Tariff.Ballot
variable {u:ℝ→ Normalize.Change G d} {p q:ℕ} {L: Type*} {r:L→ℝ} {t τ:ℝ→ℝ} {Ω:Filter L}
-- Pose compact cost
lemma fitsVote (φ:Test n)(hd:d≤h)(hp:∀ v:ListInput G n d,∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ x∈ tsupport φ,
    ‖frank F P none d r x v-appointedH140Crop q (τ r) (sent V h x (GradedFar.raised (fun _=>hd) (fun i=> stand (u r) (v i):ListInput G n d)))‖ ≤ C*g∴ r^(p+1)):
    Ballot.Session F P Z φ p q d τ u:= by intro i; simp_rw [← projected Z M H] at hp; exact hp i
-- no assumption for empty arity stamp in Fray
lemma vacancyVote (φ:Test 0): Ballot.Session F P Z φ p q d τ u:= by
 intro i; refine ⟨0,le_rfl,Eventually.of_forall (fun r x hx=>?_)⟩
 rw [frank_empty, start_small Z M H (φ.tsupport_subset hx) _ (fun i=>i.elim0),crop_one, sub_self,norm_zero,zero_mul]
lemma reserve {E: Type*}{B:L→E→Prop}{x:L→E→Points n}{τ:L→ℝ}{D:L→ Sec G d →ₗ[ℂ] Sec G d}(hd:d≤h)(hp:p≤q)(ht:Tendsto τ Ω (𝓝 0))
    (he: ∃ b:ℝ,0≤b ∧ ∀ᶠ x in Ω, |τ x-t (r x)| ≤ b*g∴ (r x)^(p+1))(hv: ∀ (v:Sec G d)(i:Toon G d), ∃ b:ℝ,0≤ b ∧ ∀ᶠ x in Ω,
       ‖coord i (D x v)-coord i v‖ ≤ b*g∴ (r x)^(p+1))
    (hY:∀ v:ListInput G n d,∃ C:ℝ,0≤C ∧ ∀ᶠ i in Ω,∀ j:E, B i j →
       ‖frank F P none d (r i) (x i j) v - appointedH140Crop q (τ i) (sent V h (x i j) (GradedFar.raised (fun _=>hd) (fun a=> D i (v a): ListInput G n d)))‖ ≤ C*g∴ (r i)^(p+1)):
    Portal F P Z Ω B r x t d p:= by simp_rw [← projected Z M H] at hY; exact ⟨q,τ,D,hp,ht,he,hv,hY⟩
-- same for mixed monetary uses on [1,2] ratio
lemma here {τ:Route→ℝ}{α β:Route→ Sec G d→ₗ[ℂ]Sec G d}(hd:d≤h)
    (ht:Tendsto τ upGauge (𝓝 0)) (hv:Tendsto (fun i=>Neighbor.stamp G d (α i)) upGauge (𝓝 1))(hf:Tendsto (fun i=>Neighbor.stamp G d (β i)) upGauge (𝓝 1))
    (hY:∀ (v w:Sec G d),∃ b:ℝ,0≤ b ∧ ∀ᶠ i in upGauge,
        ‖shared F P d i v w - appointedH140Crop q (τ i) (sent V h (outgoing RootG) (GradedFar.raised (fun _=>hd) (carpet d (α i v) (β i w))))‖ ≤ b*g∴ i.1) : JointTicket F P Z d:=by
 simp_rw [← projected Z M H] at hY; exact ⟨q,τ,α,β,ht,hv,hf,hY⟩
omit H
variable (C)
def report (q:Calendar→ℕ)(i:Calendar) : Set (Points n):= Set.range (rounded (n:=n) C i.1 (q i))
lemma enoughReports (N:ℕ)(r:ℝ) (hr:0<r)(x:Points n): ∃ y∈ Set.range (rounded C r N), ‖y-x‖ ≤ (4*(n:ℝ))* (C.S.a N/r):=by
 let l:= C.S.a N; let z:= address l (r•x); have h:= Extraction.approximate (C.S.a_pos N) (r•x); refine ⟨rounded C r N z, ⟨z,rfl⟩,?_⟩
 change dist (Order.grid C N z) (r•x) ≤ _ at h; rw [dist_eq_norm,targeted C hr,← smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm r] at h; exact le_trans ((le_div_iff₀ hr).2 h) (le_of_eq (by ring))
variable {C}{U B:ℝ} {K:Set (Points n)}{S':Set (Points m)}
local notation "P∥"=> moving G U B
section
variable (fmesh:Calendar→ℕ)
include hG
lemma covers {c:ℝ}(hc:0 ≤ c)(k:ℕ)(he:∀ᶠ p in P∥, C.S.a (fmesh p) / p.1 ≤ c*g∴ p.1^k): Coverage G U B K S' (report C fmesh) k:= by
 let D:=4*((n+m:ℕ):ℝ); have hd:0≤D:= by dsimp only [D]; positivity
 refine ⟨D*c+1,by positivity,?_⟩; filter_upwards [he, poses (strength_positive hG), poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin)] with i hh hp he x _
 obtain ⟨p,hz,h⟩:= enoughReports C (fmesh i) i.1 he x; exact ⟨p,hz,h.trans ((mul_le_mul_of_nonneg_left hh hd).trans ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right (by linarith only) (by positivity))))⟩ -- linarith only
end
include hG in
lemma installLiteral (H:∀ K' N', IsCompact K'→ K'⊆conf n→IsCompact N'→ N' ⊆ Outside m→ K ⊆ interior K'→ S' ⊆ interior N'→
    ∀ k:ℕ,1≤k→ ∃ (fmesh:Calendar→ℕ) (c:ℝ),0≤c ∧ (∀ᶠ p in P∥,C.S.a (fmesh p)/p.1 ≤ c*g∴ p.1^k) ∧
      Portal F P Z P∥ (fun i x=> x∈report C fmesh i ∧ Access K' N' i x) Prod.fst (fun _ x=>x) t h q): GridPose F P Z t K S' h U B q:= by
 intro K N hK hx hN hz hp hi k he; obtain ⟨fmesh,c,hc,H',H⟩:= H K N hK hx hN hz hp hi k he
 exact ⟨report C fmesh, covers fmesh (hG:=hG) hc k H',H⟩
end YM.Integration.GradedFar.Batch
