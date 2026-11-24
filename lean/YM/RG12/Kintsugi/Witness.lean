import YM.RG12.Rail.Run
import YM.Pert.Dense.Supplier
import YM.RG12.Alidade.Logbook
/-!
# Strengthened commissioning for all n,d compact test calibration

Only ask retention of the chosen arcs, NOT another lit set or new calendar obligations. See
Grant for the new launch port. Everything on the same UV bewall.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Climb Ward Next.UVStress
open MergeProof MergeProof.East
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff)
structure Ranked (P:Commission.Port C) : Prop where
   signs d: ∃ ξ, Checks (P.panels d 0).arc (P.panels d 1).arc (P.panels d 2).arc ξ (trays d) d
variable (hS:Ranked P) (T:MaxwellData C)
include h
local notation "A!"=> C.path.levels
lemma achieving {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{L:∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
   (hp:Scrim C W u ψ φ δ (fly (A!)) r L)(hG:G.Simple) (d:ℕ)
   {c:ℝ}(he:Checks (P.panels d 0).arc (P.panels d 1).arc (P.panels d 2).arc c (trays d) d) (R:ℝ)(hR:0<R) (ε:ℝ)(hε:0<ε) :
    ∀ᶠ k in atTop, ∀ I:ℕ→ℕ→TableL C d, Poised (P.panels d) P.chart U.room.cutoff P.haar P.locality (trays d) (P.budget d) k I →
       (wok C d k (P.panels d 0).arc c I).toStation.Admissible f T.hT.spin (d+2) R ε:=by
    by_contra! e
    obtain ⟨k,hk,hE⟩:=extraction_of_frequently_atTop e
    have hQ := h
    choose I hI h using hE -- shadows h
    let K(n):=wok C d (k n) (P.panels d 0).arc c (I n)
    have hr(n)(b:ℝ):= w_right (P:=P.panels d) c f T.hT.spin b (hI n)
    have hg : Granular K f T.hT.spin (d+2) R := by
       refine ⟨⟨Eventually.of_forall (fun i=>(hr i (P.panels d 0).arc).1),Eventually.of_forall (fun i=> (hr i (P.panels d 0).arc).2.mono fun j h=>h.mono fun k h=> h.1),Eventually.of_forall (fun i=> (hr i (P.panels d 0).arc).2.mono fun j h=>h.mono fun k h=> h.2.1),Eventually.of_forall (fun i=> (hr i (P.panels d 0).arc).2.mono fun j h=>h.mono fun k h=> h.2.2)⟩,(Station.gap_rate (A!) hG _).comp hk.tendsto_atTop,?_⟩
       intro n hn q ht x
       exact aspect (P.panels d) P.chart U.room.cutoff hG hp P.haar P.locality _ (hQ.covered.2.1 d) f (Nat.le_add_left ..) R hR T.hT.smooth T.hT.spin he q ht (depthWord q _) hn hk.tendsto_atTop _ hI
    obtain ⟨i,hi⟩:=(supply_wheel K hg U.room.ordered U.room.kernel.smooth U.room.cutoff U.room.generic T.hT.smooth hR ε hε).exists
    exact h i hi

section panel
local notation "H!"=>U.room.kernel
local notation "B!"=> Bel C.book
private abbrev mold (d:ℕ) (Y:Lifts C d) (S:Table C.book) : Next.UVStress.Panel S := fun i=> if e:i≤d then (S.project i).comp (Y ⟨i,Nat.lt_succ_of_le e⟩).toLinearMap else 0
variable {D rank:ℕ}(X:Next.UVStress.Station C D){ℱ:Filter UVIndex}[ℱ.NeBot](hF:ℱ ≤ f.fuse)(Y:Lifts C D)
    (he:∀ (i : Fin (D+1)) v,Tendsto (fun j=> X.atCut j i v) ℱ (𝓝 (Y i v)))
    {R ε:ℝ}(hs:X.Admissible f T.hT.spin rank R ε)
-- fixed filter instantiation of harvested proof
omit h in
include hF he hs in
lemma all_charms :
      let Z:= mold D Y S
      (∀ d≤D, StraightAt (S:=S) (H!).spin T.hT.spin Z d) ∧ Z 0 ((B!).unit 0)=S.unit 0 ∧
      ∀ (n : ℕ), n ≤ rank → ∀ v : Fin n → (Bel C.book).Tag, (∀ i,(v i).1 ≤ D) →
        ∀ t : Test n, tsupport t ⊆ Scaling.window R n →
        ∀ M : ℝ, 0 < M → (∀ x, ‖t x‖ ≤ M) →
        ‖t.applyTo (Next.UVStress.tested X.r Z v) - t.applyTo (disc v)‖ ≤ ε * Next.UVStress.Station.charge v * M := by
  intro Z
  have eq (d : ℕ) (h : d≤D) x : Z d x=S.project d (Y ⟨d,Nat.lt_succ_of_le h⟩ x) := by simp only [Z,dif_pos h]; rfl
  let z : Fin (D+1) := ⟨0,Nat.succ_pos _⟩
  refine ⟨fun d hd => ?_, ?_, fun n hn v hv t ht M hm ht' => ?_⟩
  · let i : Fin (D+1) := ⟨d,Nat.lt_succ_of_le hd⟩
    constructor
    · intro x; rw [eq d hd,eq d hd,S.conj_project]; apply congr_arg
      exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).conj T.hT.spin d x)) (he i x).star
        (((show ∀ᶠ j in f.fuse, ∀ (i : Fin (D+1)) v, X.atCut j i ((Bel C.book).conj _ i v) = star (X.atCut j i v) from hs.lift_real)).filter_mono hF |>.mono fun _ h => h i x)
    intro s x; rw [eq d hd,eq d hd,S.mirror_project]; apply congr_arg
    exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).mirror T.hT.spin d s x))
      ((C.book.mirrorGroup d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (he i x))
      (((show ∀ᶠ j in f.fuse, ∀ (i : Fin (D+1)) s v, X.atCut j i ((Bel C.book).mirror T.hT.spin i s v) = C.book.mirrorGroup i s (X.atCut j i v) from hs.lift_signed)).filter_mono hF |>.mono fun _ h => h i s x)
  · rw [eq _ (Nat.zero_le _)]
    apply congr_arg (S.project 0)
    refine tendsto_nhds_unique_of_eventuallyEq (he z ((Bel C.book).unit 0)) tendsto_const_nhds ?_
    exact (show ∀ᶠ u in f.fuse, X.atCut u z ((Bel C.book).unit 0) = C.book.scalar 0 from hs.lift_unit).filter_mono hF
  let g : Caps n := fun i => (v i).1
  let m (j) (i : Fin n) : C.book.Ref (g i) := X.atCut j ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  let y (i : Fin n) : C.book.Ref (g i) := Y ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  have hh : S.integralOn g y (Next.UVStress.dilate X.rad t)=t.applyTo (Next.UVStress.tested X.r Z v) := by
    unfold Table.integralOn; rw [zoom_integral]
    apply t.apply_eq; intro x hx
    change S.value g _ y = S.useAt S _ (panels Z ∘ v)
    let l : Fin n → C.book.Token := fun i => ⟨g i,y i⟩
    rw [show panels Z ∘ v = S.classTokens ∘ l from funext (fun i => by
      unfold panels Function.comp
      change Sigma.mk (g i) (Z (g i) ((v i).2)) = Sigma.mk (g i) (S.project (g i) (y i))
      rw [eq _ (hv i)])]
    exact (S.at_project S (H!).laws.toSymmetric (fun _ => le_rfl) ((enlarged X.rad _).1 hx) l).symm
  have hz : Tendsto (fun j : ℕ×ℕ => X.paid v hv t j.1 j.2) ℱ (𝓝 (t.applyTo (Next.UVStress.tested X.r Z v))) := hh ▸
    calibrated_smear U.room.ordered ℱ hF _ (v:=m) (x:=y) fun i => he ⟨(v i).1,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  refine le_of_forall_pos_le_add fun η hη => ?_
  exact le_of_tendsto ((hz.sub_const (t.applyTo (disc v))).norm)
    ((show ∀ᶠ i in f.fuse, ‖X.paid v hv t i.1 i.2 - t.applyTo (disc v)‖ ≤ ε * Next.UVStress.Station.charge v * M + η from
      hs.short hn v hv t ht M hm ht' η hη).filter_mono hF)
end panel
end YM.RG12.Kintsugi
namespace YM.RG12.Kintsugi
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Climb Ward Next.UVStress
open MergeProof MergeProof.East
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff)
variable (hS:Ranked P) (T:MaxwellData C)
local notation "A!"=> C.path.levels
local notation "H!"=>U.room.kernel
local notation "B!"=> Bel C.book
local notation "χ"=> C.path.levels.clock.hatBeta
def angle (k d:ℕ)(Z:TableL C d) : Lifts C d:= fun i => LinearMap.toContinuousLinearMap (Arche.aligned C M k (Z i) ∘ₗ (ladder C i).toLinearMap)
def shore (k d:ℕ)(Z:TableL C d): Next.UVStress.Panel S:= mold d (angle M k d Z) S
lemma shore_at (k d i:ℕ)(Z:TableL C d)(hi:i≤d)(w:(B!).Field i): shore (S:=S) M k d Z i w = S.project i (Arche.aligned C M k (Z ⟨i,Nat.lt_succ_of_le hi⟩) (ladder C i w)):=by
    unfold shore mold angle; rw [dif_pos hi]; rfl
-- uniform along lit for ANY FIXED d, no extraction choices beyond Observe (ω same all d). Use for diagonal contradiction.
structure Authentic (k d:ℕ) (Z:TableL C d) : Prop where
    -- measured frame. lens not necessarily scheme U, but will soon align it.
    straight i : i≤d → StraightAt (H!).spin T.hT.spin (shore M k d Z) i
    units : shore M k d Z 0 ((B!).unit 0)=S.unit 0
    limits_ (n:ℕ) : n ≤ d+2 → ∀ v : Fin n → (B!).Tag,(∀ i,(v i).1 ≤ d)→
      ∀ t:Test n,tsupport t ⊆ Scaling.window (sizeHint d) n → ∀ a:ℝ,0<a → (∀ x, ‖t x‖ ≤ a) →
         ‖t.applyTo (Next.UVStress.tested (gap (A!) (P.panels d 0).arc k) (shore (S:=S) M k d Z) v)- t.applyTo (disc v)‖ ≤ costHint d * Next.UVStress.Station.charge v * a
    above i v: mass C _ (Z i v) ≤ 2*(2*(A!).clock.monitor k)^i.val*(mag (A!) (P.panels d 0).arc k)^i.val*mass C _ v
    below i v: mass C _ v ≤ 2^i.val*(3/2)*mass C _ (Z i v)
    covers i: Surjective (Z i)
    leveled : mag (A!) (P.panels d 0).arc k ≤ χ k
    monitored : (A!).clock.monitor k ≤ χ k

include h hS
lemma wears (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) (hG:G.Simple) (d:ℕ):
    ∀ᶠ k in atTop,lit k →∃ Z,Authentic U M P T k d Z:=by
   obtain ⟨ξ,hξ⟩:= hS.signs d
   obtain ⟨W,r,L,hR⟩:= H.costlier
   let A:= C.path.levels; let a:= (P.panels d 0).arc
   have Tea(t:ℝ):∀ᶠ k in atTop,bill t (χ k) ≤ χ k := by
      filter_upwards [(hat_grows (C:=C) hG).eventually (Alidade.boil_in t 1 one_pos)] with k hk; simpa only [Real.rpow_one] using! hk
   have Ha:= achieving U P h T (hR.toPackage.toTableTickets.system) hG d hξ (sizeHint d) (zero_lt_one.trans_le (show 1 ≤ sizeHint d from by simp [sizeHint])) (costHint d) (cost_pos _)
   filter_upwards [Ha,h.offers d,Tea 1,Tea a] with k hk hz ht ht' hi
   obtain ⟨I,hI⟩:=hz hi
   let l:= Ultrafilter.of ϕ; let b:=mag A a k
   have hb:1 ≤ b:=by dsimp [b]; rw [mag_bill]; exact Glimmer.costed a _ (by unfold a; linarith only [(P.panels d 0).huge,Nat.cast_nonneg (α:=ℝ) d])
   obtain ⟨Z,hZ⟩:=Arche.compare_in he hI.early hI.charts b hb l (Ultrafilter.of_le ϕ)
   have hY(i:Fin (d+1))(v:(B!).Field i) : Tendsto (fun j=> (wok C d k a ξ I).atCut j i v) (l:Filter UVIndex) (𝓝 (angle M k d Z i v)) := Arche.tends_aligned he hZ i (ladder C i v) (hI.early _ i.is_le)
   obtain ⟨h1,h2,h3⟩:= all_charms U T (wok C d k a ξ I).toStation ((Ultrafilter.of_le ϕ).trans hf) _ hY (hk I hI)
   refine ⟨Z,h1,h2,h3,hZ.ceiling,hZ.base,fun i=> (Arche.produced hZ i).2,?_,?_⟩
   · rw [mag_bill]; exact ht'
   change A.clock.monitor k ≤ χ k; rw [show  A.clock.monitor k=bill 1 (χ k) from ?_]; exact ht
   simp [A,Perch.bill,Calendar.monitor,boil,Perch.y]
end YM.RG12.Kintsugi
