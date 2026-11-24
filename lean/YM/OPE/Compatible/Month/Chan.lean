import YM.Next.RANK.Stretch
import YM.OPE.Compatible.Month.Lens
/-!
 # Shape generation & reboots. til now no reports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l:Filter ι} {A:ι→ Model D P L E o κ C m}
abbrev WickSite (A:Model D P L E o κ C m)(p:Site A.c):= A.V.ratio.embed p
structure Homer (A:Model D P L E o κ C m)(p:Site A.c)(d j:ℕ)(I: Seats A.forest) where
    Q:Support A.c
    X: Support A.f
    Y: Support A.f
    Z: Support A.f
    H: Seats A.forest
    good: Primacy A.forest I H Y X Z Q A.R.p.B j
    homeQ: Q=roomB p (pArc A.V.patch d)
    largeX : X=roomB (WickSite A p) (rope A.V.patch (o_cover A.V.patch d A.R.p.B j))
    header: H=seatB A.forest (roomB (WickSite A p) (o_cover A.V.patch d A.R.p.B j))
def fitted (A:Model D P L E o κ C m)(p:Site A.c)(d j:ℕ)(I: Seats A.forest) (hp:I⊆ seatB A.forest (roomB (WickSite A p) d)): Homer A p d j I:= ⟨_,_,_,_,_, mainRing A.forest p d _ j I hp,rfl,rfl,rfl⟩
lemma seatCard {c f:Side}{S:StepData c f} (F:Forest S.ratio)(X:Support f): (seatB F X).card ≤ X.card * Fintype.card Axis:=by
   let f:= X×ˢ(univ:Finset Axis); have hz : (Finset.map (Embedding.subtype _) (seatB F X))⊆f:=by
     intro i hi; obtain ⟨j,hp,rfl⟩:=mem_map.mp hi; exact mem_product.mpr ⟨(mem_filter.mp hp).2,mem_univ _⟩
   have hg:= Finset.card_le_card hz; simpa only [card_map, f,card_product,card_univ] using hg
namespace Chase
variable (h: Chase A l) {j:ℕ}(d:ι→ℕ) (hg:Lite A l (fun i=>(d i:ℝ)))
include h hg
lemma trackSpan :
 let a i:= o_cover (A i).V.patch (d i) (barM A i) j
 Lite A l (fun i=>(a i:ℝ)) ∧ Lite A l (fun i=>(rope (A i).V.patch (a i):ℝ)):=by
    intro r
    have he (v:ℝ):= Lite.flatC v h
    have hP {u:ι→ℕ} (hv:Lite A l (fun i=>(u i:ℝ))):Lite A l (fun i=>(rope (A i).V.patch (u i):ℝ)):=by
       unfold rope; push_cast; refine Lite.shift ((he 16|>.add hv h).add (he (4*L.val+1)) h) (h.port.mono fun i hi=>?_); dsimp only;rw [hi.port.2.1]
    suffices hp:Lite A l (fun i=>(r i:ℝ)) from ⟨hp,hP hp⟩
    apply Lite.shift (u:=fun i=>(o_cover D (d i) (barM A i) j:ℝ)) ?_ (h.port.mono fun i hi=>by unfold r; rw [hi.height]); unfold o_cover circuitY rope pArc ySpan; push_cast
    repeat' first | exact he _ | exact hg | exact billed h | apply Lite.add _ _ h | apply Lite.rmul
-- squeeze bound
variable (x:∀ i, Site (A i).c)(I:∀ i,Seats (A i).forest)(p:∀ i, Homer (A i) (x i) (d i) j (I i))
lemma dart : Lite A l (fun i=>( ((p i).X).card:ℝ)) ∧ Lite A l (fun i=>(coverNumber (barM A i) (p i).X:ℝ)) ∧ Lite A l (fun i=> ((p i).H.card:ℝ)):=by
    let g i:= o_cover (A i).V.patch (d i) (barM A i) j; let r i:= rope (A i).V.patch (g i); have hh:= h.port; obtain ⟨hf,hR⟩:=trackSpan (j:=j) h d hg
    have he {u:ι→ℕ}(hx:Lite A l (fun i=>(u i:ℝ))): Lite A l (fun i=> (((u i+u i+1:ℕ)^4:ℕ):ℝ)):=by
       push_cast; exact ((hx.add hx h).add (Lite.flatC (1:ℝ) h) h).product_pw h 4
    have ht(i): (p i).X=halo (r i) {WickSite (A i) (x i)}:=(p i).largeX
    refine ⟨?_,?_,?_⟩
    · apply (he hR).ofLe; filter_upwards with i; simp only [ht i, Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show Nat.le _ _ from le_trans (Corona.halo_size ..) (by simp; try rfl))
    · apply (he hR).ofLe; filter_upwards with i; simp only [ht i, Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (encumber _ _ (A i).R.p.B_pos (roomB (WickSite _ (x i)) (r i))).trans (pulseR ..)
    apply ((Lite.flatC ((Fintype.card Axis):ℝ) h).rmul (he hf)).ofLe; filter_upwards with i; simp only [Real.norm_of_nonneg (Nat.cast_nonneg _),norm_mul]; push_cast; rw [(p i).header]
    have hv: ((seatB (A i).forest (halo (g i) {WickSite (A i) (x i)})).card) ≤ Fintype.card Axis * ((g i + g i +1)^4):= by
      apply (seatCard ..).trans; rw [mul_comm]; gcongr; simpa using halo_size ({WickSite (A i) (x i)}) (g i)
    exact_mod_cast hv
end Chase
end YM.PhysicalNext.Repeat.Aroma
