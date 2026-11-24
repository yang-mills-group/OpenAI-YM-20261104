import YM.SharpGram.Lenses.Sights
import YM.Pier.Lair.Grace

/-! exhaust ℕ horizons in real lengths. subsequently change to any compatible frame with near continuity property. physical read.ALL r at F on Gamma; use basis and multilinearity so no continuity of frame asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Lair
open Function Filter Set Table Extraction Climb Analysis Ward Spec
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank
open Next.UVStress Spin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f : Extraction.Order}{S:Table C.book}
variable (F: Final C f S) (h:G.Simple) {H : (Bel C.book).Hierarchy}
set_option quotPrecheck false
local notation "B" => (Bel C.book)
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "τ" => (turns C)
local notation "W₀" => (Maxwell.Free.scheme C.book.grid)
local notation "W₁" => F.sector.derivatives
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "H₁" => F.room.kernel
local notation "τ₁" => F.sector.turns
variable {X:Scaling S}{l: Ultrafilter (ℕ×ℕ)}{Z:Arch C}{V:∀ i, Vane C i}
open MeasureTheory SharpGram Lenses
open scoped ContDiff

-- all r version, unit at horizon. Retain field gains compatible with limiting scheme through turning cameras
structure OStage (Y:FamilyBasis (C:=C) S) (m:ℕ):Prop where
   orient : ∀ i:Fin (m+1),AlignO F.sector F.room.kernel.spin (Maxwell.Free.hierarchy C.labels) _ (Y i)
   aligned (i j:Fin (m+1)) (he:i.val ≤ j.val) (x): Y j ((W₀).rise he x)=(W₁).rise he (Y i x)
variable (Y:ℝ→FamilyBasis (C:=C) S)
def edition (R : Zoom) : Scaling S:= ⟨Y ∘ R.r,fun _=>1,R.r,fun _=>one_pos, R.positive,R.shrinking,R.limits⟩
structure Present : Prop where
    aligned m : ∀ᶠ r in Pilot.trail, OStage F (Y r) m
    continuity (R:Zoom) : Approaches R (isoPanel (edition Y R)) -- NB of the tested correlations on all-field basis, not of basis itself

lemma sleeve_of (hq:Approaches (path X) (isoPanel X)) (m:ℕ): ∀ᶠ i in atTop,Lenses.Sleeve m (isoPanel X i) (X.r i) :=by
    have hs:= Next.UVStress.window_closed (sizeHint m)
    have hr: 0<sizeHint m:= inv_pos.mp (cost_pos m)
    have hQ(n:Fin (m+1))(t:Fin n → Fin (m+1))(x:record C (fun i=>(t i).val)):=
        (hq.values n (hang _ (depthWord (fun i=>(t i).val) x))).reads _ (hs n) (fun x hx=>spaced_conf (inv_pos.mpr hr) hx.1) _ hr _ (cost_pos m)
    filter_upwards [eventually_all.mpr (fun i=> eventually_all.mpr (fun v=>eventually_all.mpr (hQ i v)))] with i hi
    refine ⟨fun {n} hn q hv x=>?_⟩; let j:Fin (m+1):=⟨n,Nat.lt_succ_of_le hn⟩
    exact hi j (fun i=>⟨q i,Nat.lt_succ_of_le (hv i)⟩) x
lemma clarity (B0:Bliss F l Z H): ∃ T:ℝ→FamilyBasis (C:=C) S, Present F T ∧ PlotX F H l h (fun r=> T r 4):=by
    let O(r:ℝ)(p:FamilyBasis (C:=C) S)(m:ℕ):Prop:= AtAngle F (H:=H) (𝓛:=l) h r (p 4)∧ OStage F p m∧ Lenses.Sleeve m (Lenses.testLens p) r
    let U(r:ℝ)(p:FamilyBasis (C:=C) S)(m:ℕ):Prop:= ∀ j:Fin (m+1),O r p j
    have hs(m):∀ᶠ r in Pilot.trail, ∃ p:FamilyBasis (C:=C) S, U r p m:=by
       by_contra hy
       obtain ⟨s,hS,hQ⟩:= contradictionTrail _ hy; obtain ⟨f,hf,J,hJ,V,hV⟩:=B0.picks s (hS.mono_right nhdsWithin_le_nhds) (fun i=> (hQ i).1)
       obtain ⟨J',hΩ,hA,hS₀,hB,hL⟩:= angles F h hV
       have hz d: ∀ᶠ i in atTop,O (J'.r i) (J'.U i) d:=by
           filter_upwards[hL,sleeve_of hA d,eventually_all.mpr (fun i:Fin (d+1)=>hB i),eventually_all.mpr (fun i:Fin (d+1)=>eventually_all.mpr (fun j:Fin (d+1)=>eventually_all.mpr (fun h:i.val ≤ j.val=> hS₀.rises _ _ h)))] with i hi hv hw hV; exact ⟨hi,⟨fun j=>hw j,hV⟩,hv⟩
       obtain ⟨i,hi⟩:= (eventually_all.mpr (fun i: Fin (m+1)=> hz i)).exists
       rw [hΩ,hJ] at hi; exact (hQ (f i)).2 ⟨J'.U i,hi⟩
    let A i:= glen C.S i
    let p(r:ℝ): Finset ℕ:= (Finset.Iic (A r)).filter fun m=>∃ v:FamilyBasis (C:=C) S,U r v m
    obtain ⟨x,f,hX⟩:= (hs 0).exists
    let Y (r:ℝ):= if h:(p r).Nonempty then (show ∃ v:FamilyBasis (C:=C) S,U r v ((p r).max' h) from (Finset.mem_filter.mp (Finset.max'_mem (p r) h)).2).choose else f
    have Hz(m):∀ᶠ i in Pilot.trail,O i (Y i) m:=by
       filter_upwards [hs m,(glen_leads C.S).eventually_ge_atTop m] with i hi hp; have hv:m∈p i:=Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hp,hi⟩; have ht:(p i).Nonempty:=⟨m,hv⟩
       have hd: U i (Y i) ((p i).max' ht):=by unfold Y; rw [dif_pos ht]; exact (show ∃ v,U i v ((p i).max' ht) from (Finset.mem_filter.mp (Finset.max'_mem (p i) ht)).2).choose_spec
       exact hd (⟨m,Nat.lt_succ_of_le (Finset.le_max' _ m hv)⟩: Fin ((p i).max' ht+1))
    refine ⟨Y,⟨fun m=> (Hz m).mono fun i hi=> hi.2.1,?_⟩,(Hz 4).mono fun i hi=> hi.1⟩
    intro R; constructor; intro n v
    let t : Caps n:=fun i=>(v i).1
    let K:= edition Y R; let M:=isoPanel K; let V(i:Fin n):=(v i).2
    have hT:Tendsto R.r atTop Pilot.trail:= tendsto_nhdsWithin_iff.mpr ⟨R.limits,Eventually.of_forall R.positive⟩
    have hy(i:record C t): let p:= hang t (depthWord t i); Fades (fun k=> Next.UVStress.tested (R.r k) (M k) p - disc p):=by
       intro p
       refine ⟨fun k=>(smoothZoom (H₁).smooth _ (R.positive k)).sub (smoothDisc (T:=Bel C.book) H.smooth p),fun s hs hK D hp ε he=> ?_⟩
       obtain ⟨k,hk,hi,hq,hL,hζ⟩:= ((eventually_ge_atTop n).and ((eventually_all.mpr fun i=> eventually_ge_atTop (t i)).and
         ((size_ascends.eventually_ge_atTop D).and ((size_ascends.eventually (Work.A05.compact_fits hs hK)).and (cost_clears.eventually (ge_mem_nhds he)))))).exists
       filter_upwards [hT.eventually (Hz k)] with j hj x hx hP
       exact ((hj.2.2).ticket hk t hi i x (hx.trans hL) (fun i=>(hP i).trans hq)).trans hζ
    change Fades (fun k=>Next.UVStress.tested (R.r k) (M k) _-_)
    exact SharpGram.fadeTuple F R.positive hy (fun k=>V) V (fun _=>tendsto_const_nhds)

variable (P : Present F Y)
namespace Present
include P in
lemma grade (d e:ℕ)(ht:d≤e) : ∀ᶠ i in Pilot.trail,∀ x,Y i e ((W₀).rise ht x)=(W₁).rise ht (Y i d x):=(P.aligned e).mono fun _ hi=> hi.aligned (⟨_,Nat.lt_succ_of_le ht⟩ : Fin (e+1)) (Fin.last e) ht
include P in
lemma scheme (d:ℕ):∀ᶠ i in Pilot.trail,AlignO F.sector (H₁).spin (Maxwell.Free.hierarchy C.labels) _ (Y i d) := (P.aligned d).mono fun _ hi=> hi.orient (Fin.last d)
-- any pathological sampling admits proof via Zoom contradiction.
lemma pull (Q:ℝ→Prop) (ht:∀ R:Zoom,∀ᶠ i in atTop,Q (R.r i)) : ∀ᶠ i in Pilot.trail,Q i:=by
    by_contra hv
    obtain ⟨s,hs,h⟩:= contradictionTrail Q hv
    let H := hs.mono_right nhdsWithin_le_nhds;
    choose g hg he using fun k:ℕ=> ((eventually_gt_atTop k).and (H.eventually (gt_mem_nhds (h k|>.1)))).exists
    let r (k:ℕ):ℕ:= Nat.rec 0 (fun _ x=>g x) k
    have hr:StrictMono r:= strictMono_nat_of_lt_succ fun i=> hg (r i)
    obtain ⟨k,hk⟩:= (ht ⟨s ∘ r,(fun _=>(h _).1), strictAnti_nat_of_succ_lt (fun i=>he (r i)), H.comp hr.tendsto_atTop⟩).exists; exact (h _).2 hk
include P
variable {n:ℕ}{t:Caps n}
lemma anyJets (v:ℝ→Ribbon (Bel C.book) t) (x:Ribbon (Bel C.book) t) (hz : ∀ i: Fin n,Tendsto (fun r => v r i) Pilot.trail (𝓝 (x i)))
 (j:ℕ)(s:Set (Points n))(hs:IsCompact s)(hS:s ⊆ conf n) (ε:ℝ)(he: 0 < ε):
   ∀ᶠ r in Pilot.trail,∀ y∈s,
      ‖iteratedFDeriv ℝ j (fun q=> S.classMoment S t (r • q) (fun i=>Y r (t i) (v r i))) y-
       iteratedFDeriv ℝ j (fun q=>(Bel C.book).classMoment (Bel C.book) t q x) y‖ ≤ ε :=by
   refine pull _ fun R=>?_; exact travels_jet (H₁) F.phase.transport.derivatives (H₀) (Maxwell.Free.scheme_derives C.labels) (edition Y R) (P.continuity R) (v ∘ R.r) x (fun i=>(hz i).comp (tendsto_nhdsWithin_iff.mpr ⟨R.limits,Eventually.of_forall R.positive⟩)) j s hs hS ε he
lemma runs (v:ℝ→Ribbon (Bel C.book) t) (x:Ribbon (Bel C.book) t) (hz : ∀ i: Fin n,Tendsto (fun r => v r i) Pilot.trail (𝓝 (x i))) (s:Set (Points n))(hs:IsCompact s)(hS:s ⊆ conf n) (ε:ℝ)(he: 0 < ε):
    ∀ᶠ r in Pilot.trail, ∀ y∈s,
       ‖S.classMoment S t (r • y) (fun i=>Y r (t i) (v r i))-(Bel C.book).classMoment (Bel C.book) t y x‖ ≤ ε :=by
    filter_upwards [P.anyJets _ _ v x hz 0 s hs hS ε he] with r hr x hx; specialize hr x hx
    rw [show ∀ f g:Points n→ℂ, iteratedFDeriv ℝ 0 f x-iteratedFDeriv ℝ 0 g x= iteratedFDeriv ℝ 0 (f-g) x from fun f g=>ContinuousMultilinearMap.ext (fun p=>by simp),norm_iteratedFDeriv_zero] at hr; exact hr
lemma atTrace (m:ℕ) :∀ᶠ r in Pilot.trail, chores r (Y r 4) m:= by
    have hv: 0<sizeHint m:= inv_pos.mp (cost_pos m)
    have H(n:Fin (m+1)) (v:Fin n→ PegC C 4) (j:Fin (m+1)):=P.anyJets _ _ (fun _=>PoleC C 4 ∘ v) (t:=fun _=>4) (PoleC C 4 ∘ v) (fun i=>tendsto_const_nhds) j (Scaling.window (sizeHint m) n) (window_closed ..) (fun _ hx=> spaced_conf (inv_pos.mpr hv) hx.1) _ (cost_pos m)
    exact eventually_all.mpr fun n=> eventually_all.mpr fun v=> eventually_all.mpr fun i=> H n v i
end Present
end YM.Pier.Lair
