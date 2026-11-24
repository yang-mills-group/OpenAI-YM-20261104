import YM.GradedFar.Physical.Elevation

/-!
# Supplying Ample from the earlier C5 stock hypotheses

Can use ONLY `Answered`-type compact receipts with `d≥6` & positive arities;
lift to use B & Pose & any mixed training jobs. DEMONSTRATE exact term precedent here
for the hypothetical C5 Agenda. Not constructing it. -/
namespace YM.FVA2.GradedFar.Physical.Elevation
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Physical.Round
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p d : ℕ} {I V:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J : FramesH P)
    (hJ: oriented U J)
local notation "F"=> familyPoint U J
-- prove exists first because continuation uses simult; construct by induction on h
lemma payout_down (r: d≤h) (f:Filter I)(D:I→ Normalize.Change G h)(hD:Tendsto (fun i=>guide G h (D i)) f (𝓝 0)) :
    ∃ C : I→ Normalize.Change G d, Tendsto (fun i=> guide G d (C i)) f (𝓝 0) ∧
       ∀ i (a:Sec G d), stand (D i) (up r a)=up r (stand (C i) a) := by
    induction h,r using Nat.le_induction with
    | base => exact ⟨D,hD,fun _ _=> rfl⟩
    | succ k hk ih=>
       let X i:= fell k (D i); let L:= (guide G k).toLinearMap ∘ₗ fell k ∘ₗ (guide G (k+1)).symm.toLinearMap
       have hx:Tendsto (fun i=>guide G k (X i)) f (𝓝 0) := by
          have he:= L.continuous_of_finiteDimensional.continuousAt.tendsto.comp hD; rw [map_zero] at he
          refine he.congr fun i=>?_ ; unfold L X; simp
       obtain ⟨C,hC,h⟩:= ih X hx; refine ⟨C,hC,fun i a=>?_⟩; change stand (D i) (XSpace.Normalize.step k (up hk a))=_; rw [stoop]; change XSpace.Normalize.step k (stand (X i) (up hk a))=_; rw [h i]; rfl
include H hJ
lemma confirm_lift (hr:d≤h)(q k:ℕ) (w:ℝ→ℝ)(E:ℝ→Normalize.Change G d)(D:ℝ→Normalize.Change G h)
    (he:∀ᶠ i in τ,∀ x:Sec G d, stand (D i) (up hr x)=up hr (stand (E i) x)) (v:Tags G d n){X:Set (Points n)} (hx:X⊆conf n) :
      Confirmed N (F h) q k w D X (up hr ∘v) ↔ Confirmed N (F d) q k w E X v := by
   have hp : ∀ᶠ r in τ,∀x∈X,F h r n x (up hr ∘v) - crop q (w r) (Pose.line N x (stand (D r)∘ up hr ∘ v)) =
     F d r n x v - crop q (w r) (Pose.line N x (stand (E r)∘v)) := by
      filter_upwards [he,hJ.raises _ _ hr,self_mem_nhdsWithin] with i ht hz (hi: 0 < i) x he
      rw [line_up N M H x (stand (E i)∘v) hr, show stand (D i)∘up hr ∘v=up hr ∘stand (E i)∘v from funext fun a=>ht (v a)]
      refine congrArg (fun z:ℂ=> z-crop q (w i) (Pose.line N x (up hr ∘ stand (E i) ∘ v))) ?_
      symm; exact painted_rise U J none v (present hi (hx he)) (d':=fun _=>h) (fun _=>hr) (fun j=>hz _)
   exact ⟨fun h=> Terms.tee h (hp.mono fun r hr x=> hr x.val x.property), fun h=> Terms.tee h (hp.mono fun r hr x=> (hr x.val x.property).symm)⟩

/-- Earlier agenda level, common cap `M`, formal read through still-higher.
   A *finite union* of C5 requests with these h0. For compact `Latest` where we
may also need Body.Value with zero arities. -/
def agenda : Prop := ∀ (d n p:ℕ)(v:Tags G d n) (X:Set (Points n)), IsCompact X → X⊆conf n →
   ∃ (k q M h:ℕ) (t':ℝ→ℝ) (D:ℝ → Normalize.Change G M)(hd:d≤M)(h6:6≤M)(hh:M≤h),
    2≤k ∧ p+1≤k ∧ k≤q ∧ Tendsto (fun i=>t' i/gYM G i) τ (𝓝 1) ∧
    Tendsto (fun i=>guide G M (D i)) τ (𝓝 0) ∧
    let T (n:ℕ)(x:Set (Points n))(v:Tags G M n):= Answered N U J v x q k hh t' D
    (∀ i:Fin (N.store.survey 6).n, let w := (N.store.survey 6).scope i; T w.n (tsupport w.t) (up h6∘w.p)) ∧
    (∀ s:XSpace.Rose.Badge, T 3 (tsupport (XSpace.Rose.test N.criterion)) (up h6∘XSpace.Rose.missing (XSpace.Rose.tag G) s)) ∧
    (∀ i:Fin (N.store.survey d).n, let w := (N.store.survey d).scope i; T w.n (tsupport w.t) (up hd∘w.p)) ∧ T n X (up hd∘v)

theorem latest (hA:agenda N U J): Latest N F := by
    intro d n p v X hX hx
    obtain ⟨k,q,d',h,t,D,hv,h6,h',hk,hp,hq,ht,hD,H0,P,H',Hq⟩:= hA d n p v X hX hx
    obtain ⟨C,hC,hC'⟩:= payout_down h6 τ D hD; obtain ⟨B,hB,hB'⟩:= payout_down hv τ D hD
    have h {l a:ℕ}(hr:a≤d'){v':Tags G a l}{S:Set (Points l)}(hs:S⊆conf l)(E:ℝ → Normalize.Change G a)
        (he:∀ i (x:Sec G a), stand (D i) (up hr x)=up hr (stand (E i) x))(h': Answered N U J (up hr ∘v') S q k h' t D): Confirmed N (F a) q k t E S v' :=
       (confirm_lift N M H U J hJ hr q k t E D (Eventually.of_forall he) v' hs).1 (answers N M H U J _ _ q k _ t D h')
    exact ⟨k,q,t,C,B,hk,hp,hq,ht,hC,hB,⟨fun i=> h h6 ((N.store.survey 6).scope i).t.tsupport_subset C hC' (H0 i), fun i=> h h6 (XSpace.Rose.test N.criterion).tsupport_subset C hC' (P i)⟩,
        fun i=> h hv ((N.store.survey d).scope i).t.tsupport_subset B hB' (H' i), h hv hx B hB' Hq⟩
-- mixed two scale comparison. y fixed clearance, already PoseFit gives these approximately after reading true Frame coordinates 
-- carry to any cap `M≥6` by raising W and Test, charge functional directions on larger
lemma older_offer (h0:d≤h)(u v: Toon G d)(j k:ℕ)(t':DataPoint→ℝ)(A B:DataPoint→ Normalize.Change G h)
    (hk : 2≤k)(hk':k≤j)
    (hA: Tendsto (fun i=>guide G h (A i)) filed (𝓝 0))(hB:Tendsto (fun i=>guide G h (B i)) filed (𝓝 0))(ht:Tendsto (fun i=>t' i/gYM G i.1) filed (𝓝 1))
    (he : Buys filed (fun i:DataPoint => P.classMoment (spectator U none) (fun _:Fin (1+1)=>h) (i.1 • rootPoints)
          ((Fin.append (fun _:Fin 1=> J (resize i.1 i.2.val) h (Level.Dial h i.2.val (up h0 (theory u)))) (fun _:Fin 1=> J i.1 h (up h0 (Read.prism (theory v)))))) -
         crop j (t' i) (Pose.line N rootPoints (arms (stand (A i) (up h0 (theory u))) (stand (B i) (up h0 (Read.prism (theory v)))))))
       (fun i=>gYM G i.1) k) : Offered N (F d) (next J d) u v := by
    let X:= up (G:=G) h0; let b:= Read.prism (theory v)
    obtain ⟨C,hC,hc⟩:= payout_down h0 filed A hA; obtain ⟨D,hD,hd⟩:= payout_down h0 filed B hB; refine ⟨j,k,C,D,t',hk,hk',hC,hD,ht,he.congr' ?_ (EventuallyEq.refl ..)⟩
    have hf:Tendsto (Prod.fst:DataPoint→ℝ) filed τ:= tendsto_comap
    let q(i:DataPoint):=i.2.val
    filter_upwards [hf.eventually self_mem_nhdsWithin,hf.eventually (hJ.raises _ _ h0),
       (span_nears _ N M _ q hf (Eventually.of_forall (fun i=> i.2.property)) H).eventually (hJ.raises _ _ h0)] with i (hi: 0 < i.1) hr hk
    let T:=Level.Dial d i.2.val (theory u); let z:=resize i.1 i.2.val; let r:=i.1
    apply congrArg₂ HSub.hSub
    · unfold mix
      let V:= next J d i.1 i.2.val T
      change _= F d i.1 _ rootPoints (arms V b)
      -- move Fd.. up then recover exterior
      rw [show F d i.1 _ rootPoints (arms V b)=F h i.1 _ rootPoints _ from painted_rise (d:=fun _=>d) (d':=fun _=>h) U J none (r:=i.1) (arms V b) (present hi ok_wall) (fun _=> h0) (fun j=>hr _)]
      apply congrArg (P.classMoment _ _ (i.1 • rootPoints)); funext j; fin_cases j
      · change J z _ (Level.Dial h _ _) = J r _ (X V)
        rw [Level.chain]; change J z _ (X T)=_; rw [hr,hk]; apply congrArg _ ; exact (LinearEquiv.apply_symm_apply (J i.1 _) _).symm
      rfl
    apply congr_arg
    simp_rw [hc i, hd i, line_up N M H rootPoints (arms (stand (C i) (theory u)) (stand (D i) (Read.prism (theory v)))) h0]; apply congr_arg; funext j; fin_cases j <;> rfl
end
end YM.FVA2.GradedFar.Physical.Elevation
