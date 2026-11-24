import YM.RemainderComparison.Solos.Hues
/-!
# Held-test qlocal push — STATIC collars in each marked word before summation

Use mould `Lesson`: families reporting over T with pointwise integral congruence; graded by
slot occurrence WORD (not just set of marked positions). VerifiedReset predictor has same rules
inside regular good chart and WHOLE forced bits. Including absent/gasKey as well as repeated
letters. The uniform comparison budgets alone don't give these equalities.

Extension of the supplied RemainderComparison/Solos/Hues, here generalized in budget and also
checking each genuine stencil's provenance, reusing its uniform dominator and local-continuation
proofs. Global captions have no flagged extension costs in this argument.

As a tidy diagnostic: `.dew` gives ALL held properties on an open neighborhood of every healthy
field. This avoids losing linearity of germs exactly at boundary by inferring more than what the
mask permits. No assertion about the unmasked nominal solutes everywhere at every step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Collar
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
open Solos (tart)
variable (M:ι→Portrait R α)
structure Lesson (ι:Type)(α:Type*) where
    Knows : Multiset ι → (α→ℝ)→ Prop
    pitch {q:Multiset ι}{F:α→ℝ} (a: ℝ) : Knows q F→ Knows q (fun x=> a*F x)
    choir {q:Multiset ι}{f g:α→ℝ}: Knows q f → Knows q g→ Knows q (fun x=> f x+g x)
    nil (q:Multiset ι) : Knows q (fun _=>0)
    constant : ∀ a:ℝ, Knows 0 (fun _=>a)
    shares {p q:Multiset ι}{f g:α→ℝ}: Knows p f→ Knows q g → Knows (p+q) (fun x=> f x*g x)
    meal {σ:Type}[MeasurableSpace σ] {μ:Measure σ} {s:Multiset ι} {F:σ→α→ℝ} :
           (∀ i,Knows s (F i)) → (∀ t,Integrable (fun i=>F i t) μ) → Knows s (fun t=> ∫ i,F i t ∂μ)
namespace Lesson
variable (L':Lesson ι α)
lemma seats {q:Multiset ι}{υ:Type*}(s:Finset υ)(F:υ→α→ℝ) (h:∀ i∈s,L'.Knows q (F i)) : L'.Knows q fun i=>∑ j∈s,F j i:=by
    induction s using Finset.induction with
    | empty=> simp_rw [sum_empty]; exact L'.nil q
    | insert i s hi he=> simp_rw [sum_insert hi]; exact L'.choir (h i (mem_insert_self _ _)) (he fun j hj=> h j (mem_insert_of_mem hj))
lemma stack {υ:Type*}(s:Finset υ)(r:υ→Multiset ι)(F:υ→α→ℝ) (h:∀ i∈s,L'.Knows (r i) (F i)) : L'.Knows (∑ i∈s,r i) (fun i=>∏ j∈s,F j i):=by
    induction s using Finset.induction with
    | empty=> rw [sum_empty]; simp_rw [prod_empty]; exact L'.constant 1
    | insert i s hi he=> rw [sum_insert hi]; simp_rw [prod_insert hi]; exact L'.shares (h i (mem_insert_self _ _)) (he fun j hj=> h j (mem_insert_of_mem hj))
end Lesson
open Solos (tart)
variable (M:ι→Portrait R α)
variable (Ll:Lesson ι α) (Hpc: ∀ (U:Config G f) i, Ll.Knows {i} (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
variable (y:α)(X:Coat T F) (i:Drums (brand M y) S)
local notation "q'"=> i.val.val
private lemma noteEq (p:Finset ι): p.val=∑ i∈p,({i}:Multiset ι):= by
   induction p using Finset.induction with
   | empty=>simp
   | insert i s hi he=> rw [sum_insert hi, Finset.insert_val_of_notMem hi, show ({i}: Multiset ι)+(_)=i ::ₘ ∑ i∈s, ({i}:Multiset ι) from Multiset.singleton_add _ _,← he]
include Hpc
lemma syllabic (U:Config G f) : Ll.Knows q' (fun a=> (team (brand M a) i).ingredients U):=by
    unfold Team.ingredients; have hx(z:α): (∏ j∈(team (brand M z) i).own,j.ingredient U)= ∏ j∈i.val,(brand M z j).ingredient U:= Solos.shape _ _ _
    simp_rw [hx, noteEq i.val]
    apply Ll.stack
    intro k _; exact Hpc U k
lemma words (p:Directions G f) (v:ℝ) : Ll.Knows q' (fun u=> (team (brand M u) i).paidU X v p):=by
    unfold Team.paidU; have hx(z:α): (∏ j∈(team (brand M z) i).own,j.paidU X v p)= ∏ j∈i.val,(brand M z j).paidU X v p:= Solos.shape _ _ _
    simp_rw [hx, noteEq i.val]; apply Ll.stack
    intro j _; unfold Leaf.paidU Leaf.fond; let c':= X.enforce (2*v) p (X.plaza (areas R T 0 X.B ((brand M y j).turn.badge S)))
    have hz(z:α): (brand M z j).turn=(brand M y j).turn:=rfl
    change Ll.Knows {j} (fun z=> (brand M z j).ingredient (X.input p)*c')
    simpa only [mul_comm] using (Ll.pitch c' (Hpc (X.input p) j))
lemma solar (V: Config G c)(p:Molecule S)(I':Finset (Bond f))(b:F.Slice G×Air f G) : Ll.Knows q' (fun a=> (team (brand M a) i).carat I' X V v Ñ p W r m b):=by
    let Y:= vary (X.wrapY b.1) V
    apply Ll.pitch; unfold Team.floret
    -- rw common reach in lambda
    have he (z:α): (team (V' z) i).signs S=i.reach:= Palette.label _ _
    simp_rw [he]; split_ifs; next he=>
      let c':= floating Y r R W Ñ (course (X.wrapY b.1) v R.beta b.2 V) (Matter.own p) m (p\i.reach)
      simp_rw [mul_comm _ (floating (vary _ _) _ _ _ _ _ _ _ (p\i.reach))]; exact Ll.pitch _ (words M Ll Hpc y Y i _ _)
    next=> exact Ll.nil _

lemma heat(X:Coat T F) (H:Cash W X.x μ L Q o C T R) (hr:X.width=o.K)(hp:X.manifest)(K: Finset ℕ) (p:Molecule S): Ll.Knows q' (fun a=> (team (brand M a) i).tithe X K W o.a Q.table Q.halo p):=by
    apply Ll.meal (F:=fun (v:F.Slice G × Air f G) a=> (team (brand M a) i).into X W o.a Q.table K Q.halo p v)
    · intro v
      unfold Team.into Team.premium
      have he (z:α): (team (V' z) i).signs S=i.reach:= Palette.label _ _
      simp_rw [he]; split_ifs
      next h=> simp_rw [mul_comm _ ((X.wrapY v.1).term R Q.table W o.a K Q.halo v.2 (p\i.reach))]
               exact Ll.pitch _ (words M Ll Hpc y _ _ _ _)
      exact Ll.nil _
    intro V; exact ((team (V' V) _).tip X K H hr hp p).2.1

set_option maxHeartbeats 200000 in
lemma act_h (p: Molecule S) (V: Config G c): Ll.Knows q' (fun a=> Palette.act (brand M a) H χ V p i):=by
    let X (r:Greenbelt.Reserve S):= prism T x χ o.K V (allot r)
    unfold Palette.act Team.lotus likely; apply Ll.pitch; apply Ll.seats (F:=fun r a=> (team (V' a) i).bloom (X r) W o.a Q.table Q.halo p)
    intro r _; unfold Team.bloom; split_ifs
    next=>
      unfold Team.steep likely; apply Ll.pitch; apply Ll.seats (F:=fun z a=> (team (V' a) i).tithe (((planted (X r) p)).taggedL z) (Matter.own p) W o.a Q.table Q.halo p); intro j _
      exact heat M Ll Hpc y i (((planted (X r) p)).taggedL j) H rfl (planted_valid (X r) p) (Matter.own p) p
    next=> exact Ll.nil _
end YM.RemainderComparison.Collar

