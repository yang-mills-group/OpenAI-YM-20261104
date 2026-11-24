import YM.OPE.Compatible.Assemblage.Perennial

/-! Recomputed words at a step carry honest integrability also on junk
components. No claim that these new junk coeffs test the copies until
passing safe intersections. Not a *uniform* envelope estimate.
-/
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars true
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J N : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{n:Side}
    {R:Rep G n}{d e c a w η α σ T Q b τ:ℝ}
variable {X:Type}[MeasurableSpace X]
variable {B:Census V}
open RG.Envelope
lemma ofCast {f:X→ℝ}(h:Envelope f) : Envelope (fun i:X=> (f i : ℂ)):=by
    obtain ⟨C,hC⟩:=h.cost; refine ⟨Complex.continuous_ofReal.measurable.comp h.meas,C,fun i=>?_⟩; simpa using hC i
abbrev Hover (g:X→Poly B):Prop:=∀ j:B.Mode, Envelope (fun U=> (g U).part j)
lemma Hover.legible {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} (g:X→Poly B)(h:Hover g)(μ:Measure X)[IsFiniteMeasure μ] : Integrable g μ:=by
    exact (MeasureTheory.integrable_pi_iff (E:=fun _: B.Mode=>ℂ)|>.mpr fun i=> (h i).integrableC μ) -- inspect
lemma hovers {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} (g:Poly B) : Hover (fun _:X=>g) := fun _=> Envelope.constC _
lemma hover_cast {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {f:X→ℂ} (h:Envelope f)(b:B.Mode) : Hover (fun i=> Poly.send b (f i)):=by intro j; simp_rw [Poly.part_send]; split; exact h; exact constC _
namespace Hover
variable {g h k:X→Poly B}
lemma plus {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {g h : X → Poly B} (p:Hover g)(q:Hover h):Hover (fun i=>g i+h i):= fun i=> (p i).addC (q i)
lemma negative {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {g : X → Poly B} (p:Hover g):Hover (fun i=>-g i):= fun i=> (p i).negC
lemma minus (p:Hover g)(q:Hover h):Hover (fun i=>g i-h i):=by simp_rw [sub_eq_add_neg]; exact plus p (negative q)
lemma many {V J : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {f:J→X→Poly B}(s:Finset J)(h:∀ i∈s,Hover (f i)):Hover (fun i=>∑ j∈s,f j i):=by intro j; simp_rw [Poly.part_sum]; exact Envelope.sumC s _ fun i hi=> h i hi j
lemma scaleC {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {g : X → Poly B} {f:X→ℂ} (hp:Envelope f)(p:Hover g): Hover (fun U=> f U • g U):=fun i=> hp.mulC (p i)
lemma echo {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {g h : X → Poly B} (p:Hover g)(q:Hover h) : Hover (fun U=> g U*h U):=by
    intro i; simp_rw [Poly.part_mul]; apply Envelope.sumC; intro a _; apply Envelope.sumC; intro b _; split; exact (p _).mulC (q _); exact constC _
lemma repeatP (p:Hover g)(n:ℕ): Hover (fun i=> g i^n):=by induction n with
    | zero=> simp only [pow_zero]; exact hovers _
    | succ n ih=> simp_rw [pow_succ]; exact echo ih p
lemma multipleP {f:J→X→Poly B}(s:Finset J)(h:∀ i∈s,Hover (f i)):Hover (fun i=>∏ j∈s,f j i):=by
    induction s using Finset.induction_on with
    | empty => simp only [prod_empty]; exact hovers _
    | @insert i s hi ih=> simp_rw [prod_insert hi]; exact echo (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma Pass (p:Hover g): Hover (fun i=> Poly.pass (g i)):=many _ (fun i _=> Hover.scaleC (constC _) (Hover.repeatP p i))
lemma flagI {V : Type} [Fintype V] [DecidableEq V] {X : Type} [MeasurableSpace X] {B : Census V} {g : X → Poly B} {Y:X→Prop}[DecidablePred Y](hv:MeasurableSet {x|Y x})(p:Hover g): Hover (fun i=> if Y i then g i else 0):=by
    intro j; have hz:=p j; obtain ⟨C,hC⟩:= hz.cost
    rw [show (fun i:X=>(if Y i then g i else 0).part j)=(fun i=> if Y i then (g i).part j else 0) from funext fun i=> by split <;> rfl]
    refine ⟨Measurable.ite hv hz.meas measurable_const,max C 0,fun i=>?_⟩; split; exact (hC i).trans (le_max_left ..); next=> rw [norm_zero]; exact le_max_right ..
end Hover
lemma flight_grams {V J : Type} [Fintype V] [DecidableEq V] {G : Gauge} {n : Side} {e : ℝ} {B : Census V} {S:J→Support n}{F:J→ Config G n→Poly B}{t:V→ℝ}{m:ℕ}{o:V→Site n}{a c:ℝ}(h:∀ i,Borne o (S i) (F i) a)(hp:Towed t S F m e c)(i:J):Hover (F i):=by
    intro j; obtain ⟨x,_,_,hT⟩:= hp; obtain ⟨v,_,hv,_⟩:= hT i; exact ⟨(h i).me _,v j,fun k=>hv k j⟩
private lemma constant_measures (p:Prop) : MeasurableSet {_t:X | p}:=by by_cases h:p <;> simp [h]
lemma expenses {K:Box n→ Config G n→Poly B}{f: Config G n→Poly B}(hr:R.Lawful σ T Q b τ) (hK:∀ i,Hover (K i))(h:Hover f):Hover (play R B K f):=by
    apply Hover.scaleC (ofCast (R.exponentEnv hr|>.exp)); apply Hover.echo (Hover.Pass h); apply Hover.many
    intro i _; apply Hover.flagI (Y:=fun U=>Pattern (flags R.p.threshold U) i) ?_ (Hover.multipleP i (fun j _=>hK j)); unfold Pattern; exact ((constant_measures _) : MeasurableSet {U:Config G n|(i:Set (Box n)).PairwiseDisjoint Prod.fst}).inter (by simp_rw [@eq_comm _ (Finset.biUnion i _) (flags ..)]; exact flags_measurable_eq ..)
-- used for restored retouch. obtains output slots F/k envelope at step.
variable {Z : V×I→Site n}{l:V×I→ Config G n→ℂ}{k:V×I→ℕ→ Config G n→ℂ}
    {P:Config G n→ Poly (Names V I)}{v:V}{x:V→Site n}{r:V→Motion}{t:V→Equiv.Perm V}{W:V×I→ℝ}{ψ:V×I→ℂ}
lemma kindly (h:Arc R l k P v r x t Z W d e c a η ψ) (hp:R.activities.Valid R.p α σ)
    (hy:∀ U,R.eval U≠0)(hk:∀ i,Dominated (k i))(hv:∀ i U,(P U).part ((Names V I).fire i)=coin R (l i) (k i) U): (∀ i,Envelope (l i))∧(∀ i j,Envelope (profile R.activities (k i) j)):=by
    let B:= Names V I
    obtain ⟨F,Y,χ,hχ,_,ht,he,hF,hZ,_,hI,hJ,hy'⟩:=h.see; let G':= fun i:Config G n=> Mach B ψ+ ∑ j,F j i

    have hh (i:Config G n): (G' i).part B.quiet=0:=by unfold G'; rw [Poly.part_plus,mute,Poly.part_sum,zero_add]; exact sum_eq_zero (fun k _=> (hF k).sil i)
    let K':=closure Y (conviction χ B) Prod.snd R.p.threshold; let f:=G'-kelp χ B
    have hr : P=play R B K' f:=hy'.trans (funext (fun i=> Accent.reversal _ _ _ _ hχ hZ _ (hh i)))
    have hf(i:V×I)(j:Box n): profile R.activities (k i) j=fun U=> (K' j U).part (B.fire i):=funext fun U=> ((posts _ _ _ hZ hI hp U i j).trans (hJ ..)).symm
    have hf' : ∀ U,(f U).part B.quiet=0:=by intro U; simp only [f,Pi.sub_apply,part_sub,kelp,Poly.part_sum,hh,corn_quiet χ B,sum_const_zero,sub_zero]
    have he': ∀ j, Hover (conviction χ B j):=by
        intro j; apply hover_cast (X:=Config G n); obtain ⟨F,hF,-⟩:= hχ.fee j.1;exact ⟨(hχ.yes j.1 j.2).borel,F j.2,(hF _).2⟩
    have hs(i): l i=fun U=> (f U).part (B.fire i):= funext fun U=> (ascent R B K' f U l k hp (fun j=> (Accent.wine Y (conviction χ B) Prod.snd R.p.threshold U j (fun _=>(hZ _).permits _) (corn_quiet χ B U)).trans (hI _ U)) (hf' U) i ((hk i).summable U) (fun j=> congr_fun (hf i j).symm U) (hy U) (congr_arg (fun p=>(p U).part (B.fire i)) hr.symm|>.trans (hv ..))).symm
    constructor
    · intro i; rw [hs]; have hx: Hover G':=Hover.plus (hovers _) (Hover.many _ (fun _ _=> flight_grams (fun i=> (hF i).toBorne) ht _))
      exact Hover.minus hx (Hover.many _ (fun _ _=>he' _)) _
    intro i j; rw [hf]; simp_rw [K',quarters]; exact Hover.many _ (f:=fun x U=>tallyHead Y (conviction χ B) Prod.snd R.p.threshold U j x) (fun z _=> by
       apply Hover.flagI _ (Hover.multipleP _ (fun i _=> match i with | Sum.inl i=>flight_grams (fun i=>(hZ i).toBorne) he _|Sum.inr i=>he' i))
       have h1 : MeasurableSet {U:Config G n| Sealed Prod.snd z} := constant_measures _
       have h2 : MeasurableSet {U:Config G n | flash Prod.snd z=j} := constant_measures _; exact h1.inter (h2.inter (census_me ..))
       ) _
end YM.MergeProof.Ribbons.ManyCopies
