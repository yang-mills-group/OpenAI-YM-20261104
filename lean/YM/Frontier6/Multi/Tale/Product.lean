import YM.Frontier6.Multi.Tale.Chart

/-!
# Observable absolute anchored fields. Finite linear operations only on valid samples,
including Haar costs prior to row extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Tale
open Function Set Finset Filter Spec
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {V X:Type*}[Fintype V][DecidableEq V][TopologicalSpace X] {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K: Final C F S)(c:E4) (d:ℕ)
set_option quotPrecheck false

def album (d:ℕ) (A:Spelling S): Palette K d:= display K d (written K c A)
def absorb (d:ℕ) (A:Spelling S): S.Field d:= capture K d (written K c A)
abbrev Visible (d:ℕ) (A:Spelling S):Prop:= observable K d (written K c A)
lemma bye_span (z:ℕ) (b:S.Field z) : Illuminates K d (written K c (letter S c ⟨z,b⟩)) (reaches K d z b):=by
    constructor; intro i p a g; rw [reaches_at]; let Y:=(p.val.flip K a).roll K g; exact (read_letter K none c z b Y.clear _).symm
lemma apo_letter (t:S.Tag): Visible K c d (letter S c t):=⟨_,bye_span K c d t.1 t.2⟩
lemma absorb_letter (b:S.Field d): absorb K c d (letter S c ⟨d,b⟩)=b:=by unfold absorb capture; rw [display_on K (bye_span K c d d b)]; exact detector_field ..
lemma united {n:ℕ} (u:StateIndex K) (x:V→ E4)(v:V→ S.Tag) (s:Fin n → S.Tag) (y:Points n): written K c (assembly S (fun i=>x i+c) v) u n y s= written K 0 (assembly S x v) u n y s:=by
   change poll _ _ (_* assembly S _ s)=poll _ _ (_* assembly S _ s)
   simp only [add_zero]; rw [←concatenates,← concatenates];
   rw [show Sum.elim (fun i=>x i+c) (fun i=>y i+c)=(fun i=> Sum.elim x (fun i=>y i) i+c) from (by ext1 z; cases z <;> rfl), translating K]

variable {d c} {u v: Spelling S}
lemma Visible.low {w:ℕ}(he:w≤d)(h: Visible K c d u): Visible K c w u:=observable_down K h he
lemma absorb_lower {w:ℕ}(he:w≤d)(h: Visible K c d u): projectBelow K he (absorb K c d u)= absorb K c w u:=capture_lower K h he
lemma Visible.cf (h: Visible K c d u)(hz:Congr K u v): Visible K c d v:=by unfold Visible; rw [← readout K c u v hz]; exact h
lemma absorbed (d:ℕ)(c:E4)(h:Congr K u v): absorb K c d u=absorb K c d v:= congr_arg (capture K d) (readout K c u v h)
lemma matches_plus (h:Visible K c d u)(he:Visible K c d v): Illuminates K d (written K c (u+v)) (album K c d u+album K c d v):=by
    constructor; intro i p a g; change (album K c d u i p a g)+(album K c d v i p a g)=_
    unfold album; rw [(displayed K h).seats,(displayed K he).seats, map_add]; rfl
lemma Visible.plus (h:Visible K c d u)(he:Visible K c d v): Visible K c d (u+v):=⟨_,matches_plus K h he⟩
lemma absorb_plus (h:Visible K c d u)(he:Visible K c d v): absorb K c d (u+v) = absorb K c d u+absorb K c d v:=by unfold absorb capture; rw [display_on K (matches_plus K h he),map_add]; rfl
lemma matches_scal (h:Visible K c d u)(a:ℂ): Illuminates K d (written K c (a•u)) (a • album K c d u):=by constructor; intro i p b g; change a • album K c d u i p b g=_; unfold album; rw [(displayed K h).seats, map_smul];rfl
lemma Visible.scale (h:Visible K c d u)(a:ℂ): Visible K c d (a•u):=⟨_,matches_scal K h a⟩
lemma absorb_scal (h:Visible K c d u)(a:ℂ): absorb K c d (a • u)=a • absorb K c d u:=by unfold absorb capture; rw [display_on K (matches_scal K h a),map_smul]; exact rfl
lemma Visible.sub (h:Visible K c d u)(he: Visible K c d v): Visible K c d (u-v):= by rw [sub_eq_add_neg, ← neg_one_smul ℂ]; exact h.plus K (he.scale K _)
lemma absorb_sub (h:Visible K c d u)(he:Visible K c d v): absorb K c d (u-v)=absorb K c d u-absorb K c d v:=by rw [sub_eq_add_neg u,← neg_one_smul ℂ, absorb_plus K h (he.scale K _), absorb_scal K he,neg_one_smul,sub_eq_add_neg]
lemma matches_null : Illuminates K d (written K c 0) 0:= ⟨fun i p b g=>by rw [map_zero];rfl ⟩
lemma Visible.zero : Visible K c d 0:=⟨_, matches_null K⟩
lemma absorb_zero : absorb K c d 0=0:=by unfold absorb capture; rw [display_on K (matches_null K),map_zero]
lemma Visible.sum {u:V→Spelling S}(s:Finset V)(he:∀ i∈s,Visible K c d (u i)): Visible K c d (∑ i∈s,u i):=by induction s using Finset.induction_on with
    | empty=> rw [Finset.sum_empty];exact zero K
    | @insert i s h ih=> rw [Finset.sum_insert h]; exact (he i (mem_insert_self ..)).plus K (ih (fun i hi=> he _ (mem_insert_of_mem hi)))
lemma absorb_many {u:V→Spelling S}(s:Finset V)(he:∀ i∈s,Visible K c d (u i)): absorb K c d (∑ i∈s,u i)=∑ i∈s,absorb K c d (u i):=by induction s using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact absorb_zero K
    | @insert i s h ih=> have hr j (hj:j∈s):= he j (mem_insert_of_mem hj); rw [Finset.sum_insert h, Finset.sum_insert h, absorb_plus K (he i (mem_insert_self ..)) (Visible.sum K s hr),ih hr]

lemma visibles (X:V→ E4) {r:ℝ} (he: Frontier6.Safe K d r)(hv:Injective X)(hp:∀ i,‖X i-c‖ ≤ r)(v:V→S.Tag): Visible K c d (assembly S X v):=by
   let f:= written K c (assembly S X v)
   suffices hh:∀ p:Probe S, clearC r p.exterior → Continuous (fun g=>(p.roll K g).tip K f) by exact ⟨fun i p b=> ⟨_,hh (p.val.flip K b) (flip_safe K p.val (he i p) b)⟩, ⟨fun i p b g=>rfl⟩⟩
   intro p hr
   let Z:= V⊕ Fin p.length; let d (i:Z):= Sum.elim (fun i=>(v i).1) (fun i=>(p.letter i).1) i;
   let y(g:Ortho):Z→ E4:= Sum.elim X (fun i=>(p.roll K g).exterior i+c); let F(g:Ortho)(i:Z):S.Field (d i):=Sum.rec (motive:=fun i=>S.Field (d i)) (fun i=>(v i).2) (flying K p g) i
   let P(g):= assembly S (y g) (fun i=> ⟨d i,F g i⟩); have hP(g:Ortho): (p.roll K g).tip K f=poll S (state K none) (P g):=by
      change poll S (state K none) (_ * assembly S (fun i=>(p.roll K g).exterior i +c) (p.roll K g).letter) =_
      rw [← concatenates]; apply congr_arg (poll S (state K none)); apply congr_arg (assembly S (y g)); ext1 i; rcases i with i|i <;> rfl
   have hX:Continuous y:= continuous_pi fun i=>by rcases i with i|i; exact continuous_const; exact ((PiLp.continuous_apply ..).comp (spinner p.exterior)).add continuous_const
   have hF:Continuous F:=continuous_pi fun i=> by rcases i with i|i; exact continuous_const; exact (continuous_apply i).comp (fly_cont K p)
   have hg(g:Ortho):Injective (y g):=by
      let W:= p.roll K g; have hk : Injective W.exterior.ofLp:= (Points.tail_in W.clear); have he(j) := clear_exterior (roll_safe K p hr g) j
      have hy(i j)(h:X i= W.exterior j+c):False:= by have hz:= hp i; rw [h,add_sub_cancel_right] at hz; exact not_le.mpr (he j) hz
      rintro (i|i) (j|j) h; exacts [congr_arg _ (hv h), (hy i j h).elim, (hy j i h.symm).elim, congr_arg Sum.inr (hk (add_right_cancel h))]
   simp_rw [hP]; exact continuous_iff_continuousAt.mpr fun g=> Inspect_cont K none d hX.continuousAt (hg g) hF.continuousAt
end YM.Frontier6.Tale
