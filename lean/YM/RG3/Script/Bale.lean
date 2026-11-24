import YM.RG3.Script.Florist

/-! # Keeping all support reserves on the re-closed sections.
Recover proportional marker costs `w s`. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Edition
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n : Side} {V : Type} [DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge}
 {P : Rep G n}{d : Deck R P}{e : Edition ζ R G}{D:V→ℕ}{H : Hol G}{X:(s:V)→Labels.Frame G (D s)}{L:(s:V)→SectionData (X s)}
 {k : V→ℝ}
variable (hr: ∀ s, Readable H (L s) P.p n (k s))(hz:d.contents.origins=ζ)(he:d.Active)(h:e.Principle P.p)
  {a δ : ℝ}{m : ℕ→ℝ}{w:V→ℝ}(hl: Loaded H a m δ L d e k w)(hw: ∀i,0<w i)
include hr hz he h hl hw

abbrev stageCost (k w:V→ℝ)(δ:ℝ)(i:V): ℝ := k i * (δ/(w i))

def palm (e:Edition ζ R G)(d:Deck R P)(H:Hol G)(k:V→ℝ)(m f:ℕ→ℝ) (X:(s:V)→Labels.Frame G (D s)) (i:ℕ) :=
    (e.shaft i).elim (f i) (fun s=>Primary.ink (F:=X s) s (e.scribe d) H (k s) m i)
abbrev jointFeed (i:V) (d:Deck R P)(e : Edition ζ R G)(L:(s:V)→SectionData (X s))(H:Hol G)(hr:∀ s, Readable H (L s) P.p n (k s)):=feeds i (e.scribe d) H (L i) (hr i|>.sound.anchored)

lemma trunk (hg:P.p.supportExponent+1 ≤ a)(s):
    (jointFeed s d e L H hr).Worth w P.p.B (P.p.supportExponent+1) (Primary.ink (F:=X s) s (e.scribe d) H (k s) m) δ ∧
      0≤δ ∧ (X s).coeffSize ((X s).core (petition (X:=X) e H d s)) ≤ δ/(w s) ∧ w s*‖petition (X:=X) e H d s 0‖ ≤ δ ∧
        (X s).coeffSize (petition (X:=X) e H d s) ≤ δ/(w s) := by
  have ha:= authorized hz h he
  have hv:=demand hr hl hw hg s
  have he':=(hv.combine hw (hr s) ha).2
  refine ⟨hv.purchase hw (hr s) ha,budget_nonneg hv.2,(Work.G08.size_core ..).trans he',?_,he'⟩
  exact (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (petition (X:=X) e H d s) _).trans ((norm_le_size ..).trans he')) (hw s).le).trans_eq (by field_simp [(hw s).ne'])

variable {f:ℕ→ℝ}{u v γ Y : ℝ}
variable (hb:e.Grant P.p w a u v Y f)
include hb
omit he hz in
lemma lower_reg (hg:P.p.supportExponent+1 ≤ a) (i:ℕ):
    let S:= tent e L d i; let F := display e H L d i; let C := palm e d H k m f X i
    0 ≤ C ∧ ∀ s∈ (e.pins i).val, P.p.supBounds (ζ s) S F C:= by
  intro S F C
  cases ht:e.shaft i with
  | none=>
    rw [show C=f i from by simp [C,palm,ht]]; unfold S F; rw [(grass (e:=e) (L:=L) (d:=d) H ht).2,(grass (e:=e) (L:=L) (d:=d) H ht).1]; exact ⟨hb.nn _,hb.pay _⟩
  | some t=>
    have hp:e.only i t:=e.from_shaft ht
    unfold C F S palm; rw [ht,(blossom H ht).2,(blossom H ht (L:=L) (d:=d)).1]
    refine ⟨(demand hr hl hw hg t).positive (hr t) i, fun s hs=>?_⟩
    rw [show e.pins i =_ from hp] at hs; have H' :=mem_singleton.mp hs; subst s
    unfold Primary.grows Primary.fires Primary.ink
    have hh : Primary.earns t (e.scribe d) i := hp; rw [if_pos hh,if_pos hh]; dsimp only [Option.elim]; rw [if_pos hh]
    exact (charge_atom _ (hr t) (h.reg i) (hl.1 _ _ hp)).1

-- h upper section footprint times k at required exponent
variable [Fintype V]
lemma stored (hg:P.p.supportExponent+1 ≤ a) {K:ℝ} (hK:∀ i,expense P.p.B a ((L i).footprint (ζ i)) (k i) ≤ K):
    let q:= sprayed e H L d; let b:=shuffle (stageCost k w δ) (palm e d H k m f X)
    q.Grant P.p w a (u+δ) ((v+δ)+K*δ) Y b:= by
  intro q b
  have hi i := trunk hr hz he h hl hw hg i
  have ht i := (hr i).nonneg
  have hh i := lower_reg hr h hl hw hb hg (d:=d) i -- arguments after omit
  have ha i : P.p.supBounds (ζ i) ((L i).footprint (ζ i)) (signal i (e.scribe d) H (L i)) (stageCost k w δ i):= bound_weaken ((presented_good _ (hr i) _).2) (mul_le_mul_of_nonneg_left (hi i).2.2.1 (ht i))
  have Hk (i : V) (_hj:i∈Set.univ) : 0 ≤ K:= le_trans (show 0≤expense P.p.B a ((L i).footprint (ζ i)) (k i) from mul_nonneg (Real.exp_pos _).le (ht i)) (hK i)
  refine ⟨fun i=>?_ ,fun i=>?_ , fun i=>?_,fun s=>?_,hb.captions⟩
  · change w i * ‖_ + _‖ ≤ _; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (hw i).le).trans (by rw [mul_add]; exact add_le_add (hb.one _) (hi i).2.2.2.1)
  · cases hy:numbering (V⊕ℕ) i with
    | inl i=> simpa only [b,revive hy] using (ha i).1
    | inr i=> simpa only [b,corsage hy] using (hh i).1
  · cases hy:numbering (V⊕ℕ) i with
    | inl i=>
      unfold q b sprayed; rw [revive hy]; simp only [revive hy]
      intro j hj; obtain rfl:=mem_singleton.mp hj; exact ha _
    | inr i=>
      unfold q b sprayed; simp only [corsage hy]
      exact (hh i).2
  let cd:=expense (n:=n) P.p.B a
  let fg (i:V):= if s=i then w s * cd ((L i).footprint (ζ i)) (stageCost k w δ i) else 0
  let fo:= per P.p.B a w e.pins (tent e L d) (palm e d H k m f X) s
  have hF:(per P.p.B a w q.pins q.home b s)=shuffle fg fo := by
    ext1 i; cases hy:numbering (V⊕ℕ) i with
    | inl i=> simp only [q,per,b,sprayed,revive hy,fg,Poly.solo_toll]; split_ifs with H H' H' -- goal eq costs on i when H:s∈...
              · subst i; rfl
              · exact (H' (mem_singleton.mp H)).elim
              · exact (H (mem_singleton.mpr H')).elim
              rfl
    | inr i=> simp only [q,per,b,sprayed,corsage hy,fo]
  rw [hF,add_comm (v+δ)]
  have hr1 : SumBudget fg (K*δ):= Budget.certify (fun j=>by
    unfold fg; split
    next _=> exact mul_nonneg (hw _).le (mul_nonneg (Real.exp_pos _).le (ha _).1)
    exact le_rfl) (fun t=>by
    by_cases he : s∈t
    · rw [Finset.sum_eq_single s (fun j _ hj=> if_neg (show ¬s=j from Ne.symm hj)) (fun he'=> (he' he).elim)]
      rw [if_pos rfl]; unfold cd expense stageCost
      exact (le_of_eq (show w s*(Real.exp _*(k s*(δ/w s)))=expense P.p.B a ((L s).footprint (ζ s)) (k s) *δ by unfold expense; field_simp [(hw s).ne'])).trans (mul_le_mul_of_nonneg_right (hK _) (hi s).2.1)
    rw [show (∑ i∈t,fg i)=(0:ℝ) from Finset.sum_eq_zero (fun i hi=> by apply if_neg; exact fun H=>he (H.symm ▸ hi))]; exact mul_nonneg (Hk s trivial) (hi s).2.1)
  have hr2 : SumBudget fo (v+δ):= by
    refine budget_mono (budget_plus (hb.more s) (hl.2 s)) (fun i=>per_nn (fun i=>(hw i).le) (fun i=> (hh i).1) _ _) (fun i=>?_)
    unfold fo per
    split
    next hS=>
      cases ht:e.shaft i with
      | none=> rw [palm,tent,ht]; exact le_add_of_nonneg_right ((hl.2 s).1 _)
      | some j=>
        have hp:e.only i j:=e.from_shaft ht
        rw [show e.pins i=_ from hp] at hS
        have hj:= mem_singleton.mp hS; subst s
        have he0:= per_nn (j:=e.pins) (X:=e.home) (B:=P.p.B) (a:=a) (fun i=>(hw i).le) hb.nn i j
        rw [per,if_pos (show j∈(e.pins i).val from (hp ▸ mem_singleton_self _))] at he0
        apply le_trans _ (le_add_of_nonneg_left he0); rw [show e.pins i=_ from hp,Poly.solo_toll,tent,palm,ht,paidR]; refine le_of_eq ?_
        unfold veil Primary.grows; simp only [Option.elim]; rw [if_pos (show Primary.earns j (e.scribe d) i from hp)]
    exact le_add_of_nonneg_right ((hl.2 s).1 _)
  exact Cost.equiv _ (Cost.sum (f:=Sum.elim fg fo) hr1 hr2)
end YM.RG3.Script.Edition
