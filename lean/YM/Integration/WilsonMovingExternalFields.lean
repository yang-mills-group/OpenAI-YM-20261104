import YM.Integration.WilsonMixedScaleReportLedger

/-! Every microscopic slot appearing in the actual RG17 product, including
the original fixed exterior fields. The configuration may vary with both
regulators on one common compact subset of the configuration space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingExternalFields
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Table OPE OPE.Orbits
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G) (hG:G.Simple)
    {f:Extraction.Order} {S:Table R.family.book} {F:Spec.Final R.family f S} {n:ℕ}

private theorem regrade {C:Family G} {D H:ℕ} {a:(ℕ×ℕ)→C.label D} {b:C.label D}
    {l:Filter (ℕ×ℕ)} (ha:Tendsto a l (𝓝 b)) (eq:H=D) :
    Tendsto (fun i=>(eq.symm ▸ a i:C.label H)) l (𝓝 (eq.symm ▸ b:C.label H)) := by
  subst D;exact ha

def physical (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d)
    (r:ℝ) (i:(ℕ×ℕ)) (z:Positions (n+X.n)) : ℂ :=
  R.family.numeric i.1 i.2
    (Fin.append (fun j=>(⟨d j,atRef L (d j) r i (w j)⟩:R.family.book.Token)) (refTags X))
    (wrap _ ∘ z)

def limit (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d)
    (r:ℝ) (z:Points (n+X.n)) : ℂ :=
  S.useAt S z (Fin.append (tags (S:=S) (d:=d) (fun j=>master L (d j) r (w j))) X.tags)

include hG in
theorem purchased (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d)
    (r:ℝ) (refs:∀ j,R.family.ref (d j)≤L.level r) (K:Set (Points (n+X.n)))
    (hk:IsCompact K) (sep:K⊆conf _) (ε:ℝ) (he:0<ε) :
    ∀ᶠ i:(ℕ×ℕ) in L.lens,∀z:Positions (n+X.n),tag (R.family.S.a i.1) z∈K →
      dist (physical R L X d w r i z) (limit R L X d w r (tag (R.family.S.a i.1) z)) < ε := by
  letI:=L.notbot
  let bare:=fun j=>S.representative (X.degree j) (X.labels j)
  let b:=joinRef R.family d (e:=X.degree) (fun j=>locatedRef L (d j) r (w j)) bare
  let a (i:(ℕ×ℕ)):=joinRef R.family d (e:=X.degree) (fun j=>atRef L (d j) r i (w j)) bare
  have curr (j:Fin n) : Tendsto (fun i=>atRef L (d j) r i (w j)) L.lens (𝓝 (locatedRef L (d j) r (w j))) :=
    tendsRef L le_rfl (v:=fun _=>w j) tendsto_const_nhds (refs j)
  have rot (j:Fin (n+X.n)) : Tendsto (fun i=>a i j) L.lens (𝓝 (b j)) := by
    cases j using Fin.addCases
    · rename_i j
      simp only [a,b,joinRef,Fin.addCases_left];exact regrade (curr j) (Fin.append_left ..)
    simp only [a,b,joinRef,Fin.addCases_right];exact tendsto_const_nhds
  have hi:=WilsonMovingCalibratedFields.paid R hG F L.certified (Fin.append d X.degree) a b rot K hk sep ε he
  filter_upwards [hi] with i h z hz
  let x:=tag (R.family.S.a i.1) z
  have field:S.value (Fin.append d X.degree) x b=limit R L X d w r x := by
    have hA:=(S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (sep hz)
      (fun j=>(⟨_,b j⟩:R.family.book.Token))).symm
    refine hA.trans (congrArg (S.useAt S x) ?_)
    rw [←pairNames X (fun j=>locatedRef L (d j) r (w j))]
    funext j;cases j using Fin.addCases
    all_goals simp only [Function.comp_apply,Fin.append_left,Fin.append_right,tags,names]
    · rename_i j
      change (⟨d j,S.project _ (locatedRef L _ r (w j))⟩:S.Tag)=_
      rw [payRef]
    change (⟨_,S.project _ (S.representative _ _)⟩:S.Tag)=_
    rw [S.rep];rfl
  have final:=h z hz;rw [field] at final
  unfold physical;rw [pairNames X (fun j=>atRef L (d j) r i (w j))]
  exact final

include hG in
theorem paired (L:Layout F) (X:External R.family S) (d:Caps n) (w:R.family.book.Vector d)
    (r:ℝ) (refs:∀ j,R.family.ref (d j)≤L.level r) (K:Set (Points (n+X.n)))
    (hk:IsCompact K) (sep:K⊆conf _) (ε:ℝ) (he:0<ε) :
    ∀ᶠ i:(ℕ×ℕ) in L.lens,∀z t:Positions (n+X.n),tag (R.family.S.a i.1) z∈K → tag (R.family.S.a i.1) t∈K →
      ‖(physical R L X d w r i z-physical R L X d w r i t) -
       (limit R L X d w r (tag (R.family.S.a i.1) z)-limit R L X d w r (tag (R.family.S.a i.1) t))‖<2*ε := by
  filter_upwards [purchased R hG L X d w r refs K hk sep ε he] with i h z t hz ht
  have a:=h z hz;have b:=h t ht;rw [dist_eq_norm] at a b
  generalize physical R L X d w r i z=p at a ⊢
  generalize physical R L X d w r i t=q at b ⊢
  generalize limit R L X d w r (tag (R.family.S.a i.1) z)=u at a ⊢
  generalize limit R L X d w r (tag (R.family.S.a i.1) t)=v at b ⊢
  rw [show (p-q)-(u-v)=(p-u)-(q-v) by ring]
  exact (norm_sub_le _ _).trans_lt (by linarith)

end YM.Integration.WilsonMovingExternalFields
