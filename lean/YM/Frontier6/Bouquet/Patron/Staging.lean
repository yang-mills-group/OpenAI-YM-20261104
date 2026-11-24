import YM.Frontier6.Bouquet.Patron.Theater

/-! Cylindrical questions and algebraic linear extension. Outside detector
 clearances the extension maps are only used for arbitrary totalization: they
 won't give physical readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(x:E4)(d:ℕ)

def VisibleMap : Submodule ℂ (Spelling S) where
    carrier:= {v| Visible K x d v}
    add_mem' := fun h he=> Visible.plus K h he
    smul_mem' := fun c v he=> Visible.scale K he c
    zero_mem' := Visible.zero K
def stageMap : VisibleMap K x d →ₗ[ℂ] S.Field d where
    toFun v:= absorb K x d v.val
    map_add' p q:= absorb_plus K p.property q.property
    map_smul' a p:= absorb_scal K p.property a

def Stage : Spelling S →ₗ[ℂ] S.Field d:= stageMap K x d ∘ₗ (LinearMap.exists_leftInverse_of_injective (VisibleMap K x d).subtype (VisibleMap K x d|>.ker_subtype)).choose
def StageWeight : Spelling S→ₗ[ℂ] S.Field d:=(weight K d).toLinearMap ∘ₗ Stage K x d
def stagePart : Spelling S→ₗ[ℂ] Spelling S:= suit K x d ∘ₗ StageWeight K x d
def completeQ : Spelling S→ₗ[ℂ] Spelling S:= deck K x d ∘ₗ Stage K x d
def runOut : Spelling S→ₗ[ℂ] Spelling S:= LinearMap.id-completeQ K x d
variable {x} {v: Spelling S}
lemma stage_value (hv:Visible K x d v): Stage K x d v=absorb K x d v:=by
    let p:= VisibleMap K x d; let h:=LinearMap.exists_leftInverse_of_injective p.subtype p.ker_subtype; let x':p:=⟨v,hv⟩
    change (stageMap K x d) (h.choose (p.subtype x'))=(stageMap K x d) x'; exact congr_arg (stageMap K x d) (DFunLike.congr_fun h.choose_spec x')
lemma stage_weight (hv:Visible K x d v): StageWeight K x d v=Forest.pitch K x d v:=by unfold StageWeight Forest.pitch; simp only [LinearMap.comp_apply]; exact congr_arg (weight K d) (stage_value K _ hv)
lemma stage_part (hv:Visible K x d v): stagePart K x d v= part K x d v:= by unfold stagePart Forest.part; simp only [LinearMap.comp_apply]; exact congr_arg (suit K x d) (stage_weight K _ hv)
lemma stage_all (hv:Visible K x d v): completeQ K x d v= Forest.all K x d v:=by unfold completeQ Forest.all; simp only [LinearMap.comp_apply]; exact congr_arg (deck K x d) (stage_value K _ hv)
lemma run_out (hv:Visible K x d v): runOut K x d v= Forest.reject K x d v:= congr_arg (v- ·) (stage_all K _ hv)

section
variable [Fintype V][DecidableEq V]
variable {r:ℝ}[TopologicalSpace I] {P:Set E4} {A:Art S I}{y:I→ E4}{p:I→ V→ E4}{t:I}
lemma stage_word (hc: Frontier6.Safe K d r)(ht:snug (y t) r (p t))(hy:ContinuousAt y t)(hp:ContinuousAt p t)(v:V→ S.Tag): ContinuousAt (fun i=> Stage K (y i) d (assembly S (p i) v)) t:=by
    let g(z:E4×(V→ E4)):= absorb K z.1 d (assembly S z.2 v); let U: Set (E4 × (V→ E4)):= {z| snug z.1 r z.2}
    have hu : IsOpen U := isOpen_iff_mem_nhds.mpr fun z hz => snug.at continuousAt_fst continuousAt_snd hz
    have hg:ContinuousOn g U:= absorb_continuous K hc hu continuous_fst.continuousOn continuous_snd.continuousOn (fun z hz=>hz) _
    have hz := hg.continuousAt (hu.mem_nhds (show (y t, p t)∈ U from ht)); refine (hz.comp_of_eq (hy.prodMk hp) rfl).congr ((snug.at hy hp ht).mono (fun i hi=>?_)); exact (stage_value K d (snug.apo K (y i) hc hi v)).symm -- func argument val annotate
lemma Appears.purchased (h:Appears P t A)(he:∀ x∈ P, ‖x-y t‖< r)(hy:ContinuousAt y t)(hr:Frontier6.Safe K d r): ContinuousAt (fun i=> Stage K (y i) d (A i)) t:=by
    induction h with
    | say v hv h hp=> exact stage_word K _ hr ⟨h,fun i=> he _ (hp ⟨i,rfl⟩)⟩ hy hv v
    | cf h hv ih=> exact ih.congr (hv.mono (fun i hi=> congr_arg (Stage K (y i) d) hi))
    | vac=> simp_rw [Pi.zero_apply,map_zero]; exact continuousAt_const
    | add _ _ ih jh=> simp_rw [Pi.add_apply,map_add]; exact ih.add jh
    | scale h hi ih=> simp_rw [map_smul]; exact hi.smul ih
end
end YM.Frontier6.Bouquet
