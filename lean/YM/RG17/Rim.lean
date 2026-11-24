import YM.RG17.FirstVar
import YM.Trace2.Along

/-!
Fixed-size profile Window round first point in reporting coords. Exact
smeared translation constraint for EVERY such window. In physical uses
scale cutoff with that geometry; annular placement untouched.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open Points Analysis Work.A05 Trace WithLp
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{B:Register G}{S:Table B}

structure Rim where
    test : Test 2
    χ : E4→ℝ
    smooth : ContDiff ℝ ∞ χ
    tight : HasCompactSupport χ
    early : ∀ x∈ tsupport test,Window x χ

namespace Rim
-- The chosen shell can stay fixed throughout a neighborhood of both points
lemma accommodates {z:Points 2}(hz:z∈conf _):∃ U:Set (Points 2),∃ χ, Window z χ ∧ z∈ U ∧ IsOpen U ∧ U⊆conf _ ∧ ∀ x∈ U,Window x χ:=by
    obtain ⟨χ,hχ⟩:= Work.A05.has_window z hz
    have hi:∀ᶠ x in 𝓝 z,χ=ᶠ[𝓝 (x 0)] fun _=>1:=(show Continuous (fun k:Points 2=>k (0:Fin 2)) by fun_prop).continuousAt.tendsto.eventually (eventually_eventuallyEq_nhds.mpr hχ.2.2.1)
    have he:∀ᶠ x in 𝓝 z,∀ i:Fin 1,x i.succ ∉ tsupport χ := eventually_all.mpr fun i=>(show Continuous fun k:Points 2 => k i.succ by fun_prop).continuousAt.tendsto.eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds (show z i.succ∈(tsupport χ)ᶜ from hχ.2.2.2 i))
    have ht: {x:Points 2|x∈conf _∧ Window x χ}∈𝓝 z:= by filter_upwards [(conf_open _).mem_nhds hz,hi,he] with x hx hi he; exact ⟨hx,hχ.1,hχ.2.1,hi,he⟩
    obtain ⟨U,hU,hu,hz⟩:= mem_nhds_iff.mp ht
    exact ⟨U,χ,hχ,hz,hu,fun x hx=>(hU hx).1,fun x hx=>(hU hx).2⟩
variable (N:Rim) (i:Axis)

private def Fm : E4 × Points 2 ≃ᵐ Points 3 := (MeasurableEquiv.toLp 2 _).trans (peel.symm.toHomeomorph.toMeasurableEquiv)
private lemma hc_join : MeasurePreserving Fm (volume.prod volume) volume:= show MeasurePreserving ((peel (n:=2)).symm.toHomeomorph ∘ _) _ _ from (peel (n:=2)).symm.measurePreserving.comp (WithLp.volume_preserving_toLp E4 (Points 2))
private def unite : (E4 × Points 2) ≃L[ℝ] Points (2+1) := (WithLp.prodContinuousLinearEquiv 2 ℝ E4 (Points 2)).symm.trans (peel.symm.toContinuousLinearEquiv)
private lemma unite_at (y:E4)(x:Points 2):unite (y,x)=Points.cons y x := rfl
private lemma divided (z:Points 3) : unite.symm z=(z 0,z.tail):= rfl

def latch (i:Axis)(z: Points 3):ℂ:= N.test z.tail * ↑(Analysis.D (basis i) N.χ (z 0))
private lemma seek : tsupport (latch N i) ⊆ unite '' ((tsupport (Analysis.D (basis i) N.χ)) ×ˢ tsupport N.test):=by
    have hs : HasCompactSupport (Analysis.D (basis i) N.χ) := N.tight.fderiv_apply ℝ _
    apply closure_minimal _ ((hs.prod N.test.hasCompactSupport).image unite.continuous).isClosed
    intro x hx
    have hp:N.test x.tail ≠0 := fun h=> hx (by simp [latch,h])
    have ht:Analysis.D (basis i) N.χ (x 0) ≠0 := fun h=>hx (by simp [latch,h])
    exact ⟨(x 0,x.tail),⟨subset_closure ht, subset_closure hp⟩,unite.apply_symm_apply x⟩

def armed (i:Axis): Test 3:=⟨latch N i,by
    have hs: ContDiff ℝ ∞ (Analysis.D (basis i) N.χ):= (N.smooth.fderiv_right (by simp)).clm_apply contDiff_const
    exact (N.test.contDiff.comp (contDiff_snd.comp unite.symm.contDiff)).mul (Complex.ofRealCLM.contDiff.comp (hs.comp (contDiff_fst.comp unite.symm.contDiff))),by
    have hs : HasCompactSupport (Analysis.D (basis i) N.χ) := N.tight.fderiv_apply ℝ _
    exact (((hs.prod N.test.hasCompactSupport).image unite.continuous).of_isClosed_subset (isClosed_tsupport _) (seek N i)), by
    intro z h; obtain ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩:= seek N i h
    exact Work.A05.window_cons_conf (N.test.tsupport_subset hy) (N.early _ hy) (tsupport_comp_subset (g:=fun f:E4→L[ℝ]ℝ=>f (basis i)) (by simp) _ hx)⟩
lemma armed_at (z:Points 3):N.armed i z=latch N i z:=rfl

abbrev price (w:S.Field 4) (i:Axis) (j:S.Field 4) (r:ℝ) := plate (S:=S) (d:=fun _:Fin 3=>4) ![j,w,w] r (armed N i)
private abbrev picked (J w:S.Field 4) : Fin 3→S.Tag := Fin.cons ⟨4,J⟩ (Fin.cons (α:=fun _:Fin 2=>S.Tag) ⟨4,w⟩ (fun _:Fin 1=>⟨4,w⟩))
private lemma picked_eq (J w:S.Field 4): picked J w=Orbits.tags (S:=S) (d:=fun _=>4) (![J,w,w]) := by funext i; fin_cases i <;> rfl
private def innerTerm (w:S.Field 4) (r:ℝ) (i:Axis) (v:S.Field 4)(x: Points 2) := N.test x * ∫ y:E4, ↑(Analysis.D (basis i) N.χ y) * S.useAt S (r • Points.cons y x) (picked v w)
private lemma price_fold (w:S.Field 4){r:ℝ}(hr:0<r) (i:Axis) (J:S.Field 4) (h:S.Hierarchy) :
    price N w i J r = ∫ x:Points 2,innerTerm N w r i J x := by
    let f (p:Points 3):= N.armed i p * S.useAt S (r • p) (Orbits.tags (S:=S) (d:=fun _=>4) ![J,w,w])
    change (∫ p,f p)= _
    rw [← hc_join.integral_comp Fm.measurableEmbedding (g:=f)]
    have hh:Integrable f:= plate_int _ h (N.armed i) hr
    rw [MeasureTheory.integral_prod_symm (fun x=> f (Fm x)) (hc_join.integrable_comp_emb Fm.measurableEmbedding|>.2 hh)]
    refine integral_congr_ae (Eventually.of_forall fun z=>?_)
    unfold innerTerm
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y=>?_)
    have hs: Fm (y,z)=Points.cons y z:=rfl
    have hu:(Points.cons y z).tail=z:=by ext i; simp [Points.cons,Points.tail]
    unfold f; dsimp only; rw [hs,picked_eq]
    change (N.test (Points.cons y z).tail * ↑(Analysis.D (basis i) N.χ ((Points.cons y z) 0))) * _ = _
    rw [hu, mul_assoc]; rfl
private lemma fold_int (w:S.Field 4){r:ℝ}(hr:0<r) (i:Axis) (J:S.Field 4) (h:S.Hierarchy) :
    Integrable (innerTerm N w r i J) := by
    let f (p:Points 3):= N.armed i p * S.useAt S (r • p) (Orbits.tags (S:=S) (d:=fun _=>4) ![J,w,w]); have hh:Integrable f:= plate_int _ h (N.armed i) hr
    apply Integrable.congr ((hc_join.integrable_comp_emb Fm.measurableEmbedding|>.2 hh).integral_prod_right)
    filter_upwards with z
    change (∫ y:E4,f (Fm (y,z)))=innerTerm ..; unfold innerTerm; rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y=>?_)
    have hs: Fm (y,z)=Points.cons y z:=rfl
    have hu:(Points.cons y z).tail=z:=by ext i; simp [Points.cons,Points.tail]
    unfold f; dsimp only; rw [hs,picked_eq]; change (N.test (Points.cons y z).tail * ↑(Analysis.D (basis i) N.χ ((Points.cons y z) 0))) * _ = _
    rw [hu, mul_assoc]; rfl

-- scales: Ward on Y-sector (L exact fields), all compact shapes within Rim
lemma stress_cut (w:S.Field 4){r:ℝ}(hr:0<r) (h:S.Hierarchy) (D:DiffPlan S) (Y:S.Rotation) (hd:D.Derivatives S)
    (J:S.Stress)(hp: StressLaws S J D.deriv Y.lie) :
    N.test.applyTo (swipe r w w timeAxis) = - ∑ i:Axis, price N w i (r^4 • J i timeAxis) r := by
    simp_rw [price_fold N w hr _ _ h]
    rw [← MeasureTheory.integral_finsetSum _ (fun i _=> fold_int N w hr _ _ h),← MeasureTheory.integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x=>?_)
    by_cases hx:N.test x=0
    · simp only [hx, innerTerm,zero_mul,Finset.sum_const_zero,neg_zero]
    have hx0: x∈tsupport N.test:=subset_closure hx
    have hs:= N.early _ hx0; have he : r • x ∈ conf 2:= smul_conf hr (N.test.tsupport_subset hx0)
    have hv:= (hp.translation he (fun _:Fin 1=>⟨_,w⟩) (window_stretch hr hs) timeAxis _ w).symm
    simp_rw [innerTerm]
    rw [← Finset.mul_sum, ← mul_neg]
    refine congr_arg (N.test x * ·) ?_
    unfold swipe; rw [show derym (r•x) timeAxis w w= _ from (hd.kernels 4 timeAxis w he (fun _:Fin 1=>⟨_,w⟩)).symm,hv, Table.shellGrad,smul_neg,Finset.smul_sum]
    refine congr_arg Neg.neg (Finset.sum_congr rfl fun a _=>?_)
    let X:= J a timeAxis; let A:=picked X w
    have hh:=integrate_sheet_scale hr x A hs.1 a (fun _=>1)
    simp only [sheet,one_smul,Work.A05.weight,stretch,mul_one] at hh
    -- slot linearity
    have hl(y:E4): (r^4:ℝ) • S.useAt S (r • Points.cons y x) (picked X w) = S.useAt S (r • Points.cons y x) (picked (r^4 • X) w):=by
       unfold picked
       simp only [← Work.A01.front_eval]; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [map_smul]
    -- expose integrals
    change r • (∫ y:E4, ↑(Analysis.D (basis a) (stretch r N.χ) y)*Ward.disc A (Points.cons y (r•x)))= (∫ y:E4, ↑(Analysis.D (basis a) N.χ y)*S.useAt S (r • Points.cons y x) (picked (r^4 • X) w))
    rw [show (∫ y:E4, ↑(Analysis.D (basis a) (stretch r N.χ) y)*Ward.disc A (Points.cons y (r•x)))= _ from hh]
    rw [Complex.real_smul, ← mul_assoc, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae; filter_upwards with y
    rw [← hl, Complex.real_smul]; unfold Ward.disc; push_cast; unfold A; ring

-- no conditioning:(unit) times whole untouched at points; integral of
-- window derivative vanishes. thus k in the vacuum stress never measured.
lemma price_unit (w:S.Field 4){r:ℝ}(hr:0<r)(h:S.Hierarchy): N.price w i (S.unit 4) r=0:=by
    rw [price_fold N w hr i _ h]
    refine Eq.trans (integral_congr_ae (μ:=volume) (g:=0) (Eventually.of_forall fun x=>?_)) (integral_zero ..)
    unfold innerTerm
    by_cases hx:N.test x=0
    · simp [hx]
    have hp : x∈tsupport N.test:= subset_closure hx
    let f := Analysis.D (basis i) N.χ
    let s := Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨4,w⟩ (fun _:Fin 1=>⟨4,w⟩)
    let z := S.useAt S (r•x) s
    have hf(y:E4)(hz:f y≠0): Points.cons (r • y) (r • x)∈ conf 3:= by
       rw [← smul_cons]; exact smul_conf hr (window_cons_conf (N.test.tsupport_subset hp) (N.early _ hp) ((tsupport_comp_subset (g:=fun f:E4→L[ℝ]ℝ=>f (basis i)) (by simp) _ (subset_closure hz))))
    let X y := ((f y:ℝ):ℂ)* S.useAt S (r • Points.cons y x) (picked (S.unit 4) w)
    have he : X = fun y=> ((f y:ℝ):ℂ) * z:=by
        funext y; unfold X; by_cases hE:f y=0
        · simp [hE]
        rw [smul_cons,picked,S.at_unit h.laws (hf _ hE)] ; congr 1
    have hφ : (∫ y,f y)=0:=by
        have hC : Integrable N.χ:= N.smooth.continuous.integrable_of_hasCompactSupport N.tight
        have hf : Integrable f := ((N.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport (N.tight.fderiv_apply ℝ _)
        have hd (y:E4): DifferentiableAt ℝ N.χ y:= N.smooth.differentiable (by simp) _
        have hu:= integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (g:=N.χ) (f:=fun _=>(1:ℝ)) (v:=basis i) (μ:=volume) (by simp) (by simpa using! hf) (by simpa using hC) (fun _ _=>differentiableAt_const _) (fun _ _=> hd _)
        simpa using! hu
    change N.test x * (∫ y,X y)=0; rw [he,MeasureTheory.integral_mul_const,integral_complex_ofReal,hφ]; simp

def first_slot (w:S.Field 4){r:ℝ}(hr:0<r) (h:S.Hierarchy)(ψ:Test 3): S.Field 4 →ₗ[ℂ] ℂ where
   toFun J := plate (d:=fun _=>4) ![J,w,w] r ψ
   map_add' x y:=by
       have hv (v):=plate_int (d:=fun _:Fin 3=>4) ![v,w,w] h ψ hr
       unfold plate Test.applyTo; rw [← integral_add (hv _) (hv _)]
       apply integral_congr_ae; filter_upwards with z
       rw [←picked_eq, ←picked_eq, ←picked_eq]; unfold picked; rw [← Work.A01.front_eval, map_add]; rw [Work.A01.front_eval,Work.A01.front_eval,mul_add]
   map_smul' c x:=by
       unfold plate Test.applyTo; change _ = c * _; rw [← MeasureTheory.integral_const_mul]; apply integral_congr_ae; filter_upwards with z
       rw [←picked_eq, ←picked_eq]; unfold picked; rw [← Work.A01.front_eval, map_smul, Work.A01.front_eval,smul_eq_mul,mul_left_comm]

variable {f:Extraction.Order}{S:Table C.book}{F:Final C f S}
abbrev stressBill (L:Layout F) (r:ℝ) (w:S.Field 4) (i:Axis) := N.price w i (tensorRay (portal L) r i timeAxis) r
def Qstress (L:Layout F) (r:ℝ) (w:S.Field 4):= -(∑ i:Axis, N.stressBill L r w i)
def Qscalar (L:Layout F) (r:ℝ) (w:S.Field 4):= -N.price w timeAxis (scalarRay (portal L) r) r

lemma precise (L:Layout F) {a b k r} (hr:0<r) (h : StressRay F (portal L r) r a b k) :
    let p:=scalarRay (portal L) r
    a • N.Qstress L r p + b • N.Qscalar L r p = force (portal L) N.test r p:=by
    intro p
    let Z:=F.room.kernel
    let s (i:Axis):= first_slot p hr Z (N.armed i)
    have ht(i:Axis)(v:S.Field 4):N.price p i v r=s i v :=rfl
    let E:=F.phase.transport
    change _=N.test.applyTo (swipe r p p timeAxis)
    have hv(i):N.price p i (r^4 • F.sector.energy i timeAxis) r = a • N.stressBill L r p i + if i=timeAxis then b • N.price p timeAxis p r else 0 :=by
       rw [h.tensor i timeAxis,ht,map_add,apply_ite (s i)]; simp only [map_add]
       split
       · rename_i he;subst i; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul, ←ht,price_unit _ _ _ hr Z,smul_zero,add_zero]; rfl
       simp only [map_zero,add_zero]; exact ((s i).restrictScalars ℝ).map_smul a ((portal L r) (metric0 C.labels i timeAxis))
    simp_rw [stress_cut N p hr Z F.sector.derivatives F.sector.turns E.derivatives F.sector.energy E.charges,hv]
    unfold Qstress Qscalar
    rw [Finset.sum_add_distrib,Finset.sum_ite_eq', ← Finset.smul_sum]; simp; exact add_comm _ _
end Rim
end YM.RG17

