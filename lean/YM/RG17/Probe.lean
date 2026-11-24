import YM.RG17.Profile

/-!
# Finite smooth exterior probes in unselected S

All probes fixed; z includes the center position. Read in translated
coordinates (center=0). Actual YM kernel, not a PT clustering condition.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)

structure External (C:Family G)(S:Table C.book) where
    n : ℕ
    tags : Fin n → S.Tag
    test : Test (n+1)

namespace External
variable (X:External C S)
def degree (i:Fin X.n):ℕ:= (X.tags i).1
def labels : Labels S X.degree:= fun i=>(X.tags i).2
def offset (x:Points (X.n+1))(i:Fin X.n):E4:= x i.succ - x 0

def pay (d:ℕ)(v:S.Field d)(x:Points (X.n+1)):ℂ := upon S d 0 (X.offset x) X.labels v

-- Translate coordinates; prove exact ambient reading.
include F in
lemma pay_eq (d:ℕ)(v:S.Field d)(x:Points (X.n+1)) (h:x∈conf _) :
    X.pay d v x=S.useAt S x (Fin.cons ⟨d,v⟩ X.tags) :=by
   let a := X.offset x
   let t:= x 0
   let p := fun i:Fin X.n=> x i.succ
   have he : Points.cons t (points p) = x:=PiLp.ext (by intro i; refine Fin.cases ?_ (fun j=> ?_) i; simp [t,Points.cons]; simp [p,Points.cons])
   have hx : Injective (beside (sole t) p):= (consIn (e:=Equiv.refl _) ..).1 (he ▸ h)
   let w :Labels S (fun _:Unit=>d):=sole v
   have hA : (fun i=> beside (sole t) p i + -t)=beside (sole (0:E4)) a := by
       funext i; cases i <;> simp [a,p,sole,sub_eq_add_neg,offset,t]
   have hi: whole S (sole t) w p X.labels = whole S (sole 0) w a X.labels:= by
       unfold whole; rw [← hA]; exact (carrying (hT:=F.room.kernel) (a:=stages w X.labels) hx _).symm
   change whole S (sole 0) w a X.labels = _
   rw [← hi,whole_observed]
   have hz:= head_observe S (names X.labels) (e:=Equiv.refl _) (⟨d,S.representative _ v⟩:C.book.Token) F.room.kernel.laws.toSymmetric hx
   let u := Fin.cons (α:= fun _=> C.book.Token) ⟨d,S.representative _ v⟩ (names X.labels)
   change _= S.read (Points.cons t (points p)) u at hz
   rw [he] at hz
   refine hz.trans ((S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) h u).symm.trans (congr_arg _ ?_))
   funext i; refine Fin.cases ?_ (fun j=>?_) i
   · change (⟨_, S.project _ (S.representative _ _)⟩:S.Tag)= _
     rw [S.rep]; rfl
   simp only [Function.comp_apply,u,Fin.cons_succ]
   change (⟨_, S.project _ (S.representative _ _)⟩:S.Tag)= X.tags j
   rw [S.rep]; rfl

include F in
lemma pay_integrable (d:ℕ)(v:S.Field d) : Integrable (fun x=> X.test x * X.pay d v x) := by
    apply (X.test.smearing (K:= fun x=> S.useAt S x (Fin.cons ⟨d,v⟩ X.tags))
      (show ContinuousOn _ _ from (Next.UVStress.smoothDisc F.room.kernel.smooth _).continuousOn)).congr
    apply Eventually.of_forall; intro x; by_cases h:x∈conf _
    · dsimp only; rw [X.pay_eq F d v x h]
    change X.test x * _= _; simp [X.test.vanishes h]

def charge (d:ℕ): S.Field d →ₗ[ℂ] ℂ where
   toFun v:= X.test.applyTo (X.pay d v)
   map_add' v w:=by
      simp only [Test.applyTo,pay,map_add,mul_add]; exact integral_add (X.pay_integrable F ..) (X.pay_integrable F ..)
   map_smul' c v:=by
      simp only [Test.applyTo,pay,map_smul,smul_eq_mul,mul_left_comm (X.test _)]; exact integral_const_mul ..

-- Uniform room for this one exterior test.
lemma range_open : ∃ δ>0, ∀ x∈ tsupport X.test, ClearOf 0 (X.offset x) δ:=by
    obtain ⟨T,η,hT,hη,hx⟩:= roomCosts (K:=tsupport X.test) X.test.hasCompactSupport X.test.tsupport_subset
    refine ⟨η,hη,fun x hv=>?_⟩
    have hh:= hx 1 (show (0:ℝ)<1 from one_pos) x hv
    constructor
    · intro j
      have h:=hh.spaced 0 j.succ (Ne.symm (Fin.succ_ne_zero j))
      simpa [posed, offset] using h
    intro j k he
    simpa [offset,posed] using (hh.spaced j.succ k.succ (Fin.succ_injective _ |>.ne he))

lemma continuous_offset : Continuous X.offset:=by unfold offset; apply continuous_pi; intros; fun_prop

end External

lemma external_zero {d:ℕ}(v:S.Field d) (h:∀X:External C S,X.charge F d v=0): v=0:=by
   refine S.field_ext F.room.kernel.laws.toSymmetric ?_
   intro n w x hx
   let K(x:Points (n+1)):=S.useAt S x (Fin.cons ⟨d,v⟩ w)
   have hg:ContinuousOn K (conf (n+1)):= (Next.UVStress.smoothDisc F.room.kernel.smooth (Fin.cons ⟨d,v⟩ w)).continuousOn
   have hz:∃ P:S.Field d→ₗ[ℂ] ℂ,∀ v:S.Field d,S.useAt S x (Fin.cons ⟨d,v⟩ w)=P v:=by
      refine ⟨Work.A01.frontRead w x d,fun v=>?_⟩
      exact (Work.A01.front_eval w x _ _).symm
   obtain ⟨L,hL⟩:=hz
   rw [hL 0,map_zero]; apply (Test.weak_null hg).mp _ hx
   intro φ
   let X : External C S:=⟨n,w,φ⟩
   exact (Test.apply_eq φ (fun i hi=> (X.pay_eq F d v i hi).symm)).trans (h X)

open Submodule in
lemma finiteProbes (d:ℕ) : ∃ (R:Finset (External C S))(c:ℝ), 0≤c ∧
     ∀ x:S.Field d, ‖x‖ ≤ c * ∑ X∈R, ‖X.charge F d x‖ := by
   -- finite dimensional compactness of dual problem
   -- use expression of basis coordinates
   let A : External C S→ (S.Field d→ₗ[ℂ] ℂ):= fun X=>X.charge F d
   have hs : Submodule.span ℂ (Set.range A)=⊤:=by
      let V:= Submodule.span ℂ (Set.range A)
      have hs: V.dualCoannihilator=⊥:=by
         apply le_bot_iff.mp; intro x hx; refine (Submodule.mem_bot ..).mpr (external_zero F x fun E=>?_ )
         exact (Submodule.mem_dualCoannihilator _).mp hx (A E) (Submodule.subset_span (Set.mem_range_self _))
      change V=⊤
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=V),hs]; simp
   let B:=Module.finBasis ℂ (S.Field d)
   let I:=Fin (Module.finrank ℂ (S.Field d))
   have hp(i:I): ∃ W:External C S→₀ℂ,Finsupp.linearCombination ℂ A W=B.coord i:=by
       have hx : (Finsupp.linearCombination ℂ A).range = Submodule.span ℂ (Set.range A) := Finsupp.range_linearCombination ℂ
       apply LinearMap.range_eq_top.mp (hx.trans hs)
   choose W hW using hp
   let R:= Finset.univ.biUnion fun i:I=> (W i).support
   let m(i:I):=∑ Z∈(W i).support,‖W i Z‖
   refine ⟨R,∑ i:I,m i*‖B i‖,Finset.sum_nonneg (fun i _=>mul_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (norm_nonneg _)),fun x=>?_⟩
   let D:= ∑ Z∈R,‖Z.charge F d x‖
   have hh(i:I) : ‖(B.coord i) x‖ ≤ m i*D:=by
      rw [← hW,Finsupp.linearCombination_apply]; simp only [Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply]
      unfold m; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun Y h=>?_)
      rw [norm_smul]; exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun Z: External C S=> ‖Z.charge F d x‖) (fun _ _=>norm_nonneg _) (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,h⟩)) (norm_nonneg _)
   change _ ≤ _ * D
   nth_rw 1 [← B.sum_repr x]; rw [Finset.sum_mul]
   refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
   rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)).trans_eq (by ring)
end YM.RG17

