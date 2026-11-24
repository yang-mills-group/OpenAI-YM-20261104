import YM.RG11Proof.Fields.Positive
import YM.Pert.Scale.Engineering

/-! Bigraded coordinates for the separated leading physical quotient, not
for a basis selected independently by each scheme from off-shell generators.
View the grading also as doing the accounting on total derivatives (not dropped).
Uses the manuscript radius rescaling on the free fields for homogeneity.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD MvPolynomial YM.Pert.RawLabels
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {F : Frames G} {d e : ℕ}

-- Separate from RStage; no `corners` assertion (for changing bases or
-- compatible nested choices later); AtWeight & Length combined.
structure Adapted (F : Frames G)(d : ℕ) extends Basis F d where
  w (i:toBasis.J) : ℕ×ℕ
  alive (i:toBasis.J) : (writes F d (b i)).IsWeightedHomogeneous compileW (w i)
  heights (i:toBasis.J): (w i).1 ≤ d
  lengths (i:toBasis.J): (w i).2 ≤ d

private theorem cap_length (B : RStage F d)(i) : (B.w i).2 ≤ (B.w i).1 := by
  have hz : writes F d (B.b i) ≠ 0:= (map_ne_zero_iff _ (writes_inj F _)).mpr (B.b.ne_zero i)
  obtain ⟨l,hl⟩ : (writes F d (B.b i)).support.Nonempty := by simpa using hz
  have hp:= B.weighs i (mem_support_iff.mp hl); have hs:=B.length i (mem_support_iff.mp hl)
  rw [←hs,←hp]; simp only [Finsupp.weight_apply,Finsupp.sum,costKey,letterCount,nsmul_eq_mul]
  apply Finset.sum_le_sum; intro s _; gcongr
  linarith

def eachBasis (F:Frames G) (d : ℕ) : Adapted F d where
  toBasis := atStage F d
  w:= (recorded F d).w
  heights:= (recorded F d).cap
  lengths i:= (cap_length (recorded F d) i).trans ((recorded F d).cap i)
  alive i:= fun l hl=> Prod.ext ((weight_collapse l).symm ▸ (recorded F d).weighs i hl) ((weight_collapse l).symm ▸ (recorded F d).length i hl)

-- κ_h,k in the physical quotient only.
private def pure (d:ℕ)(w:ℕ×ℕ):= (MvPolynomial.weightedHomogeneousSubmodule ℂ compileW w).comap (writes F d)

def pr {F:Frames G} (w : ℕ×ℕ) (d:ℕ) : E F d →ₗ[ℂ] WickPol G:= (weightedHomogeneousComponent compileW w).comp (writes F d)

variable (B : Adapted F d)

theorem pr_at (i:B.toBasis.J) (w : ℕ×ℕ) : pr w d (B.b i) = if w=B.w i then writes F d (B.b i) else 0 := by
   unfold pr; rw [LinearMap.comp_apply]
   split <;> rename_i h
   · rw [h,(B.alive i).weightedHomogeneousComponent_same]
   exact (B.alive i).weightedHomogeneousComponent_ne _ h

-- A single homogeneous field uses only these basis indices.
theorem pure_read {p : E F d} {w : ℕ×ℕ} (h : IsWeightedHomogeneous compileW (writes F d p) w)
    (i:B.toBasis.J) (he:B.w i≠w) : B.b.equivFun p i=0:=by
  let P (j:B.toBasis.J):=if B.w i=B.w j then B.b.equivFun p j • B.b j else 0
  have hz : writes F d (∑ j,P j) = 0:=by
    have hl := congrArg (pr (B.w i) d) (B.b.sum_equivFun p)
    rw [_root_.map_sum] at hl ⊢
    simp_rw [_root_.map_smul, pr_at] at hl
    change (∑ j,_)=0
    rw [show (∑ j,writes F d (P j)) = _ from Eq.symm (Finset.sum_congr rfl (fun j _=>show (if B.w i=B.w j then B.b.equivFun p j • writes F d (B.b j) else 0)=_ from by by_cases H:B.w i=B.w j <;> simp only [P,H,_root_.map_smul,↓reduceIte,_root_.map_zero]))]
    simpa only [smul_ite,smul_zero] using hl.trans (h.weightedHomogeneousComponent_ne _ he)
  have hl := (writes_inj F d) (hz.trans (map_zero (writes F d)).symm)
  have ht:=congrArg (fun x => B.b.equivFun x i) hl
  rw [_root_.map_sum,Finset.sum_apply] at ht
  have HH (j:B.toBasis.J): B.b.equivFun (P j) i=if i=j then B.b.equivFun p j else 0 := by
    by_cases hj:i=j
    · subst j; simp [P]
    by_cases hi:B.w i=B.w j <;> simp [hi,P,hj]
  simpa [HH] using ht

theorem enroll_write (F : Frames G) (d : ℕ) (p : Label G d) : writes F d (enroll F d p)=reduceEq p.val := by
  unfold enroll UVNext.FreeStress.embed; rw [LinearMap.comp_apply,writes_project]; change reduceEq ((F.level d).coords.symm ((F.level d).coords p)).val = _; rw [LinearEquiv.symm_apply_apply]

theorem label_writeRaw (F : Frames G) (d : ℕ) (p : E F d) : (physicalLabel F d p).val=writeRaw (writes F d p):=by
   let q:= physicalLabel F d p
   have hz:= enroll_write F d q; rw [show enroll F d q=p from physical_round F p] at hz
   rw [hz,← convertPol]
   have he: fixedPolynomial G d q=q:=by rw [←embed_round F q, show enroll F d q=p from physical_round F p]
   exact congrArg Subtype.val he.symm

theorem basis_label (i:B.toBasis.J): physicalLabel F d (B.b i) ∈ Grade (B.w i) := by
  rw [pure_grade]; unfold pureDegree
  rw [label_writeRaw]
  exact gradeMove compileW bidegree writeRaw (gradientWrite (fun i=> (i+2,1))) _ _ (B.alive i)

lemma pure_label_below (d:ℕ) (p:Label G d) {w:ℕ×ℕ} (hp:p∈ Grade w):
   p.val∈localFields G w.1:= by
  refine ⟨?_,p.property.2⟩
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
  intro v hv; change Labels.height v ≤ w.1
  have ht:= pure_grade w p |>.mp hp (mem_support_iff.mp hv)
  rw [weight_slot v] at ht; exact (show height v=w.1 from congrArg Prod.fst ht).le

lemma stairs (i:B.toBasis.J) (he:(B.w i).1≤e) : B.b i ∈ lower F e d := by
  rw [show B.b i = enroll F d (physicalLabel F d (B.b i)) from (physical_round F _).symm]
  let p:= physicalLabel F d (B.b i)
  have hp := pure_label_below d p (basis_label B i)
  have hl := (raiseLabel G he (⟨p.val,hp⟩:Label G (B.w i).1)).property
  exact ⟨(⟨p.val,hl,p.property⟩: ↥(localFields G e ⊓ localFields G d)), rfl⟩

theorem GM_lower (p : Label G d) (w : ℕ×ℕ) (hp : p∈ Grade w) :
   (reduceEq p.val).IsWeightedHomogeneous compileW w :=
   gradeMove bidegree compileW reduceEq (gradientReduce (fun i=> (i+2,1))) p.val w ((pure_grade w p).1 hp)

theorem small_read (i:B.toBasis.J) (he:e<(B.w i).1) (v:E F d) (hv:v∈lower F e d): B.b.equivFun v i=0:=by
   have hd : e≤d := he.le.trans (B.heights i)
   obtain ⟨q,rfl⟩:=hv
   let f:Label G e:=⟨q.val,q.property.1⟩
   change B.b.equivFun (enroll F d (raiseLabel G hd f)) i = _
   rw [← decompose f]
   simp_rw [_root_.map_sum,Finset.sum_apply]; apply Finset.sum_eq_zero; intro k hk; apply Finset.sum_eq_zero; intro l _
   have hp (w:ℕ×ℕ) : IsWeightedHomogeneous compileW (writes F d (enroll F d (raiseLabel G hd (gradePart w f)))) w:= (enroll_write ..).symm ▸ GM_lower (gradePart w f) w (gradePart_mem ..)
   apply pure_read B (hp (k,l)) i
   intro hq; have ht := congrArg Prod.fst hq
   have hm:=Finset.mem_range.mp hk; dsimp at ht; omega

-- R can be supported using lex(grade,slots); not just engineering.
theorem rotation_pure (F : Frames G) {w : ℕ×ℕ} (s : Ortho) (x:E F d) (h:IsWeightedHomogeneous compileW (writes F d x) w) :
    IsWeightedHomogeneous compileW (writes F d (rideO F s d x)) w:=by
  change IsWeightedHomogeneous _ (writes F d (ride F s d x)) _
  rw [ride_at]; apply gradeMove compileW compileW (pullSol s) ?_ _ _ h
  intro i; rw [pullSol,MvPolynomial.aeval_X]
  unfold symbol; apply MvPolynomial.IsWeightedHomogeneous.sum; intro j _; apply MvPolynomial.IsWeightedHomogeneous.C_mul
  exact isWeightedHomogeneous_X ℂ compileW ⟨_,_⟩

def level (B:Adapted F d) (i:B.toBasis.J):= (B.w i).1*(d+1)+(B.w i).2

theorem mirror_level (a:Axis) {i j:B.toBasis.J} (he:level B i<level B j): frameMirror B.toBasis a i j=0:= by
  have hr: B.w i ≠ B.w j:= fun h=>by unfold level at he; simp_rw [h] at he; omega
  unfold frameMirror; rw [Matrix.of_apply]; unfold Basis.coord
  unfold Table.adj; rw [LinearMap.comp_apply,B.pinned]
  rw [show (freeTable F).mirror _ _ _ _ = _ from Pert.Rigid.wear_ride F (Signed.mirror a) (B.b i)]
  rw [pure_read B (rotation_pure F _ _ (B.alive i)) j hr.symm]; rfl

-- Connect `Positive` at every free field horizon to `leading_of_paired`
end YM.RG11.Fields
