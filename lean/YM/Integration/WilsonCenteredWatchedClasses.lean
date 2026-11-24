import YM.Integration.WilsonCenteredWatchedLimit

/-! The original quotient-field labels and the actual calibrated cutoff
detector have the same held test on every separated near placement. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredWatchedClasses
open Function Set MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open OPE OPE.Orbits Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching
open WilsonCenteredWatchedShape WilsonCenteredWatchedCylinder WilsonCenteredWatchedLimit
open WilsonMacroscopicRichWatchReader WilsonMacroscopicRichWatchPlot
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n:ℕ} {f:Extraction.Order} {S:Table R.family.book}

def lift (d:Fin n→ℕ) (v:Labels S d) : ∀j,R.family.label (d j) :=
  fun i=>S.representative _ (v i)

theorem literal (F:Spec.Final R.family f S) {a:ℕ} (W:Fin a→Watch R.family) (i:Fin a)
    (d:Fin n→ℕ) (v:Labels S d) (r:ℝ) (x:Points n) (clear:joint (W i) r x∈conf _) :
    S.read (joint (calibrated S (W i)) r x)
      (WilsonCenteredWatchedCylinder.tags R d (lift R d v) (calibrated S (W i))) =
    current W (r • x).ofLp v i :=by
  let w:=W i
  let e:=(exterior S w)
  let E : Fin n ⊕ Fin e.length ≃ Fin (n+w.n) :=
    (Equiv.sumCongr (Equiv.refl _) (index S w).symm).trans finSumFinEquiv
  let q : Fin (n+w.n)→R.family.book.Token := Fin.append (fun j=>⟨d j,lift R d v j⟩)
    (fun j=>detectorRaw S (S.classTokens (w.q j)))
  change S.read (joint w r x) q =
    Orbits.moment S (beside (r • x).ofLp (OPE.positions S e).ofLp)
      (stages v (fun j=>(OPE.tags S e j).2))
  have places : beside (r • x).ofLp (OPE.positions S e).ofLp =
      (joint w r x).ofLp ∘ E :=by
    funext j
    cases j with
    | inl j => simp [E,joint,points,beside]
    | inr j =>
      obtain ⟨j,rfl⟩:=(index S w).surjective j
      have node : (OPE.positions S e) (index S w j)=w.held j.succ :=
        congrArg Prod.fst (WilsonMacroscopicRichWatchPlot.entry (S:=S) w j)
      change (OPE.positions S e) (index S w j)=_
      rw [node]
      simp [E,joint,points]
  have labels : names (stages v (fun j=>(OPE.tags S e j).2)) = q ∘ E :=by
    funext j
    cases j with
    | inl j =>
      simp [names,stages,q,E,lift]
      rfl
    | inr j =>
      obtain ⟨j,rfl⟩:=(index S w).surjective j
      have raw : OPE.tags S e (index S w j)=S.classTokens (w.q j) :=
        congrArg Prod.snd (WilsonMacroscopicRichWatchPlot.entry (S:=S) w j)
      change detectorRaw S (OPE.tags S e (index S w j))=_
      rw [raw]
      simp [q,E]
  rw [observed,places,labels,perm_observe S F.room.kernel.laws.toSymmetric E q clear,
    named_fin S F.room.kernel.laws.toSymmetric q clear]

theorem tested (F:Spec.Final R.family f S) {a:ℕ} (W:Fin a→Watch R.family) (i:Fin a)
    (d:Fin n→ℕ) (v:Labels S d) (r:ℝ) (φ:Test n)
    (clear:∀x∈tsupport (φ:Points n→ℂ),joint (W i) r x∈conf _) :
    reading (S:=S) R d (lift R d v) φ (calibrated S (W i)) r =
    φ.applyTo (fun x=>current W (r • x).ofLp v i) :=by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport (φ:Points n→ℂ)
  · exact congrArg (φ x * ·) (literal R F W i d v r x (clear x hx))
  · have h : φ x=0 :=by by_contra ne; exact hx (subset_closure ne)
    simp [h]

end YM.Integration.WilsonCenteredWatchedClasses
