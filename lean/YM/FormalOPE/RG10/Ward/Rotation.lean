import YM.FormalOPE.RG10.Ward.Proxies
import YM.Wilson.Symmetry
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails

/-! Transport of Wilson regulator correlations and supports by the allowed signed-translations.
Only inversion-preserving translations. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function Filter
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) (s : Signed) {u : Site n} (hu : -u=u)

include hu in
lemma reflectSend (e : Edge (Site n)) : sendEdge s u (Orb.reflect e) = Orb.reflect (sendEdge s u e) := by
  rcases e with ⟨x,i⟩; unfold Orb.reflect sendEdge affine
  let d := Step.rotate (posDir i) s
  have ha : s.act (step i:Site n) = d.vec := (Step.vec_rotate (posDir i) s).symm
  dsimp only
  change d.used (s.act (-x-step i)+u) = (-(d.used (s.act x+u)).1 - step (d.used (s.act x+u)).2, (d.used (s.act x+u)).2)
  simp only [Signed.act_sub, Signed.act_neg, ha]
  unfold Step.used Step.vec; cases he:d.neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · refine Prod.ext ?_ rfl; dsimp only
    conv_lhs => rhs; rw [← hu]
    abel
  refine Prod.ext ?_ rfl; dsimp only
  conv_lhs => lhs; rhs; rw [← hu]
  abel

private lemma index_fixes (e : OEdge n) : index e.val=e := Subtype.ext e.property

private lemma projection_eq {i j : Edge (Site n)} (h : index i=index j) : i=j ∨ i=Orb.reflect j := by
  have he : eR i=eR j := congr_arg (fun k : OEdge n => k.val) h
  rcases eR_spec i with hx|hx <;> rcases eR_spec j with hb|hb <;> rw [hx,hb] at he
  · exact Or.inl he
  · exact Or.inr he
  · exact Or.inr (by rw [← he, reflect_reflect])
  exact Or.inl (by simpa using congr_arg Orb.reflect he)

private def liftRole : Equiv.Perm (OEdge n) := Equiv.ofBijective (fun i => index (sendEdge s u i.val))
  ⟨(by
    intro i j h
    rcases projection_eq h with he|he
    · exact Subtype.ext (Wilson.sendEdge_injective _ _ he)
    rw [← reflectSend s hu _] at he; rw [← index_fixes i, ← index_fixes j];
    apply Subtype.ext; change eR _ = eR _; rw [sendEdge_injective s u he]; exact Orb.eR_reflect _),
    (by
      intro i; obtain ⟨j,hj⟩ := Finite.injective_iff_surjective.mp (sendEdge_injective s u) i.val
      use index j; unfold index; dsimp only
      have he : index (sendEdge s u (eR j)) = i:= by
        obtain h|h := eR_spec j
        · rw [h,hj]; exact index_fixes i
        rw [h, reflectSend s hu, hj];
        apply Subtype.ext; change eR _ = _; rw [eR_reflect]; exact i.property
      exact he)⟩

private lemma reads (e : Edge (Site n)) (U : Config G n) : pull s u U e =
    if s.flip e.2 then (U (sendEdge s u e))⁻¹ else U (sendEdge s u e) := by
  unfold pull Step.read sendEdge Step.rotate posDir; simp

include hu hn in
private lemma orients (e : Edge (Site n)) (A : Antes G n) : pull s u (liftLinks A) (Orb.reflect e) = (pull s u (liftLinks A) e)⁻¹ := by
  rw [reads,reflectSend s hu, reads, Orb.lift_flip hn]
  change (if s.flip e.2 then _ else _)=_; cases h:s.flip e.2 <;> rfl

variable (u) in
def orient (A : Antes G n) : Antes G n := fun i => pull s u (liftLinks A) i.val

include hu hn in
lemma orientation (A : Antes G n) : pull s u (liftLinks A)=liftLinks (orient s u A):= by
  funext i
  by_cases h:eR i=i
  · calc
      _ = pull s u (liftLinks A) (index i).val := by rw [show (index i).val=i from h]
      _ = liftLinks (orient s u A) (index i).val := (lift_at (orient s u A) (index i)).symm
      _ = _ := by rw [show (index i).val=i from h]
  have he : eR i = Orb.reflect i := (eR_spec i).resolve_left h
  nth_rw 1 [← reflect_reflect i]
  rw [orients hn s hu, show Orb.reflect i=(index i).val from he.symm,
    show liftLinks (orient s u A) i=(orient s u A (index i))⁻¹ from if_neg h]; rfl

local notation "μ" => Chart.physical G (OEdge n)
include hu in
lemma orient_measured : MeasurePreserving (orient (G:=G) s u) μ μ := by
  let e := liftRole (n:=n) s hu
  have hz : MeasurePreserving (fun U : Antes G n => (fun f => U (e f))) μ μ := by
    have hm := measurePreserving_piCongrLeft (fun _ : OEdge n => G.probHaar) e.symm
    convert hm using 1 <;> first | rfl | skip
    funext U k
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  let b (f : OEdge n) (U : G.El) := if Orb.eR (sendEdge s u f.val)=sendEdge s u f.val then U else U⁻¹
  let q (f : OEdge n) (U : G.El) := if s.flip f.val.2 then (b f U)⁻¹ else b f U
  have hq : MeasurePreserving (fun U : Antes G n => (fun f => q f (U f))) μ μ := by
    refine measurePreserving_pi (fun _ => G.probHaar) (fun _ => G.probHaar) (f := q) ?_
    intro i; by_cases he : eR (sendEdge s u i.val) = sendEdge s u i.val <;> cases h:s.flip i.val.2
    all_goals first | simpa [b,q,h,he] using! MeasurePreserving.id G.probHaar | simpa [b,q,h,he] using G.preserve_inv
  convert! hq.comp hz using 1; funext U k; unfold orient; rw [reads]
  rfl

include hu hn in
theorem beforeTurn {f : Config G n → ℝ} (hf : Continuous f) :
    preExpectation (f ∘ pull s u) = preExpectation f := by
  have hd (g : ℝ) : Continuous (preDensity g (G:=G) (n:=n)) := Real.continuous_exp.comp (((continuous_neg.comp (energy_cont.div_const (2:ℝ))).div_const _))
  have he := orient_measured (G:=G) s hu
  funext g; unfold preExpectation; congr 1 -- only numerator
  unfold preNum; simp_rw [Function.comp_apply]
  let F := f*preDensity g; have hF : Continuous F := hf.mul (hd _)
  have hx x : f (pull s u (liftLinks x))* preDensity g (liftLinks x) = F (liftLinks (orient s u x)) := by
    rw [← orientation hn s hu x]; unfold F; rw [Pi.mul_apply]; unfold preDensity; rw [energy_pull]
  simp_rw [hx]
  have hm := integral_map he.measurable.aemeasurable (f:=fun A => F (liftLinks A)) (by rw [he.map_eq]; exact (hF.comp liftlinks_cont).aestronglyMeasurable)
  rw [he.map_eq] at hm; exact hm.symm
end YM.FormalOPE.RG10.InversionWard
