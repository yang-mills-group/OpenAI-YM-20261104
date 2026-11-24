import YM.SchemeConversionRG11.Maxwell.Calm

/-!
# Finite free field-frame determination

All horizons, on the actual complex quotient *E*, preserving the real form and the unit
and the flag. For simple colors. Correlations/rotations only need signed Euclidean inputs.
These are not detector estimates on the physical construction. Couple via Profile or other
scheme marker separately, with its independently needed first-order evidence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open Pert.Position Horizon
open scoped Topology BigOperators RealInnerProductSpace InnerProduct ComplexOrder ContDiff

variable {G : Gauge} (F : Labels.Frames G) {d n k : ℕ}

abbrev Light (d : ℕ) := {p : E F d // bar F d p=p}
lemma leaders (C : G.ColorIndex) (H : G.Simple) {B : Buffer F d} (hx : Calm F B) (h : 4 ≤ d) (t : ℝ) :
    ∃ T:Door G, Fair T ∧ ∀ (v : Light F d) (A : TaylorTower G),
      Maxwell.probe (commerce T A) (address F d (flange F B t v.val))=Maxwell.probe A (address F d v.val) := by
  let L (p : Light F d) := address F d p.val
  let R (p : Light F d) := address F d (flange F B t p.val)
  have hr p : realForm (L p)=L p := by
    unfold L; rw [← address_star F (H:=spin_free _), show bar _ _ _=_ from p.property] -- rewrite?
  have ht p : realForm (R p)=R p := by
    unfold R; rw [← address_star F (H:=spin_free _)]; change address F d (bar F _ _)=_
    rw [← flange_bar,p.property]
  have hv (r : Flavor 0) : ∃ p, L p=team G r r ∧ R p=L p := by
    let q := incl F h (squads F r)
    have hh : address F d q=team G r r := (address_rise F d h _).trans (squares F _)
    have hu : bar F d q=q := address_inj F d ((address_star F _).trans (by rw [hh,realTeam]))
    refine ⟨⟨q,hu⟩,hh,?_⟩; exact congr_arg (address F d) (flange_small F H hx h (squads F r) t)
  obtain ⟨T,w⟩ := force_orthogonal (W:=L) (U:=R) C hr ht (fun n v ↦ glaze F H hx h (fun i ↦ (v i).val) t) hv
  exact ⟨T.toContinuousLinearEquiv.toContinuousLinearMap, T.norm_map, fun p A ↦ w A p⟩

lemma basic_fair {p : WickPol G} (R : Door G) (h : Fair R) (hw : p∈Teams G n k) (A : TaylorTower G) : Maxwell.probe (commerce R A) p=Maxwell.probe A p := by
  induction hw using Submodule.span_induction with
  | mem p h' => obtain ⟨u,v,rfl⟩ := h'; rw [basicTeam,basicTeam]; unfold commerce; simp only [givens]; rw [h.inner]
  | zero => simp
  | add p q _ _ hp hq => rw [map_add,map_add,hp,hq]
  | smul t p _ hp => rw [map_smul,map_smul,hp]
lemma five_fair {p : WickPol G} (H : G.Simple) (R : Door G) (h : Fair R) (hw : p∈shellSector G 5) (A : TaylorTower G) : Maxwell.probe (commerce R A) p=Maxwell.probe A p := by
  classical
  rw [five_support H,Submodule.mem_sup] at hw
  obtain ⟨x,hx,y,hy,rfl⟩ := hw
  rw [map_add,map_add,basic_fair R h hy]
  rw [low_support H,Submodule.mem_sup] at hx; obtain ⟨u,hu,v,hv,rfl⟩ := hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [map_add,map_add,basic_fair R h hv]; simp

lemma five_pin (C : G.ColorIndex) (H : G.Simple) {B : Buffer F 5} (hx : Calm F B) (p : Light F 5) (t : ℝ) : flange F B t p.val=p.val := by
  obtain ⟨T,hT,hP⟩ := leaders F C H hx (by omega) t
  apply address_inj F 5; refine equalPol _ _ (fun A ↦ ?_)
  exact (five_fair H T hT (address_in F _ _) A).symm.trans (hP p A)
lemma high_tracks (C : G.ColorIndex) (H : G.Simple) {B : Buffer F d} (hx : Calm F B) (h : 6≤d) (t : ℝ) :
    ∃ T∈Tracks G, ∀ (p : Light F d) (A : TaylorTower G),
      Maxwell.probe A (address F d (flange F B t p.val))=Maxwell.probe (commerce T A) (address F d p.val) := by
  obtain ⟨T,hT,hP⟩ := leaders F C H hx (by omega) t
  let v := (fields F d).symm (⟨vase G, vase_fits h⟩ : shellSector G d)
  have he : address F d v=vase G := by rw [address_eval]; unfold v; rw [LinearEquiv.apply_symm_apply]
  have hv : bar F d v=v := address_inj F d ((address_star F _).trans (by rw [he,vase_real]))
  have ht : T∈Tracks G := ridge_tracks T H hT (address F d (flange F B t v)) (address_in F d _)
    (fun i ↦ (hP ⟨v,hv⟩ i).trans (congr_arg _ he))
  refine ⟨T†,inInv ht, fun p A ↦ ?_⟩
  have hw := hP p (commerce (T†) A); rw [← commerce_comp,show T ∘L (T†)=1 from hT.inv',commerce_id] at hw; exact hw

lemma high_pin (C : G.ColorIndex) (H : G.Simple) {B : Buffer F d} (hx : Calm F B) (h : 6 ≤ d) (p : Light F d) : B.val p.val=0 := by
  classical
  suffices ht : ∀ A,Maxwell.probe A (address F d (B.val p.val))=0 by
    apply address_inj F d; refine equalPol _ _ fun i ↦ ?_; rw [ht,map_zero,map_zero]
  intro A
  let L := ((((Maxwell.probe A).toLinearMap.comp (address F d)).restrictScalars ℝ).toContinuousLinearMap)
  let f := fun t:ℝ ↦ L (flange F B t p.val)
  have hg := L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (earning F B 0 p.val)
  rw [flange_zero] at hg; change HasDerivAt f (L (B.val p.val)) 0 at hg -- maybe rewrites only value?
  have he : (range f).Finite := by
    refine (finitely H (address F d p.val) (address_in F _ _) A).subset ?_
    rintro x ⟨t,rfl⟩; obtain ⟨T,hT,hP⟩ := high_tracks F C H hx h t; exact ⟨T,hT,(hP p A).symm⟩
  have hu : f=ᶠ[𝓝 0] (fun _ : ℝ ↦ f 0) := by
    filter_upwards [hg.continuousAt.eventually (((he.sdiff (t:={f 0})).isClosed.isOpen_compl).mem_nhds (show f 0∈(range f \ {f 0})ᶜ from by simp))] with i hi
    by_contra hn; exact hi ⟨⟨i,rfl⟩,hn⟩
  exact hg.unique ((hasDerivAt_const ..).congr_of_eventuallyEq hu)

lemma cooled (H : G.Simple) {B : Buffer F d} (he : 5 ≤ d) (hx : Calm F B) : ∀ p : Light F d, B.val p.val=0 := by
  classical
  have hN : 0<G.lieDim := by rw [Gauge.lieDim,← G.colorIso.finrank_eq]; haveI := H.nontrivial_color; exact Module.finrank_pos
  let C : G.ColorIndex := ⟨0,hN⟩
  rcases lt_or_ge d 6 with hd|hd
  · have hg : d=5 := by omega
    subst d; intro p; have hv := earning F B 0 p.val
    rw [flange_zero] at hv; have ht s := five_pin F C H hx p s
    exact hv.unique ((hasDerivAt_const ..).congr_of_eventuallyEq (Eventually.of_forall (fun i : ℝ ↦ ht i)))
  exact high_pin F C H hx hd

lemma real_extract (B : Buffer F d) (h : ∀ p : Light F d, B.val p.val=0) : B=0 := by
  classical
  ext1; apply ContinuousLinearMap.ext; intro x
  change B.val x=0
  let z := bar F d x
  have hr : bar F d z=x := Table.reflect_star ..
  have hp : bar F d (x+z)=x+z := by rw [map_add,hr,add_comm]
  have hq : bar F d (Complex.I • (x-z)) = Complex.I • (x-z) := by rw [map_smulₛₗ,map_sub,hr]; change _ • (z-x)=_; simp; rw [← smul_neg, neg_sub]
  have hh : B.val x + B.val z=0 := (map_add B.val ..).symm.trans (h (⟨_,hp⟩:Light F d))
  have hg : B.val x=B.val z := by
    have ht : B.val (Complex.I • (x-z))=0 := h (⟨_,hq⟩:Light F d)
    rw [B.property.2.2.2.2,map_sub] at ht
    exact sub_eq_zero.mp ((smul_eq_zero.mp ht).resolve_left Complex.I_ne_zero)
  rw [←hg,←two_smul ℝ] at hh; exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

/-- Every finite free horizon, same group and frames. This is rank with respect to
all the allowed field redefinitions in `buffers`; no assumption on the selected continuum!
See next lemma for nested finite tests of these equations. -/
theorem frozen (H : G.Simple) (d : ℕ) : Pert.Position.Frozen F d := by
  rcases lt_trichotomy d 4 with hx|hx|hx
  · exact Pert.Rigid.first_frozen F H hx
  · subst d; exact Pert.Rigid.frozen_four F H
  intro B ht; exact real_extract F B (cooled F H (by omega) ht)

/-- Fix tests for all orders once, extending one system through all horizons. -/
theorem determines (H : G.Simple) : ∃ c : (d : ℕ) → Detector.Poll F d,
    ∀ i, (c i).Carries (c (i+1)) (Nat.le_succ i) := Detector.Poll.sequence (frozen F H)
end YM.SchemeConversionRG11.Corona
