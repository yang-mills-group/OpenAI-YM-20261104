import YM.FormalOPE.RG10.Carryon.Portfolio

/-!
# Uniqueness around WilsonX finite position questionnaires

Input `posture` allowed regulator dependence. Both leading questionnaire for closeness to free and leading affine frame
for closeness to identity are tested in the eventual uniqueness hypothesis, not **any** positive
Taylor correction. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G : Gauge} {F : Frames G} {d : ℕ}
local notation "K" d=> Matrix (Deck F d) (Deck F d) fps
local notation "L" d=> Matrix (Deck F d) (Deck F d) ℝ
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "ins"=> PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n
variable {D : Stock F}{u : Mark (Deck F d) PertExtension.Physical.Profile.n → fps}

lemma Credible.sure (h: Credible D u) : respects D u (posture D u):= (crib D u).normalizes h

lemma sticks (P: Plan F) (q:ℕ+) (m:ℕ): P.dressed q m d = ins (P.begins q m d) (posture P.stock (P.begins q m d)):= rfl

-- zero order fixes the actual additive Lie-parameter, using both leading and
-- normalized labels
namespace respects
variable (h : Official D)
include h
lemma unique (hu:Credible D u) {X:K d} (hx: Upright X) (h₀: Stg X 0=Stg (posture D u) 0)(hw: respects D u X): X=posture D u := by
 apply (crib D u).uniqueness hu
 · exact fun i=> (hw i).trans (hu.sure i).symm
 · intro i j; exact (coeff_zero_eq_constantCoeff_apply (X i j)).symm.trans ((congr_fun (congr_fun h₀ i) j).trans (by simp [Stg,posture]))
 · simp [posture]
 intro i hi; change Stg (posture D u) i-Stg X i ∈ (D d).Z; rw [agree h]; exact Submodule.sub_mem _ ((installed u h).higher _ hi) (hx.higher _ hi)

variable {α:Type*}{l : Filter α} (X: α → Matrix (Deck F d) (Deck F d) fps) {b:α→Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
omit h in
private lemma allClear {I A : Type*}[Fintype I]{α:Type*}{l:Filter α}{shape:A→ℕ}
   {E: TestSystem I A shape}{g : Mark I shape → ℝ}{a:α → E.Parameter}{t:α → E.Z}(h:E.Regular g)
   (ht:Tendsto (fun i=> (a i, t i)) l (𝓝 (g∘ markIn _,0)))
   (hh: ∀ᶠ i in l,E.lieResult (a i) (t i)= E.target): ∀ᶠ i in l,t i= E.branch g (a i) := by
   let A' := g ∘ markIn E.tests; let M:=(A',(0:E.Z)); let f:= E.solver; let φ:= fderiv ℝ f M;
   let S:=(LinearEquiv.ofBijective φ.toLinearMap ((E).eventually_fullrank g h |>.self_of_nhds)).toContinuousLinearEquiv
   have hd:HasStrictFDerivAt f S.toContinuousLinearMap M:= E.smooth_solve.hasStrictFDerivAt (by simp)
   have ha : Tendsto a l (𝓝 A'):= ht.fst_nhds
   have he := (E.tends g h).comp ha; have H:= HasStrictFDerivAt.eventually_left_inverse (f':=S) hd
   filter_upwards [hh,ht.eventually H, he.eventually H, ha.eventually (E.solves _ h)] with i hv hM htR hS;
   have ht : f (a i,t i)= f (a i,E.branch g (a i)):= Prod.ext rfl (hv.trans hS.symm)
   exact congr_arg Prod.snd (hM.symm.trans ((congr_arg _ ht).trans htR))

set_option maxHeartbeats 500000 in
lemma stays (hb : listens (D:=D) (l:=l) b) (hx: ∀ a,Upright (X a))
    (ht:Tendsto (fun a=> Stg (X a) 0) l (𝓝 (1:L d)))(hw: ∀ᶠ a in l,respects D (b a) (X a)): ∀ᶠ a in l,X a=posture D (b a) := by
  let E:= D d
  let P := raw F d ∘ markIn (D d).tests; let M:=(P, (0:E.Z));
  let a i:= probe D (b i);
  let k i:= Stg (X i) 0;
  let t i:E.Z:= ⟨k i- (1:L d),agree h ▸ (hx i).go⟩;
  have hg: Tendsto (fun i=> (a i, t i)) l (𝓝 M) := by
      apply hb.prodMk_nhds; apply tendsto_subtype_rng.mpr; change Tendsto (fun i=> k i - (1:L d)) l (𝓝 (0:L d)); simpa only [sub_self] using! (ht.sub_const (1:L d))
  have ne j : Stg (posture D (b j)) 0 = E.baseline + (E.branch (raw F d) (a j)).val := by ext u v; simp [posture,Stg,crib,TestSystem.leadingAdjust]; rfl
  have hAP : (1:L d)=E.baseline:= by change _=(D d).baseline; rw [h.normal]; exact diag_one
  have eqm i: (E.baseline + (t i).val)=(k i):= by rw [← hAP]; change (1:L d) + (k i - 1)= _; abel
  have hw' : ∀ᶠ i in l,E.lieResult (a i) (t i)= E.target:= by
    filter_upwards [hw] with i hv
    unfold TestSystem.lieResult; rw [eqm];
    unfold a; change E.result ((fun x:Mark (Deck F d) PertExtension.Physical.Profile.n =>constantCoeff (b i x)) ∘ _) (k i) = _
    rw [E.result_eq];
    apply Eq.trans _ ((hv 0).trans (if_pos rfl)); apply congr_arg (D d).select; funext w;
    simp only [Function.comp_apply, coeff_zero_eq_constantCoeff_apply, insert_constant,k,Stg]; rfl
  filter_upwards [allClear (E:=E) (g:=raw F d) (a:=a) (t:=t) (h.fresh _) hg hw',hw,credential h b hb] with i hD hv hc
  exact unique h hc (hx i) (((eqm i).symm.trans (congr_arg (fun u : E.Z => E.baseline + u.val) hD)).trans (ne i).symm) hv
end respects
end YM.FormalOPE.RG10.Carryon
