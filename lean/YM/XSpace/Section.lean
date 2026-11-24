import YM.Work.G01
import YM.Work.G02
import YM.Work.G03
import YM.Work.G04
import YM.Work.G05
import YM.Work.G06

/-!
# A choice of actual primary stencils for the bare operator basis

Freedom used: average for equivariance **inside** the radial-coordinate recovery, so
all label polynomials at a given top horizon come from ONE local coordinate system. This
also helps with linear Wick-jet subtraction (apply Gaussian algebra in these coordinates).
This is a choice of bona fide microscopic cylinders, cutoff-independent, WITH the
nonlinear holonomy projection, not arbitrary polynomials in linearized link fields.
Construct and certify as `YM.Source.SectionData` in the baseline conventions. (We don't
claim equality with any pre-existing `SectionData`.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Filter Set Lattice RG Labels Source Source.Drops Wilson
open Work.G05 Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {H : Hol G} {d m : ℕ}

lemma peg (H : Hol G) (d : ℕ) : Peg H d:=Work.G02.answer Work.G01.answer _ H _

-- same Taylor convention as Exact and as the projection used on bare `S_h`.
def snapTurn (s : Ortho) : Snap G d →L[ℝ] Snap G d:= LinearMap.toContinuousLinearMap (LinearMap.pi (fun i => (Taylor.turn s).comp (LinearMap.proj i)))
def snapColor (a : G.El) : Snap G d →L[ℝ] Snap G d:= LinearMap.toContinuousLinearMap
  (LinearMap.pi fun i=> (Taylor.paint a).comp (LinearMap.proj i))
lemma snapTurn_apply (s : Ortho) (x : Snap G d) (i) : snapTurn s x i=Taylor.turn s (x i):=rfl
lemma snap_color_comm (s : Ortho) (x : Snap G d) (a : G.El) : snapTurn s (snapColor a x)=snapColor a (snapTurn s x):= funext fun i => (Taylor.turn_paint s a (x i)).symm
lemma snapTurn_mul (s t : Ortho) (x : Snap G d) : snapTurn (s*t) x=snapTurn s (snapTurn t x):=funext fun i => Taylor.turn_mul s t (x i)
lemma snap_expand (s : Ortho) (x : Snap G d) : expand d (snapTurn s x)=changedJet (fun _=>Taylor.turn s) (expand d x):=by
  funext i; by_cases h:i<d-1 <;> simp [expand,h,changedJet,snapTurn_apply]
lemma bring_turn (s : Signed) (x : Snap G d) : H.links d (expand d (snapTurn s.ortho⁻¹ x)) 1=
    pull s 0 (H.links d (expand d x) 1):= by rw [snap_expand,Work.G01.swirls_of_flow H s]

structure Survey (G : Gauge) (H : Hol G) (d : ℕ) where
  size : ℕ
  looks : Fin size → Slot
  /-- one analytic inverse of the holonomy sampler through that horizon -/
  sees : GaugePanel G size → Snap G d
  kit : Vision H d looks sees
  roll (s : Signed) : GaugePanel G size →L[ℝ] GaugePanel G size
  takes (s : Signed) (U : CoverConfig G) : mapped looks (pull s 0 U)=roll s (mapped looks U)
  signed (s : Signed) (v : GaugePanel G size) : sees (roll s v) = snapTurn s.ortho⁻¹ (sees v)

private lemma have_vision (H : Hol G) (d : ℕ) : ∃ (m : ℕ) (B : Fin m→ Slot), ∃ f, Vision H d B f := by
  obtain ⟨m,B,h⟩:= Work.G03.answer G H d (peg ..)
  obtain ⟨ha,C,hc,ht⟩:= Work.G04.answer G H d m B (peg ..) h
  exact ⟨m,B,insight ha C hc ht (peg ..)⟩

set_option maxHeartbeats 600000 in
private lemma assemble_survey {B : Fin m → Slot} {f : GaugePanel G m → Snap G d} (h : Vision H d B f) : Nonempty (Survey G H d):=by
  classical
  choose v r hr hv using fun (s : Signed) (i : Fin m) => Work.G06.slot_pull (G:=G) s (B i)
  let n:= Fintype.card (Signed × Fin m)
  let e:= Fintype.equivFin (Signed × Fin m)
  let C (i : Fin n):= v (e.symm i).1 (e.symm i).2
  let view (s : Signed) : GaugePanel G n →L[ℝ] GaugePanel G m := LinearMap.toContinuousLinearMap (LinearMap.pi fun i : Fin m => r s i • LinearMap.proj (e (s,i)))
  have eval s (x : GaugePanel G n) i : view s x i=r s i • x (e (s,i)):=rfl
  have he s (U : CoverConfig G) : mapped B (pull s 0 U) = view s (mapped C U) := by funext i; simp [eval,mapped,hv,C]
  let roll (t : Signed) : GaugePanel G n →L[ℝ] GaugePanel G n := LinearMap.toContinuousLinearMap (LinearMap.pi fun i : Fin n => (r (e.symm i).1 (e.symm i).2)⁻¹ • ((LinearMap.proj (e.symm i).2) ∘ₗ (view (t*(e.symm i).1)).toLinearMap))
  have ht (t s i) (X : GaugePanel G n) : roll t X (e (s,i))=(r s i)⁻¹ • view (t*s) X i := by
    change (r (e.symm (e (s,i))).1 (e.symm (e (s,i))).2)⁻¹ • view (t*(e.symm (e (s,i))).1) X (e.symm (e (s,i))).2 = _; simp
  have hR s i : r s i≠0:=by rcases hr s i with hk|hk <;> rw [hk] <;> norm_num
  have roll_view (s t : Signed) (X : GaugePanel G n) : view s (roll t X)=view (t*s) X := by
    funext i; rw [eval,ht,smul_inv_smul₀ (hR s i)]
  have hX (X Y : GaugePanel G n) (hq : ∀ s,view s X=view s Y) : X=Y :=by
    funext i; obtain ⟨⟨s,i⟩,rfl⟩:=e.surjective i; apply smul_right_injective (M:=G.Color) (hR s i); exact congr_fun (hq s) i
  let c := (Fintype.card Signed:ℝ)
  let term (s : Signed) (X : GaugePanel G n):= snapTurn s.ortho (f (view s X))
  let g (X : GaugePanel G n):= c⁻¹ • ∑ s:Signed, term s X
  have hv (s) : Tendsto (view s) (𝓝 0) (𝓝 0):=by simpa using (view s).continuous.tendsto 0
  refine ⟨⟨n,C,g,⟨?_,?_,?_,?_⟩,roll,(fun t U=>hX _ _ fun s=>?_),?_⟩⟩
  · haveI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
    apply ContDiffAt.analyticAt
    refine ContDiffAt.smul (f:=fun _ => c⁻¹) contDiffAt_const ?_
    refine ContDiffAt.sum (fun s _=>?_)
    apply ((snapTurn (G:=G) (d:=d) s.ortho).contDiff (𝕜:=ℝ)).contDiffAt.comp 0
    exact ((show AnalyticAt ℝ f (view s 0) by rw [map_zero]; exact h.1).comp (f:=view s) ((view s).analyticAt _)).contDiffAt
  · simp [g,term,h.2.1]
  · have hq (s : Signed) : ∀ᶠ x in 𝓝 0,term s (bring H d C x)=x:=by
      let F := snapTurn (G:=G) (d:=d) s.ortho⁻¹
      have he' : Tendsto F (𝓝 0) (𝓝 0) := by simpa using F.continuous.tendsto 0
      filter_upwards [he'.eventually h.2.2.1] with x hx
      have hc : view s (bring H d C x)=bring H d B (F x):=by
        change view s (mapped C _)=mapped B (H.links _ _ _)
        rw [← he, ← bring_turn]
      dsimp only [term]; rw [hc,hx]; unfold F; rw [← snapTurn_mul,mul_inv_cancel]; ext1 i; rw [snapTurn_apply,Taylor.oneTurn]
    filter_upwards [eventually_all.mpr hq] with x hx
    have hc : c≠0:=by unfold c; positivity
    unfold g; simp_rw [hx,Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ hc _
  · intro a
    have ha (s : Signed) (x : GaugePanel G n) : view s (rotates a x)=rotates a (view s x):=by
      funext i; simp [rotates,eval]
    filter_upwards [eventually_all.mpr (fun s=> (hv s).eventually (h.2.2.2 a))] with x hx
    change g _ = snapColor a (g x)
    unfold g; rw [map_smul,map_sum]; congr 1; apply Finset.sum_congr rfl; intro s _; unfold term; rw [ha,hx]; exact snap_color_comm s.ortho _ a
  · rw [roll_view,← he, ← he,pull_pull]; simp [affine]
  intro s X
  have he' t : term t (roll s X) = snapTurn s.ortho⁻¹ (term (s*t) X):=by
    unfold term; rw [roll_view, ← snapTurn_mul, show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO .., inv_mul_cancel_left];
  unfold g; simp_rw [he', ← map_sum,map_smul]; congr 2; exact Equiv.sum_comp (Equiv.mulLeft s) (fun t=> term t X)

theorem surveys (H : Hol G) (d) : Nonempty (Survey G H d) := by obtain ⟨_,_,_,h⟩:=have_vision H d; exact assemble_survey h

namespace Survey
variable (A : Survey G H d)

def recover := blockTaylor d A.sees
def reading := A.recover ∘ fun U : CoverConfig G => mapped A.looks U
lemma recover_smooth : ContDiff ℝ ω A.recover:= blockTaylor_contDiff ..
lemma recover_zero : A.recover 0=0 := (blockTaylor_zero ..).trans A.kit.2.1
lemma recover_comm (u : G.El) (x : GaugePanel G A.size) : A.recover (rotates u x)=Cast u (A.recover x):=by
  letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
  exact Cast_blockTaylor (A.kit.1.contDiffAt.of_le le_top) u (A.kit.2.2.2 u) x
lemma recover_roll (s : Signed) (x : GaugePanel G A.size) : A.recover (A.roll s x)=snapTurn s.ortho⁻¹ (A.recover x):=by
  letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
  exact blockTaylor_equivariant (A.kit.1.contDiffAt.of_le le_top) _ _ (Filter.Eventually.of_forall (A.signed s)) _
lemma reading_gauge (x : CoverConfig G) (g : Cover → G.El) : A.reading (Lattice.gauge g x)=Cast (g 0) (A.reading x):= by
  unfold reading; simp only [comp_apply]; rw [show mapped A.looks _= _ from funext fun i=> Work.G06.slot_gauge (A.looks i) g x]; exact recover_comm ..
lemma reading_signed (x : CoverConfig G) (s : Signed) : A.reading (pull s 0 x) = snapTurn s.ortho⁻¹ (A.reading x):=by
  unfold reading; simp only [comp_apply]; rw [A.takes]; exact recover_roll ..

def coordinate (i : Key G) := (block_polynomial A.sees i).choose
lemma coordinate_at (x : GaugePanel G A.size) (i : Key G) : lumin (A.coordinate i) x=coord (expand d (A.recover x)) i := (block_polynomial A.sees i).choose_spec x
lemma coordinate_low (i : Key G) : lows (A.coordinate i) 1 := by apply lows_of_zero; rw [coordinate_at,recover_zero]; simp [coord]

def cyl : Pol G →ₐ[ℂ] Pose G A.size := MvPolynomial.aeval A.coordinate
lemma cylinder_at (p : Pol G) (x : GaugePanel G A.size) : lumin (A.cyl p) x= read (expand d (A.recover x)) p:= substituted x _ (A.coordinate_at x) _
lemma projects (p : Label G d) : Projects H p (lumin (A.cyl p.val) ∘ mapped A.looks):=by
  letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
  exact recovery_projects (A.kit.1.contDiffAt.of_le le_top) A.kit.2.2.1 (peg ..) _ _ (A.cylinder_at p.val)

variable (F : Frame G d)

def Represents (T : SectionData F): Prop:= T.Sound H ∧ pop T ∧ ∀ (v : Label G d) (U : CoverConfig G), T.evaluate (F.coords v) U= read (expand d (A.reading U)) v.val

theorem prepares : ∃ T, A.Represents F T := by
  obtain ⟨r,hr⟩:= Work.G06.enclose A.looks
  obtain ⟨Y,hY⟩:= Work.G06.realize G A.looks (box r) hr
  let T : SectionData F:=⟨box r,Y.toLinearMap ∘ₗ A.cyl.toLinearMap ∘ₗ (localFields G d).subtype ∘ₗ F.coords.symm.toLinearMap⟩
  have he (v : Label G d) : T.evaluate (F.coords v)=lumin (A.cyl v.val) ∘ mapped A.looks:=by
    funext U
    change MvPolynomial.aeval (entry U) (Y (A.cyl (F.coords.symm (F.coords v)).val))=_
    rw [hY,F.coords.symm_apply_apply]; rfl
  have ht (v : Label G d) (U : CoverConfig G) : T.evaluate (F.coords v) U = read (expand d (A.reading U)) v.val:= by rw [he]; exact cylinder_at ..
  refine ⟨T,⟨center_box r,box_covariant r,?_,?_,?_,?_,?_⟩,?_,ht⟩
  · intro v; obtain ⟨v,rfl⟩:=F.coords.surjective v; intro t U; rw [ht,ht,reading_gauge]
    have h (a : G.El) (x : Snap G d) : expand d (Cast a x)= colored a (expand d x):=by funext i; by_cases h:i<d-1 <;> simp [expand,h,Cast,colored]
    rw [h]; exact v.property.2 ..
  · rw [← F.coords_unit]; funext U; rw [ht]; exact map_one _
  · intro s v x; obtain ⟨v,rfl⟩:= F.coords.surjective v; rw [F.act_coords,ht,ht, A.reading_signed,snap_expand]; exact (eval_changed ..).symm
  · intro v x
    have hv : star v=F.coords (realBar (F.coords.symm v)):= (funext fun i=> F.conj_basis v i).symm
    rw [hv,ht]; nth_rw 2 [show v= F.coords (F.coords.symm v) from (F.coords.apply_symm_apply v).symm]; rw [ht]; exact conj_value ..
  · intro v; obtain ⟨v,rfl⟩:= F.coords.surjective v; rw [he,F.coords.symm_apply_apply]; exact A.projects v
  intro i
  refine ⟨A.size,A.looks,hr,A.cyl (F.basis i).val, F.coords_basis i ▸ he (F.basis i),lows_substitute _ A.coordinate_low _ _ ?_⟩
  intro a ha; have ha':=((pure_grade _ (F.basis i)).mp (F.pure i)) (MvPolynomial.mem_support_iff.mp ha); rw [weight_slot] at ha'; exact congr_arg Prod.snd ha'.symm
end Survey
end YM.XSpace
