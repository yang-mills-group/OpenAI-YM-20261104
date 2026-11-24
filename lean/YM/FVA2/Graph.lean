import YM.FVA2.Letter
import YM.MS.Wilson.Energy

/-!
# Rooted local fields on the inversion quotient graph

Bone paths here are just ordinary links; they can be oriented differently.
Use an optional endpoint to handle the omitted global fixing vertex. Nothing
is assumed about analytical continuum behavior of the finite configuration.
-/
set_option autoImplicit false

noncomputable section

namespace YM.FVA2
open Finset Function Set Filter MeasureTheory MS MS.Koszul MS.Book MS.Bare MS.Bare.Maurer
open MS.Cylinder Cylinder.Taylor MS.Native
open scoped Topology ContDiff

structure Ends (A P : Type) where
  tail : A → Option P
  head : A → Option P

namespace Ends
variable {P A : Type} (R : Ends A P) (G : Gauge) [DecidableEq P] [DecidableEq A]
abbrev Z (G : Gauge) (A : Type) := A × G.ColorIndex
abbrev Alphabet (G : Gauge) (A P : Type) := Letter (Z G A) (Z G P)
abbrev Links (G : Gauge) (A : Type) := Lot G A

variable {G}

def morph (e : A) : Lot G P →ₗ[ℝ] Maurer.Ends G where
  toFun z := ((R.tail e).elim 0 z,(R.head e).elim 0 z)
  map_add' u v := by
    ext1
    · cases R.tail e <;> simp
    cases R.head e <;> simp
  map_smul' u v := by
    ext1
    · cases R.tail e <;> simp
    cases R.head e <;> simp

/-- Taylor-germ field of link gauge transformations in logarithmic coordinates. -/
def flow (x : Links G A) : Lot G P →ₗ[ℝ] Links G A :=
  LinearMap.pi fun e => (voltage (x e)) ∘ₗ R.morph e

def locus (i : Z G P) (x : Links G A) := R.flow x (priv i)

omit [DecidableEq A] in
lemma locus_at (i : Z G P) (x : Links G A) (e : A) :
    R.locus i x e = volts (R.morph e (priv i)) (x e) := rfl

def tangentVec : Alphabet G A P → Links G A
| .a i => priv i
| _ => 0

variable [Fintype A]

def glowGraph : Focus.Glow (Letter.focus (Z G A) (Z G P)) (Links G A) where
  e0 := tangentVec
  seed := projector
  restore v := frame v
  ever | .a i => fun _ => ⟨i,rfl⟩
       | .k _i => fun h => (h rfl).elim
       | .b _i => fun h => (h rfl).elim
       | .c _i => fun h => (h rfl).elim

omit [DecidableEq A] in
lemma smooth_locus (i : Z G P) : germ (R.locus i) :=
  contDiffAt_pi.mpr fun e =>
    (Maurer.home (R.morph e (priv i))).comp (f:=fun x:Links G A=> x e) 0 (contDiff_apply ..|>.contDiffAt)

omit [DecidableEq A] in
lemma local_partial (i : Z G P) (e : A) {x u : Links G A}
    (ht : DifferentiableAt ℝ (R.locus i) x)
    (hv : DifferentiableAt ℝ (volts (R.morph e (priv i))) (x e)) :
    fderiv ℝ (R.locus i) x u e = fderiv ℝ (volts (R.morph e (priv i))) (x e) (u e) := by
  let J : Links G A →L[ℝ] G.Color := ContinuousLinearMap.proj e
  have he : J ∘ R.locus i = volts (R.morph e (priv i)) ∘ J := rfl
  have hp := fderiv_comp x J.differentiableAt ht
  rw [he, fderiv_comp x hv J.differentiableAt, J.fderiv, J.fderiv] at hp
  exact DFunLike.congr_fun hp.symm u

variable [Fintype P]

omit [DecidableEq A] [DecidableEq P] [Fintype P] [Fintype A] in
lemma morph_braid (e : A) (i j : Lot G P) :
    R.morph e (Native.braid i j)=Maurer.braid (R.morph e i) (R.morph e j) := by
  unfold Maurer.braid Native.braid morph
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  cases R.tail e <;> cases R.head e <;> simp

omit [DecidableEq A] in
lemma swirl_locus (i j : Z G P) : ∀ᶠ x : Links G A in 𝓝 0,
    fderiv ℝ (R.locus j) x (R.locus i x) - fderiv ℝ (R.locus i) x (R.locus j x) =
      ∑ k:Z G P,colorTerm G P i j k • R.locus k x := by
  obtain ⟨r,hr,H⟩ := LocalH.geom_patch G
  let V := H r (le_refl r)
  filter_upwards [eventually_all.mpr (fun e:A =>
    (show ∀ᶠ x:Links G A in 𝓝 0,x e ∈ Metric.ball 0 r from
      (continuous_apply e |>.tendsto (0:Links G A)).eventually (Metric.ball_mem_nhds _ hr))),
    (R.smooth_locus i).eventually (by simp),(R.smooth_locus j).eventually (by simp)] with x hx hi hj
  have he : (∑ k:Z G P,colorTerm G P i j k • R.locus k x)=R.flow x (Native.braid (priv i) (priv j)) := by
    rw [← crowd, map_sum]; simp only [map_smul]; rfl
  rw [he]; funext e
  rw [Pi.sub_apply,R.local_partial j _ (hj.differentiableAt (by simp))
        ((analytic_volts _ V (hx e)).differentiableAt (by simp)),
      R.local_partial i _ (hi.differentiableAt (by simp))
        ((analytic_volts _ V (hx e)).differentiableAt (by simp)),
      R.locus_at, R.locus_at, storm _ _ V (hx e), ← R.morph_braid]; rfl

omit [DecidableEq A] in
lemma vibes : Focus.Vibes (colorTerm G P) R.locus :=
  ⟨cartan .., R.smooth_locus, R.swirl_locus⟩

/-- Logarithm of the product Haar density relative to its value at the saddle. -/
def measure_term (x : Links G A) := ∑ i : A, lac (x i)

omit [DecidableEq A] in
lemma measure_germ : germ (measure_term (A:=A) (G:=G)) :=
  ContDiffAt.sum fun i _=> (hlog G).comp (f:=fun x:Links G A=> x i) 0 (contDiff_apply ..|>.contDiffAt)

omit [DecidableEq A] [Fintype P] in
lemma D_measure {x v : Links G A} (h : ∀ i:A,DifferentiableAt ℝ lac (x i)) :
    fderiv ℝ measure_term x v=∑ i:A, fderiv ℝ lac (x i) (v i) := by
  let T i : Links G A→L[ℝ] G.Color:= ContinuousLinearMap.proj i
  have hh i:= (h i).hasFDerivAt.comp (f:=⇑(T i)) x (T i).hasFDerivAt
  rw [show fderiv ℝ measure_term x=_ from (HasFDerivAt.fun_sum fun i _=> hh i).fderiv]
  simp; rfl

omit [Fintype P] in
lemma kernel_haar : Focus.Bills glowGraph (R.locus (G:=G)) measure_term := by
  intro k
  filter_upwards [(R.smooth_locus k).eventually (by simp),
    eventually_all.mpr (fun x:A=> (continuous_apply x|>.tendsto (0:Links G A)).eventually (
      (Maurer.wind_div (R.morph x (priv k))).and
        (((Maurer.hlog G).eventually (by simp)).and ((home (R.morph x (priv k))).eventually (by simp)))))] with x h hx
  have hv : DifferentiableAt ℝ (R.locus k) x:= h.differentiableAt (by simp)
  change Focus.index_div glowGraph (R.locus k) x + fderiv ℝ measure_term x (R.locus k x)=0
  have hd : Focus.index_div (glowGraph (P:=P)) (R.locus k) x=∑ i:A,Maurer.divs (volts (R.morph i (priv k))) (x i) := by
    unfold Focus.index_div; rw [Finset.sum_apply,Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _=>?_
    rw [by_row]; refine Finset.sum_congr rfl fun j _=>?_
    let T := projector (G:=G) (i,j)
    change fderiv ℝ (T ∘ R.locus k) x (priv (i,j))=_
    rw [fderiv_comp x T.differentiableAt hv, T.fderiv,ContinuousLinearMap.comp_apply,projector_k,
      R.local_partial k i hv ((hx i).2.2.differentiableAt (by simp))]
    simp [priv,Maurer.base]
  rw [hd,D_measure (fun i=> (hx i).2.1.differentiableAt (by simp)),← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _=> (hx i).1


def action_by (u : P → G.El) (x : A → G.El) (i : A) :=
  ((R.tail i).elim 1 u)⁻¹ * x i * (R.head i).elim 1 u

def invariant (F : (A → G.El)→ℝ) := ∀ u x, F (R.action_by u x)=F x

def exp_A (v : Links G A) := G.lieExp ∘ v

omit [DecidableEq A] [Fintype P] in
lemma inert_from (F : (A → G.El)→ℝ) (h : R.invariant F) (hg : germ (F ∘ exp_A)) :
    Focus.Inert R.locus (F ∘ exp_A) := by
  intro i
  let U (v : Links G A) (x:ℝ) : Links G A:=
    fun e => G.plog (G.mat (step (R.morph e (priv i)) (v e) x))
  let Z (t:ℝ) (x:P):= G.lieExp (t • (priv i x))
  obtain ⟨r,hr,H⟩:=LocalH.geom_patch G
  let Q:= H r (le_refl r)
  filter_upwards [hg.eventually (by simp), eventual_point hr] with v hv he
  have hz : U v 0=v := funext fun e=> by
    unfold U; rw [step_start]; exact snap_on Q (he e)
  have hU : HasDerivAt (U v) (R.locus i v) 0 := hasDerivAt_pi.mpr (fun e=> amp _ Q (he e))
  have hF := HasFDerivAt.comp_hasDerivAt_of_eq (l:= F ∘ exp_A) _
                ((hv.differentiableAt (by simp)).hasFDerivAt) hU hz.symm
  refine (hF.congr_of_eventuallyEq (f₁:=fun _=> F (exp_A v)) ?_).unique (hasDerivAt_const ..)
  filter_upwards [eventually_all.mpr (fun e:A=> walk_on (R.morph e (priv i)) Q (he e))] with t hT
  change F (exp_A v)= F (exp_A (U v t))
  rw [show exp_A (U v t)= R.action_by (Z t) (exp_A v) from ?_, h]
  funext e; unfold exp_A; dsimp only [Function.comp_apply,U]; refine (Q.2.2.2.1 (hT e)).trans ?_
  unfold step action_by morph Z; dsimp only [Function.comp_apply,LinearMap.coe_mk, AddHom.coe_mk];
  cases R.tail e <;> cases R.head e <;> simp [Next.SectorChange.exp_negative]
where
  eventual_point {r:ℝ}(hr:0<r) : ∀ᶠ v:Links G A in 𝓝 0,∀ e:A,v e∈Metric.ball 0 r :=
    eventually_all.mpr fun e=> (continuous_apply e|>.tendsto (0:Links G A)).eventually (Metric.ball_mem_nhds _ hr)
end Ends
end YM.FVA2
