import YM.XSpace.Orbifold
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-! # Root-fixed tree gauge on the inversion quotient -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Lattice Wilson MeasureTheory
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

namespace Regulator
variable (R : Regulator)
inductive Reach : ℕ → R.Vertex → Prop
| root : Reach 0 R.root
| next {k a} (l : R.Link) (b : R.Vertex) : R.Joins l a b → Reach k a → Reach (k+1) b

lemma walk_reach (w : Walk) (x : R.LSite) (hr : ∃ k, R.Reach k (R.vertex x)) : ∃ k, R.Reach k (R.vertex (stop x w)) := by
  induction w generalizing x with
  | nil => exact hr
  | cons d w ih =>
    apply ih; obtain ⟨j,hj⟩:=hr
    refine ⟨_,.next (R.link (d.used x)) _ ?_ hj⟩
    rcases d with ⟨a,b|b⟩
    · exact R.joins_of_rep (x,a)
    simp only [Step.used,Step.vec, ite_true,← sub_eq_add_neg]
    have h := Joins.symm _ (R.joins_of_rep (x-step a,a))
    simp only [sub_add_cancel] at h
    exact h

theorem connected (x : R.Vertex) : ∃ k, R.Reach k x := by
  let w := route 0 (lift x.val) 1
  have hw := R.walk_reach w 0 ⟨_,.root⟩
  have he : stop 0 w = x.val := calc
    _ = stop (wrap R.side 0) w := by rw [map_zero]
    _ = _ := (wrap_stop_cover ..).symm
    _ = _ := by unfold w; rw [route_end,wrap_lift]
  rwa [he,R.vertex_rep] at hw

abbrev Nonroot := {v : R.Vertex // v ≠ R.root}

structure Tree where
  depth : R.Vertex → ℕ
  parent : R.Nonroot → R.Vertex
  edge : R.Nonroot → R.Link
  lower (v : R.Nonroot) : depth (parent v) < depth v.val
  joins (v) : R.Joins (edge v) (parent v) v.val

open scoped Classical in
def treeDistance (x : R.Vertex) : ℕ := Nat.find (R.connected x)

lemma treecomes (x : R.Nonroot) : ∃ y l, R.treeDistance y < R.treeDistance x.val ∧ R.Joins l y x.val := by
  classical
  have hr : R.Reach (R.treeDistance x.val) x.val := Nat.find_spec (R.connected _)
  obtain ⟨x,hx⟩ := x
  generalize h : R.treeDistance x=k at hr
  cases hr with
  | root => exact (hx rfl).elim
  | next l b hb H =>
    have he : R.treeDistance _ ≤ _ := Nat.find_min' _ H
    refine ⟨_,l,lt_of_le_of_lt he ?_,hb⟩
    simp

def standardTree : R.Tree where
  depth := R.treeDistance
  parent x := (R.treecomes x).choose
  edge x := (R.treecomes x).choose_spec.choose
  lower x := (R.treecomes x).choose_spec.choose_spec.1
  joins x := (R.treecomes x).choose_spec.choose_spec.2

namespace Tree
variable {R} (T : R.Tree) {G : Gauge}

lemma parent_ne (x : R.Nonroot) : T.parent x ≠ x.val := by
  intro h
  have hp := T.lower x
  rw [h] at hp; exact (lt_irrefl _ hp)

lemma edge_injective : Injective T.edge := by
  intro a b h
  have ha := T.lower a; have hb := T.lower b
  have hx := T.joins a
  rw [h] at hx
  rcases hx with ⟨i,j⟩|⟨i,j⟩ <;> rcases T.joins b with ⟨u,v⟩|⟨u,v⟩
  · exact Subtype.ext (j.symm.trans v)
  · rw [i.symm.trans u] at ha; rw [← j.symm.trans v] at hb; omega
  · rw [j.symm.trans v] at ha; rw [← i.symm.trans u] at hb; omega
  exact Subtype.ext (i.symm.trans u)

def ties : Finset R.Link := Finset.univ.image T.edge
abbrev Fixed := ↥T.ties
abbrev Mobile := {l : R.Link // l ∉ T.ties}

def twig (a : R.Nonroot) : T.Fixed := ⟨T.edge a,by simp only [ties,Finset.mem_image]; exact ⟨a,Finset.mem_univ _,rfl⟩⟩

def treeGauge (U : T.Fixed → G.El) (v : R.Vertex) : G.El :=
  if h : v = R.root then 1
  else
    let a : R.Nonroot := ⟨v,h⟩
    let p := T.parent a
    let l := T.edge a
    treeGauge U p * (if R.src l=p then U (T.twig a) else (U (T.twig a))⁻¹)
termination_by T.depth v
decreasing_by exact T.lower _

lemma treeGauge_tie (U : R.Configuration G) (B : T.Fixed → G.El) (hm : ∀ l : T.Fixed, U l.val = B l) (l : T.Fixed) :
    R.Vague (T.treeGauge B) U l.val = 1 := by
  obtain ⟨l,hl⟩ := l
  obtain ⟨a,-,rfl⟩ := Finset.mem_image.mp hl
  have hp := hm (T.twig a)
  change U (T.edge a) = _ at hp
  change R.Vague _ _ (T.edge a) = 1; unfold Vague
  have he : treeGauge T B a.val = T.treeGauge B (T.parent a) * (if R.src (T.edge a) = T.parent a then B (T.twig a) else (B (T.twig a))⁻¹) := by rw [treeGauge, dif_neg a.property]
  rcases T.joins a with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;>
    rw [hp,h₁,h₂, he]
  · simp [h₁]
  simp [h₁,(T.parent_ne a).symm, mul_assoc]

def place (U : T.Mobile → G.El) (l : R.Link) := if h : l ∈ T.ties then 1 else U ⟨l,h⟩
@[fun_prop] lemma place_cont : Continuous (T.place (G:=G)) := continuous_pi fun l => by
  simp only [place]; split <;> fun_prop

set_option maxHeartbeats 800000 in
/-- Root-fixed tree gauge removes exactly the Haar variables on the selected
links. This computes the tree-gauge Jacobian (Haar formulation; no
additional determinant). Test e.g. with a gauge-invariant window times the
quotient Wilson Boltzmann factor and insertions. -/
theorem integral_tree (F : R.Configuration G → ℝ) (hF : Continuous F)
    (hi : ∀ g U, F (R.Vague g U) = F U) :
    (∫ U, F U ∂R.orbitPrior G) = ∫ V, F (T.place V) ∂Measure.pi (fun _ : T.Mobile => G.probHaar) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : R.Link => G.El) (· ∈ T.ties)
  let μ := Measure.pi (fun _ : T.Fixed => G.probHaar)
  let ν := Measure.pi (fun _ : T.Mobile => G.probHaar)
  have hh : MeasurePreserving e (R.orbitPrior G) (μ.prod ν) := by
    unfold e μ ν orbitPrior
    convert! measurePreserving_piEquivPiSubtypeProd (fun _ : R.Link => G.probHaar) (· ∈ T.ties) using 1
    congr 1 <;> congr 1
    exact Subsingleton.elim ..
  have he : MeasurePreserving e.symm (μ.prod ν) (R.orbitPrior G) := hh.symm e
  have hfi := hF.integrable_of_hasCompactSupport (μ:=R.orbitPrior G) (HasCompactSupport.of_compactSpace _)
  rw [← he.integral_comp e.symm.measurableEmbedding F, integral_prod (f:=fun x => F (e.symm x))]
  · have ht (x : T.Fixed → G.El) : (∫ y, F (e.symm (x,y)) ∂ν)=∫ V, F (T.place V) ∂ν := by
      let g := T.treeGauge x
      let m (l : T.Mobile) (u : G.El) := g (R.src l.val)*u*(g (R.dst l.val))⁻¹
      let d (U : T.Mobile → G.El) (l : T.Mobile) := m l (U l)
      have hd : MeasurePreserving d ν ν := measurePreserving_pi _ _ (fun l => G.preserve_two_sided (g (R.src l.val)) _)
      have hy (y : T.Mobile → G.El) : R.Vague g (e.symm (x,y)) = T.place (d y) := by
        have hv (i : T.Fixed) : e.symm (x,y) i.val=x i := congr_fun (congr_arg Prod.fst (e.apply_symm_apply (x,y))) i
        have hw (i : T.Mobile) : e.symm (x,y) i.val=y i := congr_fun (congr_arg Prod.snd (e.apply_symm_apply (x,y))) i
        funext i; by_cases h : i∈T.ties
        · rw [place,dif_pos h]; exact T.treeGauge_tie _ x hv ⟨i,h⟩
        simp only [Vague,place,dif_neg h,d,m]; rw [hw ⟨i,h⟩]
      simp_rw [← hi g (e.symm (x,_)), hy]
      calc
        _ = ∫ V, F (T.place V) ∂Measure.map d ν := Eq.symm (integral_map hd.measurable.aemeasurable (f:=fun V => F (T.place V)) (hF.comp T.place_cont).aestronglyMeasurable)
        _ = _ := by rw [hd.map_eq]
    simp_rw [ht,integral_const]; simp; rfl
  exact (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hfi

end Tree
end Regulator
end YM.XSpace
