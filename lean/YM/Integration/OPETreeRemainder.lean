import YM.Integration.OPEMSReport
import YM.RG11Proof.Fields.FreeScale
import YM.MSbar.TreeOPE.Answer

/-! The tree contraction and Taylor expansion of arbitrary separated
clusters, with each output assigned to the same physical field quotient
as the independent MS report. The exterior stays at fixed distance. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPETreeRemainder
open Function Filter Set Asymptotics FVA2 Maxwell Maxwell.Free Maxwell.Wick Pert.Position
open RG11.Fields RG11.Grove RG11.Neighborhood MSbar.OPE
open scoped Classical BigOperators Topology

variable {G : Gauge} {F : Labels.Frames G} {n m i d : ℕ}

def polynomials (F : Labels.Frames G) (d : ℕ) (v : Fin n → E F d) : Fin n → WickPol G :=
  address F d ∘ v

/-- The Taylor/Wick output of engineering dimension k, as a genuine
field of the physical quotient rather than a vector of probe values. -/
def output (F : Labels.Frames G) (x : conf n) (v : Fin n → E F i) (k : ℕ) : E F k :=
  (fields F k).symm ⟨glued x.property (polynomials F i v) k,
    glued_physical (fun g a => (sector.mp (address_in F i (v a))).2 g) x.property k⟩

theorem output_polynomial (x : conf n) (v : Fin n → E F i) (k : ℕ) :
    address F k (output F x v k) = glued x.property (polynomials F i v) k := by
  rw [address_eval, output, LinearEquiv.apply_symm_apply]

theorem output_homogeneous (x : conf n) (v : Fin n → E F i) (k : ℕ) :
    pureW scaleW k (address F k (output F x v k)) := by
  rw [output_polynomial]; exact glued_grade .. 

theorem basis_homogeneous (V : Warehouse G) (a : lab V.F i) :
    pureW scaleW (RG11.Window.grade V.F i a) (address V.F i ((tower V.F i).b a)) := by
  rw [← Fountain.common_L V]
  intro z hz
  exact congrArg Prod.fst ((Extra.FD.weight_collapse z).symm.trans ((tower V.F i).alive a hz))

variable (V : Warehouse G) {Q : MS.Land.Booked (FVA2.ColorCode.wings G)}
    (M : MS.Land.MS_Data G Q) (μ : ℝ)

def paired (k : ℕ) (x : Points (n+m)) (v : Fin n → E V.F i) (w : Fin m → E V.F d) : ℂ :=
  Fountain.phys V M μ k x (max i d)
    (Fin.append (RG11.Fields.up V.F (le_max_left i d) ∘ v)
      (RG11.Fields.up V.F (le_max_right i d) ∘ w))

theorem paired_tree (x : Points (n+m)) (hx : x ∈ conf (n+m))
    (v : Fin n → E V.F i) (w : Fin m → E V.F d) :
    paired V M μ 0 x v w = MSbar.Tree.finitePart 1 x
      (Fin.append (polynomials V.F i v) (polynomials V.F d w)) := by
  rw [paired, Fountain.vintage V M μ x hx, PositionX.visible_eq, MSbar.Tree.four _ hx]
  congr 1
  funext b
  have ht {e j : ℕ} (h : e ≤ j) (z : E V.F e) :
      address V.F j (RG11.Fields.up V.F h z) = address V.F e z := by
    rw [← Fountain.common_L V, RG11.Fields.up_write, Fountain.common_L V]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) b
  · simp only [Function.comp_apply, Fin.append_left, polynomials]
    exact ht _ _
  · simp only [Function.comp_apply, Fin.append_right, polynomials]
    exact ht _ _

theorem exterior_apart (y : Tail m) : foreign (spotX y.c) y.y := by
  intro _ j he
  apply Fin.succ_ne_zero j
  apply y.apart
  change Points.cons _ _ j.succ = Points.cons _ _ 0
  change y.c = y.y j at he
  simpa [Points.cons] using he.symm

/-- The complete tree-level expansion against this separated exterior,
simultaneously retaining every output weight through H. The normalized
remainder is bounded by a constant times the (H+1)-st length power. -/
theorem ray_remainder (x : conf n) (y : Tail m) (v : Fin n → E V.F i) (w : Fin m → E V.F d)
    (weights : Fin n → ℕ) (hv : ∀ a, pureW scaleW (weights a) (polynomials V.F i v a))
    (H : ℕ) :
    (fun r : ℝ => (r : ℂ) ^ (∑ a, weights a) * paired V M μ 0 (driven r x.val y) v w -
      ∑ k ∈ Finset.range (H+1), (r : ℂ)^k *
        paired V M μ 0 (close y) (fun _ : Fin 1 => output V.F x v k) w) =O[𝓝[>] 0]
      (fun r : ℝ => r^(H+1)) := by
  have hfar := exterior_apart y
  have hback (k : ℕ) : paired V M μ 0 (close y) (fun _ : Fin 1 => output V.F x v k) w =
      MSbar.Tree.finitePart 1 (combo (spotX y.c) y.y)
        (Fin.append (solo (glued x.property (polynomials V.F i v) k)) (polynomials V.F d w)) := by
    rw [paired_tree V M μ (close y) (OPEMSReport.close_conf y)]
    have hc : polynomials V.F k (fun _ : Fin 1 => output V.F x v k) =
        solo (glued x.property (polynomials V.F i v) k) :=
      funext (fun _ => output_polynomial x v k)
    rw [hc]
    rfl
  have h := MSbar.OPE.remainder x.property hv y.c (Points.tail_in y.apart) hfar
    (polynomials V.F d w) H
  apply h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [(contracts (x := x.val) y.c y.y hfar).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hsep hr
  have hjoint : driven r x.val y ∈ conf (n+m) :=
    combination (safe x.property y.c hr) (Points.tail_in y.apart) hsep
  simp only [paired_tree V M μ _ hjoint, hback]
  rfl

theorem basis_remainder (x : conf n) (y : Tail m)
    (u : sheaf V.F n i) (w : sheaf V.F m d) (H : ℕ) :
    let v := (tower V.F i).b ∘ u
    let z := (tower V.F d).b ∘ w
    (fun r : ℝ => (r : ℂ) ^ worth u * paired V M μ 0 (driven r x.val y) v z -
      ∑ k ∈ Finset.range (H+1), (r : ℂ)^k *
        paired V M μ 0 (close y) (fun _ : Fin 1 => output V.F x v k) z) =O[𝓝[>] 0]
      (fun r : ℝ => r^(H+1)) :=
  ray_remainder V M μ x y _ _ (RG11.Window.grade V.F i ∘ u)
    (fun a => basis_homogeneous V (u a)) H

end YM.Integration.OPETreeRemainder
