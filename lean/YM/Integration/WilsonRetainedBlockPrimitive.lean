import YM.Integration.WilsonRetainedBlockLogarithm

/-! Recombination of the nonlinear block on its original finite torus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedBlockPrimitive
open Function Finset Filter Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port Work.G05 Analysis
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}

/-- The path field and the direct Wilson remainder at the same path cutoff. -/
def kinetic {n : Side} (a : ℝ) (U : Config G n) (x : Twin n→G.Color) : ℝ :=
  (∑ p : Cell n,a*flaw (faceValue U p)) + ∑ i, ‖x i‖^2/2

theorem spring (S : StepData c f) (Q V : Config G c) (j : Bond c) :
    S.kernel.penalty*flaw (V j*(Q j)⁻¹)+‖Tube.Z S Q V j‖^2/2 =
      S.kernel.penalty*G.price (V j*(Q j)⁻¹) := by
  unfold flaw Tube.Z
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt S.kernel.penalty_pos.le,G.chord_price]
  ring

/-- The signed local summands reassemble the true fine and coarse kinetic
forms and the full Wilson blocking penalty at this one finite period. -/
theorem action (T : Tube G S) (s : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    (∑ i, loft T s U k V true i) =
      kinetic T.high.direct U (T.Xf (till s) U) +
      (∑ i, S.kernel.penalty*G.price (V i*((S.prediction U k) i)⁻¹)) -
      kinetic T.low.direct V (T.Xn (till s) V) := by
  let R:=till s
  let Q:=S.prediction U k
  let w:=T.Xn R V
  let u:=T.Xf R U
  let z:=Tube.Z S Q V
  let e:=canopyF T R V
  let a:=canopyI T R V
  let g:=canopyN T R V
  have ef := arity (T.Φ R V) e w
  have af := arity (T.Φ' R V) a w
  have gf := arity (T.N R V) g w
  have eu := arity (T.Φ R V) u w
  have az := arity (T.Φ' R V) z w
  change (∑ i, loft T s U k V true i) =
    kinetic T.high.direct U u + (∑ i,S.kernel.penalty*G.price (V i*(Q i)⁻¹)) -
      kinetic T.low.direct V w
  have sp : (∑ i,S.kernel.penalty*flaw (V i*(Q i)⁻¹))+(∑ i,‖z i‖^2)/2 =
      ∑ i,S.kernel.penalty*G.price (V i*(Q i)⁻¹) := by
    rw [Finset.sum_div,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => spring S Q V i
  simp only [loft,Spot,Fintype.sum_sum_type,Sum.elim,if_true,flora,nora,stormC,stormL,stormD,
    stormN,effective,visual,kinetic]
  change (∑ p : Cell f,(T.high.direct*flaw (faceValue U p)+ ∑ i : Bool, ‖u (p,i)-e (p,i)‖^2/2)) +
    ((∑ i : Bond c, (S.kernel.penalty*flaw (V i*(Q i)⁻¹)+‖z i-a i‖^2/2)) +
    ((∑ i : Cell c, (-(T.low.direct)*flaw (faceValue V i) +
      ((∑ j : Bool,inner ℝ (w (i,j)) (unzip (T.Φ R V) u (i,j)+unzip (T.Φ' R V) z (i,j)-w (i,j)))+
       (∑ j : Bool,inner ℝ (w (i,j)) (w (i,j)-
         (unzip (T.Φ R V) e (i,j)+unzip (T.Φ' R V) a (i,j)+unzip (T.N R V) g (i,j)))/2))))+
    ∑ i,‖g i‖^2/2)) = _
  change (∑ i,inner ℝ (e i) (e i))=_ at ef
  change (∑ i,inner ℝ (a i) (a i))=_ at af
  change (∑ i,inner ℝ (g i) (g i))=_ at gf
  change (∑ i,inner ℝ (e i) (u i))=_ at eu
  change (∑ i,inner ℝ (a i) (z i))=_ at az
  simp_rw [real_inner_self_eq_norm_sq] at ef af gf
  have eu' : (∑ i,inner ℝ (u i) (e i)) = ∑ i,inner ℝ (w i) (unzip (T.Φ R V) u i) :=
    (Finset.sum_congr rfl fun i _ => real_inner_comm _ _).trans eu
  have az' : (∑ i,inner ℝ (z i) (a i)) = ∑ i,inner ℝ (w i) (unzip (T.Φ' R V) z i) :=
    (Finset.sum_congr rfl fun i _ => real_inner_comm _ _).trans az
  simp only [norm_sub_sq_real,
    inner_sub_right,inner_add_right,real_inner_self_eq_norm_sq,neg_mul]
  simp only [Twin,Fintype.sum_prod_type] at ef af gf eu' az' sp ⊢
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib,←Finset.sum_div,
    ←Finset.mul_sum] at *
  linarith only [ef,af,gf,eu',az',sp]

/-- The local quadratic subtraction is returned exactly once, before any
subsequent marked Wick contraction or kinetic reset. -/
theorem original (T : Tube G S) (s : ℝ) (k : S.Choices) (x : ZipP G c f) :
    let U:=shaft S x
    let V:=increment 1 x.1
    (∑ p,ivy T s k p x) +
      (∑ i : Rod c f, ‖Scroll.freely T s V k i + straightened T (till s) V x.2 i‖^2/2) =
      kinetic T.high.direct U (T.Xf (till s) U) +
        (∑ i,S.kernel.penalty*G.price (V i*((S.prediction U k) i)⁻¹)) -
        kinetic T.low.direct V (T.Xn (till s) V) := by
  dsimp only
  rw [← action T s (shaft S x) k (increment 1 x.1)]
  unfold ivy squarepot
  rw [Finset.sum_sub_distrib,spots_sum S]
  ring

end YM.Integration.WilsonRetainedBlockPrimitive
end
