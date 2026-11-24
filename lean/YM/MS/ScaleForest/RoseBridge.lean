import YM.MS.ScaleForest.HeatScale
import YM.MS.ScaleForest.RoseTensor

/-!
# The proper Rose contraction: first scale and then on the open momentum trace

Two vertices: one actual quartic, one actual nominated Rose arm with its
classical (order zero) two A legs. Then close a loop. Calculate it at two
external A's of same polarization, with (retained) free colours c,d, and
external MOMENTA q,0. Conservation is at the quartic. The mark's momentum
is `-q`. In this projection there's no admixture from the alternative of a
self-pair at the quartic with a single bridge to the mark. Prove that too.
The cut convention means there are two terms, one for each way of assigning
the closing pair. Don't forget the sign from the Fourier derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Quadratic
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum XSpace XSpace.Chiral Native Cylinder
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G : Gauge} {m : ℕ}

abbrev target (mu : Axis) (c d : G.ColorIndex) (q : SectorP m) :=
  [vec (chair m mu) c q,vec (chair m mu) d 0]

abbrev bareRose (G : Gauge) := (roseMark G 0).symbol
abbrev roseConnection (G : Gauge) := firstSew (interaction G 2) (roseMark G 0) (fullShell G)
abbrev stem (G : Gauge) : Mob G := firstSymbol (interaction G 2) (roseMark G 0) (fullShell G)
abbrev cluster (G : Gauge) := loop (fullShell G) (roseConnection G)
def loopKernel (G : Gauge) (z : ℂ) : Mob G := closeG (A0 G 0) z 0 (stem G)

theorem stem_eq (G : Gauge) (m : ℕ) (l : Legs (Shore G m)) :
    stem G m l = ∫ t in (0:ℝ)..1, bridgeG (radial G t) (top4 G) (bareRose G) m l := by
  have hx := congr_fun (congr_fun (first_radial (interaction G 2) (roseMark G 0) 0).1 m) l
  simpa only [posing,exp_zero,quartic_symbol,factor, Bool.false_eq_true, if_false,
    Complex.ofReal_one,one_mul] using hx

-- Helpers for restricting component sums to gauge legs
theorem onlyAs {V : Type} [AddCommMonoid V] (F : Cfield G m → V)
    (hf : ∀ i, (∀ j a,i ≠ at_g j a) → F i=0) :
    (∑ i:Cfield G m,F i)=∑ a:G.ColorIndex,∑ i:L m,F (at_g i a) := by
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _=> ?_
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_bool,Fintype.sum_option]
  have h (z : Option (L m)) : F ((z,true),i)=0:= hf _ (by intro _ _; simp [at_g])
  simp_rw [h,zero_add]; rw [hf ((none,false),i) (by intro _ _; simp [at_g]), zero_add]

theorem radial_vec (x y : L m) (a c : G.ColorIndex) (p : SectorP m) (r : ℝ) :
    radial G r m (at_g x a) (at_g y c) p = if a=c then ↑(City.brush r p * precision x y p) else 0 := rfl
theorem radial_sym (x y : L m) (a : G.ColorIndex) (p : SectorP m) (r : ℝ) :
    radial G r m (at_g x a) (at_g y a) p = radial G r m (at_g y a) (at_g x a) (-p) := by
  simp only [radial_vec,if_true, City.brush_neg, k_even, realK x y]

theorem sewn_uses (K : Rip G) {F H : Mob G} (hf : GaugeLegs F) (hp : GaugeLegs H) : GaugeLegs (bridgeG K F H) := by
  intro m l i hi h
  unfold bridgeG
  rw [scatter_congr _ l _ (fun _ _=> (0:ℂ)) ?_]; exact map_zero (allocate ..)
  intro s t hS
  rcases List.mem_append.mp ((split_perm hS).mem_iff.mpr hi) with he|he
  · refine Finset.sum_eq_zero fun j _=> Finset.sum_eq_zero fun k _=> ?_
    rw [hf m _ i (List.mem_cons_of_mem _ he) h]; simp
  refine Finset.sum_eq_zero fun j _=> Finset.sum_eq_zero fun k _=> ?_
  rw [hp m _ i (List.mem_cons_of_mem _ he) h]; simp

theorem stem_uses (G : Gauge) : GaugeLegs (stem G) := by
  intro m l i hi hL; rw [stem_eq]
  simp_rw [sewn_uses _ (top_gauge G) onlyGauge m l i hi hL]
  simp

def attachment (r : ℝ) (l s : Legs (Shore G m)) : ℂ :=
  ∑ i : Cfield G m, ∑ j:Cfield G m,
    Heat.radius parity (radial G r m) i j (top4 G m) (bareRose G m) l s

theorem four_to_two (r : ℝ) (l s : Legs (Shore G m)) :
    attachment r l s = ∑ a:G.ColorIndex,∑ i:L m,∑ j:L m,
        2 * radial G r m (at_g i a) (at_g j a) (-net l) * top4 G m (vec i a (-net l) :: l) *
          bareRose G m (vec j a (net l) :: s) := by
  unfold attachment; rw [onlyAs]
  · refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun i _=> ?_
    rw [onlyAs]
    · rw [Finset.sum_eq_single a]; apply Finset.sum_congr rfl; intro k _
      simp only [radius, neg_neg,show parity (at_g k a)=false from rfl,cross_false,one_mul]
      intro b _ hb; apply Finset.sum_eq_zero; intro k _
      unfold radius; dsimp only; rw [radial_vec]; simp [Ne.symm hb]
      simp
    intro j h; unfold radius; dsimp only; unfold bareRose
    rw [onlyGauge m _ (j,- -net l) (List.mem_cons_self) (fun ⟨i,z,ht⟩ => h i z ht),mul_zero]
  intro i hi
  refine Finset.sum_eq_zero fun j _=> ?_
  unfold radius; dsimp only; rw [top_gauge G m _ (i,-net l) (List.mem_cons_self) (fun ⟨x,y,h⟩ => hi x y h)]; simp

theorem empty_attach (r : ℝ) (l s : Legs (Shore G m)) (hx : l.length ≠ 3) : attachment r l s=0 := by
  rw [four_to_two]; apply Finset.sum_eq_zero; intro a _
  refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> ?_
  have ht := (interaction G 2).slots
  rw [quartic_symbol] at ht
  have hv : (interaction G 2).rank = 4 := rfl
  rw [ht m _ (by rw [mod_int,hv]; simp; omega)]; simp

private theorem split_four (r : ℝ) (i j k w : Shore G m) (hi : parity i.1 = false) (hj : parity j.1=false)
    (hk : parity k.1=false) (hw : parity w.1=false) :
      bridgeG (radial G r) (top4 G) (bareRose G) m [i,j,k,w] =
        attachment r [i,j,k] [w] + attachment r [i,j,w] [k] +
        attachment r [i,k,w] [j] + attachment r [j,k,w] [i] := by
  change scatter (field parity) _ (attachment r) = _
  simp_rw [scatter_cons,scatter_nil,field,hi,hj,hk,hw,cross_false,one_mul]
  simp (disch:=simp) only [ empty_attach ]; abel

theorem attach_zero_terminal {x : L m} (l : Legs (Shore G m)) (c : G.ColorIndex) (r : ℝ) :
    attachment r l [vec x c 0]=0 := by
  rw [four_to_two]; simp [bareRose,bare_tensor,incoming,gradient_zero]

theorem attach_zero_current (r : ℝ) (l s : Legs (Shore G m)) (ht : net l=0) :
    attachment r l s=0 := by
  rw [four_to_two]; simp only [ht,neg_zero,radial_vec,City.brush,Momentum.sq,Landau.precision,Landau.delta,
    Pi.zero_apply]; simp

def sing (r : ℝ) (mu : Axis) (s t : L m) (a c d : G.ColorIndex) (p k : SectorP m) : ℂ :=
  if s=chair m mu then 0 else
    -4 * angle a c d * (City.brush r k : ℝ) * (k.sq:ℝ) * (Rose.f:ℂ)^2 *
      (∑ i:P, (gradient false i k s:ℂ)*(gradient false i p t:ℝ))

private theorem one_pair_sing (r : ℝ) (mu : Axis) (s t : L m) (a c d : G.ColorIndex) (p k : SectorP m) :
    (∑ i:L m, ∑ j:L m, 2*radial G r m (at_g i a) (at_g j a) (-k) *
      (if i=s ∧ i≠chair m mu then -2 * angle a c d else 0)* incoming j t k (-p)) = sing r mu s t a c d p k := by
  unfold sing; split <;> rename_i h
  · refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> ?_
    rw [if_neg (fun ⟨hi,hq⟩ => hq (hi.trans h))]; ring
  rw [Finset.sum_eq_single s]
  · simp only [h,ne_eq,not_false_eq_true,and_self,if_true, radial_vec,k_even,City.brush_neg,
      incoming,gradient_neg]
    push_cast; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _=> ?_
    let K : ℂ := -4 * angle a c d * (City.brush r k : ℝ) * ((↑√2:ℂ)⁻¹)^2 * (gradient false u p t : ℝ)
    calc
      _ = K * ( (∑ j:L m, precision s j k * gradient false u k j : ℝ):ℂ ) := ?_
      _ = _ := ?_
    · rw [Complex.ofReal_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; unfold K; push_cast; ring
    rw [polar_gradient]; unfold K; push_cast; ring
  · intro i _ hv; simp [hv]
  simp

theorem attach_into (r : ℝ) (mu : Axis) (s t : L m) (a c d : G.ColorIndex) (p q : SectorP m) :
    let k := p+q
    attachment r (vec s a p :: target mu c d q) [vec t a (-p)] = sing r mu s t a c d p k := by
  intro k; rw [four_to_two]
  have he : net (vec s a p :: target mu c d q) = k := by simp [target,net,k,vec]
  rw [he]; rw [ Finset.sum_eq_single a]
  · unfold target; simp_rw [top_pair,bareRose,bare_tensor,if_true]; exact one_pair_sing ..
  · intro i _ hv; simp_rw [bareRose,bare_tensor,if_neg (Ne.symm hv),mul_zero,Finset.sum_const_zero]
  simp

theorem assignments (r : ℝ) (mu : Axis) (s t : L m) (a c d : G.ColorIndex) (p q : SectorP m) :
    bridgeG (radial G r) (top4 G) (bareRose G) m (vec s a p :: vec t a (-p) :: target mu c d q) =
      sing r mu s t a c d p (p+q) + sing r mu t s a c d (-p) ((-p)+q) := by
  unfold target
  rw [split_four _ _ _ _ _ rfl rfl rfl rfl,attach_zero_terminal,attach_zero_current]
  swap
  · simp [net,vec]
  have ht := attach_into r mu t s a c d (-p) q
  rw [neg_neg] at ht
  rw [zero_add,zero_add]; exact congr_arg₂ (·+·) (attach_into ..) ht
end YM.MS.ScaleForest.Quadratic
