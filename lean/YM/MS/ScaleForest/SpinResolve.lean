import YM.MS.ScaleForest.Halves
import YM.MS.ScaleForest.RoseTensor
/-!
# Resolving a local kinetic term: open tensor in all sectors

Use this for the AA symbol at opposite momenta, not assuming anything
about off-course components. Applies also to a pole polynomial of NOT the
whole theory but a family of graphs with true-coordinates Sturdy, e.g.
a ghost loop. Thus don't need a rotationally-contracted-in-continued-
dimension calculation (may lose finite terms). Keep the external 4-plane
price, both transverse and longitudinal values, and equality in all
continued open probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.TwoPoint
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif
open Momentum
open scoped Topology ContDiff InnerProductSpace
variable {G : Gauge} {m n : ℕ}

abbrev word (i j : L m) (a b : G.ColorIndex) (p : SectorP m) := [vec i a p,vec j b (-p)]

abbrev kinetic (W : Mob G) (a b : G.ColorIndex) (p : SectorP m) (i j : L m) := W m (word i j a b p)

abbrev zeroDirection (m : ℕ) : L m := rises (Nat.zero_le m) (0:Axis)
abbrev trans (m : ℕ) : L m := rises (Nat.zero_le m) (1:Axis)
abbrev primary (m : ℕ) := spray (zeroDirection m)

lemma torch_equiv {U : Mob G} (a b : G.ColorIndex) (p : SectorP m) (i j : L m) :
    Tad U 4 m (word i j a b p)= reading 2 (fun x=> U m (word i j a b (x•p))) := by
  rw [t_bud U (j:=2),torch_at]; simp only [word, vec,ray_go,List.map_cons,List.map_nil,smul_neg]
  rfl

lemma spray_price (i : L m) : (spray i).sq=1:= by simp [Momentum.sq,spray,Pi.single_apply,ite_pow]

variable (W : Mob G) (a b : G.ColorIndex)
def along := kinetic W a b (primary 0) (zeroDirection 0) (zeroDirection 0)
def across := kinetic W a b (primary 0) (trans 0) (trans 0)
variable {W} (hW : Sturdy true W)

include hW
theorem lift_kinetic (p : SectorP m) (i j : L m) (ht : m≤n) :
    kinetic W a b (Left ht p) (rises ht i) (rises ht j)= kinetic W a b p i j := by
  unfold kinetic; rw [ ← hW.grows ht _ ]
  congr 1; simp only [word,vec, Arts.lift, List.map, Prod.map_apply]; rw [map_neg]; rfl

theorem pricing_zero : kinetic W a b (primary m) (zeroDirection m) (zeroDirection m) = along W a b := by
  unfold primary; rw [← send_spray]; exact lift_kinetic a b hW _ _ _ _

theorem axis_parity (S : Spin (L m)) (p : SectorP m) (i j : L m) : kinetic W a b p i j =
    ∑ i':L m,(S.profile i i':ℂ)* ∑ j':L m,(S.profile j j':ℂ)*kinetic W a b (S.turn p) i' j' := by
  obtain ht:= congr_fun ( hW.turn m S (fun h=> Bool.noConfusion h) ) (word i j a b p)
  change (leggo G.ColorIndex S).beam _ [vec i a p, vec j b (-p)]=_ at ht
  simp_rw [vec,at_g,fromV, map_neg,peeps] at ht; exact ht.symm

theorem simple_cols (S : Spin (L m)) (p : SectorP m) (i i' j j' : L m) (x y : ℝ)
    (hi : S.turn (spray i)= x • spray i') (hj : S.turn (spray j)= y • spray j') : kinetic W a b p i j=
      (x:ℂ)*(y:ℂ)*kinetic W a b (S.turn p) i' j' := by
  rw [axis_parity a b hW S]; unfold profile; rw [hi,hj]; simp [spray, Pi.single_apply, apply_ite,ite_mul,mul_assoc]

theorem diagonal_off (i j k : L m) (h:i≠j) : kinetic W a b (spray k) i j=0 := by
  by_cases he:i=k
  · subst i; have hx:j≠k:=Ne.symm h
    obtain ht:= simple_cols a b hW (spark j) (spray k) k k j j 1 (-1) (by simpa using sees_away hx) (by simpa using sees_p j)
    rw [sees_away hx] at ht; exact neg_eq_self.mp (by simpa using ht.symm)
  obtain ht:= simple_cols a b hW (spark i) (spray k) i i j j (-1) 1 (by simpa using sees_p i) (by simpa using sees_away h)
  rw [sees_away he] at ht; exact neg_eq_self.mp (by simpa using ht.symm)

theorem trans_resolves (i : L m) (hi : i≠zeroDirection m) : kinetic W a b (primary m) i i= across W a b := by
  let k:=trans m
  have hv : k≠zeroDirection m := (rises (Nat.zero_le m)).injective.ne (by decide)
  have hV : kinetic W a b (primary m) k k=across W a b:= by
    unfold primary; rw [← send_spray]; exact lift_kinetic a b hW _ _ _ _
  rw [← hV]; by_cases he : i=k; · rw [he]
  have ht : spray i ≠ spray k:= by intro hh; have := congr_fun hh i; simp [spray,he] at this
  let S:= tilt _ (sub_ne_zero.mpr ht)
  have hS : S.turn (spray i)= (1:ℝ) • spray k := by rw [one_smul]; exact turns _ _ ht (by simp_rw [spray_price])
  rw [simple_cols a b hW S (primary m) i k i k _ _ hS hS, show S.turn (primary m)=primary m from ?_]; simp only [Complex.ofReal_one,one_mul]
  apply floors; rw [pair_left,pair_sub]; unfold primary; simp [zap,hi,hv]

omit hW
variable (he : Home W 4) (hP : kPrice W)

-- At positive scale, can use homogeneity directly without the price he;
-- at scale zero it vanishes by Taylor degree > 0.
include he
theorem scale_kinetic (x : ℝ) (hx : 0 < x) (i j : L m) (p : SectorP m) :
    kinetic W a b (x•p) i j=(x:ℂ)^2 * kinetic W a b p i j := by
  let L:= word i j a b p
  have ht:= congr_fun (congr_fun (he (Real.log x)) m) L; unfold plow at ht
  rw [show mass L=2 from rfl, Int.cast_ofNat, Nat.cast_ofNat,
      show (-(4:ℂ))+2= -2 from by norm_num,show sr (Real.log x) L = word i j a b (x • p) from ?_] at ht
  swap
  · simp only [sr,L,word,List.map,Real.exp_log hx,vec,smul_neg]
  have hV : amount (-2) (Real.log x)= (x:ℂ)⁻¹*(x:ℂ)⁻¹:= by
    rw [show (-2:ℂ)= -1+-1 from by norm_num, amount_add]; simp_rw [show amount (-1) (Real.log x) = _ from
      (show amount (-1) (Real.log x)=(x:ℂ)⁻¹ by unfold amount; rw [ mul_neg_one, ← Complex.ofReal_neg,
        ← Complex.ofReal_exp, Real.exp_neg,Real.exp_log hx, Complex.ofReal_inv]) ]
  rw [hV] at ht; unfold kinetic; rw [← ht]; have hu : (x:ℂ)≠0:=by exact_mod_cast hx.ne'
  field_simp

include hP
theorem vanishes (i j : L m) : kinetic W a b 0 i j=0 := by
  unfold kinetic; rw (occs:=.pos [1]) [he.complete hP]; rw [torch_equiv]; simp [reading, iteratedDeriv_const]

omit he hP
def tensor2 (c d : ℂ) (p : SectorP m) (i j : L m) := (if i=j then d * p.sq else 0) + (c-d) * p i * p j

lemma primary_ne (m : ℕ) : (0:ℝ)< Momentum.sq (primary m) := by rw [spray_price]; norm_num

include he hP hW
/-- Given longitudinal and transverse value of an actual h4 term, identify
it on ALL AA words with physical momentum conservation. Include m large
when sewing it on an already continued multi-momentum object too. -/
theorem summation_rule (p : SectorP m) (i j : L m) : kinetic W a b p i j =
    tensor2 (along W a b) (across W a b) p i j := by
  by_cases hx : p=0; · subst p; rw [vanishes a b he hP]; simp [tensor2,Momentum.sq]
  obtain hp:= Arts.sq_gt p hx; let x:= Real.sqrt p.sq
  let k:=zeroDirection m; have hxx : 0<x:=sqrt_pos.mpr hp
  let L := x • primary m
  have hL : p.sq=L.sq:= by unfold L; rw [Momentum.scaling, spray_price,mul_one, Real.sq_sqrt hp.le]
  have hS : ∃ S:Spin (Arts.L m), S.turn p=L:= by
    by_cases hv : p=L; exact ⟨⟨ContinuousLinearEquiv.refl .., fun _ _=> rfl⟩,hv⟩; exact ⟨ tilt _ ( sub_ne_zero.mpr hv),turns _ _ hv hL⟩
  obtain ⟨S,hS⟩:=hS
  -- diagonalize and transport the two pieces
  let A:=across W a b; let B:= along W a b-A
  have ht (i j : Arts.L m) : kinetic W a b (S.turn p) i j= (x:ℂ)^2 * ((if i=j then A else 0) + if i=k ∧ j=k then B else 0) := by
    rw [hS,scale_kinetic a b he x hxx]; by_cases hi:i=j; · subst j; by_cases hm:i=k; subst i; rw [pricing_zero a b hW]; unfold B A; simp; rw [trans_resolves a b hW i hm]; unfold A; simp [hm]
    rw [diagonal_off a b hW i j k hi]; simp [hi,show ¬ (i = k ∧ j=k) from fun ⟨h,h'⟩=>hi (h.trans h'.symm)]
  have heQ (i : Arts.L m) : S.profile i k*x = p i := by
    have hv := S.rad (spray i) p; rw [hS] at hv; unfold L primary at hv; simp [pairing,spray,Pi.single_apply,mul_ite,ite_mul] at hv
    exact hv
  rw [axis_parity a b hW S]; simp_rw [ht]
  let U (l r:Arts.L m) := (S.profile i l : ℂ)*(S.profile j r:ℂ)
  calc
    (∑ l:Arts.L m, _)= (∑ l:Arts.L m, U l l) * ( (x:ℂ)^2 * A) + U k k*((x:ℂ)^2*B) := ?_
    _ = _ := ?_
  · simp_rw [Finset.mul_sum, mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
    simp [U,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_eq_single k]; simp; intro i _ hi; simp [hi]; simp
  rw [show (∑ l:Arts.L m,U l l) = ((if i=j then 1 else 0):ℂ) from ?_]
  swap
  · obtain hv:= S.weights i j; unfold U; simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum,hv]; split_ifs <;> simp
  unfold U tensor2; rw [← heQ, ← heQ, ← Real.sq_sqrt hp.le]; push_cast; split <;> unfold A B x <;> ring
end YM.MS.ScaleForest.TwoPoint
