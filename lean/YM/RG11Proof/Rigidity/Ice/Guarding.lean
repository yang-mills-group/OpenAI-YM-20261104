import YM.RG11Proof.Rigidity.Ice.Vault

/-!
# Supply the f tensor (weight six). Recognition needs actual pure theory
colors and their bracket, not a partonic basis convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD Reads Maxwell.Free Crowd Prism
open scoped Classical BigOperators InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color

def tri (x y z : V) := inner ℝ x (G.ad y z)
lemma group_bracket (u : G.El)(x y : V) : G.ad (G.adjoint u x) (G.adjoint u y)= G.adjoint u (G.ad x y):=by
  apply G.colorMat_injective
  simp only [G.mat_adjoint,G.colorMat_ad, Gauge.conjugate,mul_sub,sub_mul]
  simp only [mul_assoc, ← mul_assoc (star (G.mat u)) (G.mat u), G.mat_star_mul u, one_mul]
lemma tri_group (u : G.El)(x y z : V):tri (G.adjoint u x) (G.adjoint u y) (G.adjoint u z) = tri x y z:=by unfold tri;rw [group_bracket]; exact adSpin_iso ..

def scroll (G : Gauge) (p q w:Flavor 0): WickPol G:=
    ∑ i:G.ColorIndex, ∑ j:G.ColorIndex, ∑ k:G.ColorIndex, (↑(tri (unitColor G i) (unitColor G j) (unitColor G k)):ℂ) • (bit p i * bit q j * bit w k)
lemma scroll_gr (p q w:Flavor 0): grain 6 (scroll G p q w):=by
  unfold scroll; apply MvPolynomial.IsWeightedHomogeneous.sum; intro i _; apply MvPolynomial.IsWeightedHomogeneous.sum; intro j _; apply MvPolynomial.IsWeightedHomogeneous.sum; intro k _
  rw [← MvPolynomial.C_mul']; apply MvPolynomial.IsWeightedHomogeneous.C_mul
  exact ((symbol_hom (flavor 0 i p) (fun t=>t+2)).mul (symbol_hom (flavor 0 j q) (fun i=>i+2))).mul (symbol_hom (flavor 0 k w) (fun t=>t+2))
lemma scroll_real (p q w:Flavor 0):realForm (scroll G p q w)= scroll G p q w:=by unfold scroll;simp_rw [map_sum,Reads.star_smul,map_mul, realBit]; simp

lemma scroll_read (A:TaylorTower G)(p q w:Flavor 0) : probe A (scroll G p q w)=(tri (available (A 0) p) (available (A 0) q) (available (A 0) w):ℂ):=by
  unfold scroll
  let x:= available (A 0) p; let y:=available (A 0) q; let z:=available (A 0) w
  conv_rhs=> change (↑(tri x y z):ℂ); rw [← color_sum x,← color_sum y,← color_sum z]
  simp_rw [map_sum,map_smul,map_mul,bit,symbol_test,smul_eq_mul]
  unfold tri
  simp_rw [map_sum,map_smul,LinearMap.sum_apply,sum_inner, LinearMap.smul_apply,real_inner_smul_left,inner_sum,real_inner_smul_right,Finset.mul_sum]; push_cast
  simp_rw [inner_sum, real_inner_smul_right, Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
  conv_rhs => arg 2; intro i; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_
  change _*((↑(x i):ℂ)*↑(y j)*↑(z k))= _; ring

lemma scroll_fits (p q w:Flavor 0):scroll G p q w ∈ shellSector G 6:=by
  apply sector.mpr
  refine ⟨?_,fun u=> equalPol _ _ (fun A=>?_ )⟩
  · rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]; intro i hi; exact (scroll_gr p q w (MvPolynomial.mem_support_iff.mp hi)).le
  simp_rw [pigment_action,scroll_read,shade,shows_hue,tri_group]

-- Use three actual independent curvature components.
def spout (i:Axis): Flavor 0:= cell 0 i

def spring (hd : 6≤d)(p q w:Flavor 0): News F d:=
  let P:=place F _ (scroll G p q w) (scroll_fits p q w)
  let v:= up F hd P
  have h:writes F _ v=scroll G p q w:=(up_write ..).trans (place_reads ..)
  ⟨6,hd,v,
    writes_inj F _ (by rw [writes_bar, h]; exact scroll_real p q w),
    staircase F hd ▸ LinearMap.mem_range_self _ _,h ▸ scroll_gr p q w⟩
lemma springs_write (p q w:Flavor 0)(hd : 6≤d):writes F d ((spring hd p q w : News F d).v) = scroll G p q w:= (up_write ..).trans (place_reads ..)

private def paste (x y z : V) : TaylorTower G:= fun i=> if h : i=0 then h.symm ▸ (fill 0 x (blade 0 1 (1:ℝ))+fill 0 y (blade 0 2 (1:ℝ))+fill 0 z (blade 0 3 (1:ℝ))) else 0
private lemma pasted (x y z : V) : available (paste x y z 0) (spout 1)=x ∧ available (paste x y z 0) (spout 2)=y ∧ available (paste x y z 0) (spout 3)=z:=by
  have hp (i : Axis)(k) : available (paste x y z 0) (spout i) k=x k*wedge 1 0 i 0 1+y k*wedge 1 0 i 0 2+z k*wedge 1 0 i 0 3:=by
    change spout i (faceMap _ (cp k) (paste x y z 0))=_
    simp [paste,spout,which,cell_price]
  refine ⟨?_,?_,?_⟩ <;> { ext1 k; rw [hp]; simp [wedge] }

lemma Feasible.trio {b : Buffer F d}{t:ℝ}{O:Wheel G}(hd : 6≤d)(h : Feasible b t (steers O))(u:G.El)(x y z:V) :
    let P:= fun v=> O.symm (G.adjoint u (O v))
    tri (P x) (P y) (P z) = tri x y z:=by
  let R := (adSpin u).comp (steers O)
  let P := (steers O.symm).comp R
  let i : News F d:= spring hd (spout 1) (spout 2) (spout 3)
  let A:= paste x y z
  have he : quoteL F (d:=d) i.n (films P A) i.v=quoteL F i.n A i.v:= by
    have hq : (steers O).comp P=R:= ContinuousLinearMap.ext (fun k=> O.apply_symm_apply _)
    rw [h.2 i,h.2 i,reel_film,hq]; unfold R; rw [← reel_film,top_hide]
  change probe _ (MvPolynomial.weightedHomogeneousComponent _ _ _) = probe _ (MvPolynomial.weightedHomogeneousComponent _ _ _) at he
  rw [MvPolynomial.weightedHomogeneousComponent_eq_self i.gr] at he
  change probe _ (writes F d ((spring hd _ _ _ : News F d).v))= probe _ (writes F d ((spring hd _ _ _ : News F d).v)) at he
  rw [springs_write,scroll_read,scroll_read] at he
  obtain ⟨h1,h2,h3⟩:= pasted x y z
  unfold films A at he
  simp_rw [shows_film,h1,h2,h3] at he
  exact Complex.ofReal_injective he
end YM.RG11.Rigidity.Ice
