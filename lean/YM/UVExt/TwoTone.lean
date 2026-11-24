import YM.UVExt.PlaneMode

/-! Sine and cosine lifts together isolate the common α; prices before point-support limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Wilson Function RG Bid Exterior Tensor Matrix Precision Lattice Bloch Work.F03
open scoped Classical ContDiff Topology BigOperators
set_option linter.unusedSimpArgs false
variable {G : Gauge} {n : Side} (a : G.Color)

def melody (n : Side) (z:ℂ) : Dir G n := station (step 0) 1 z a
def coda : PlaqAxes := ⟨⟨0,1⟩,by decide⟩
lemma melody_is (z : ℂ) : melody a n z = wave (c:=n) (step 0) (broadcast 1 a z) := (station_eq ..).symm
lemma tone_price (z : ℂ) (ha : ‖a‖=1) (hz : ‖z‖≤1) : ∀ t i, ‖broadcast 1 a z t i‖ ≤ 1 := fun t i => by
  change ‖if _ then (a i:ℂ)*z else 0‖ ≤ _
  split_ifs
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact (mul_le_of_le_one_right (abs_nonneg _) hz).trans (ha ▸ (by simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) a) ) -- use norm_eval_fun
  simp

lemma cochain_tone (ha : ‖a‖=1) (hz : 4≤n.val) (z : ℂ) (h : ‖z‖≤1) : ‖dColor G n 1 (melody a n z)‖ ≤ 4*ripple (n:=n) ∧ gradD (melody a n z) ≤ 4*ripple (n:=n)^2 := by
  have ht (j : ℕ) : 4*ripple (n:=n)^j*(‖a‖*‖z‖) ≤ 4*ripple (n:=n)^j := by rw [ha,one_mul]; exact mul_le_of_le_one_right (by positivity [ripple_pos n]) h
  exact ⟨le_trans (d_plane _ _ 1 _ <| ripple_cap n hz) (by simpa using ht 1), le_trans (grad_plane _ _ 1 _ <| ripple_cap n hz) (ht 2)⟩

lemma tone_face (x : Site n) (z : ℂ) : dColor G n 1 (melody a n z) (x,plaquette coda) = (cell (step 0) x * (turn (step 0:Site n) 0 * z)).re • a := by
   unfold melody; rw [d_station,shift_station,shift_station]; unfold coda station
   simp only [↓reduceIte]; rw [if_neg (by decide:¬ ((_ : TypeFace 1) = coord 1))]; rw [sub_zero]
lemma tone_bill (x : Site n) (ha : ‖a‖=1) (h : 4 ≤ n.val) :
    ‖dColor G n 1 (melody a n 1) (x,plaquette coda)‖^2 + ‖dColor G n 1 (melody a n Complex.I) (x,plaquette coda)‖^2 ≥ 1/(n.val:ℝ)^2 := by
  simp_rw [tone_face,norm_smul, ha,mul_one]
  let t := cell (step 0:Site n) x; let A := (n.val:ℝ)
  let d := t * turn (step 0:Site n) 0
  change _ ≤ |d.re|^2+ _
  change _ ≤ |d.re|^2+|(t * (turn (step 0:Site n) 0 * Complex.I)).re|^2
  rw [show (t * (turn (step 0:Site n) 0 * Complex.I)).re = -d.im from by rw [←mul_assoc]; unfold d; rw [Complex.mul_re]; simp]
  calc
     1/A^2 = ((n.val:ℝ)⁻¹)^2 := by rw [one_div,inv_pow]
     _ ≤ ‖turn (step 0:Site n) 0‖^2 := pow_le_pow_left₀ (by positivity) (ripple_lower n h) _
     _ = ‖d‖^2 := by change _ = ‖cell _ x * _‖^2; rw [norm_mul, panel_norm,one_mul]
     _ = d.re^2+d.im^2 := by rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
     _ = _ := by rw [sq_abs,sq_abs]; ring

variable {a} {A : Levels G} {m} {p : Clip} {k l : ℝ} {H : ℕ→Bed} {M : ℕ→PathData G} {W : Shadow G} {σ C Λ : ℝ} (ht : Harbor A m k l H M p) (hq : Passing M W σ C Λ p)
include ht hq
set_option maxHeartbeats 300000 in
lemma tone_lower_fixed (ha : ‖a‖=1) (u : ℕ) (h : 4≤(A.S.side m u).val) : let n := A.S.side m u; let f := Tensor.diagonal (hq.economicTensor (A.S.side m u) 2);
    p.direct * n.val^2 ≤ f (melody a n 1) + f (melody a n Complex.I) := by
  intro n f
  let v := melody a n 1; let w := melody a n Complex.I
  let α (j x) := Tensor.diagonal (spray (fun i=>centered n (M i) p) 2 j) x
  have hp (x) : Tendsto (fun j=>α j x) atTop (𝓝 (f x)) := view_cont.continuousAt.tendsto.comp ((hq.centeredLimit n 2|>.1).prodMk_nhds (tendsto_const_nhds (x:=fun _ : Fin 2=>x)))
  apply ge_of_tendsto ((hp v).add (hp w))
  have hm : 4 ≤ n.val := h
  filter_upwards [ht.ties,ht.full n,hq.mask,ht.symmetry u] with i hi hT hv hs
  obtain ⟨u',v',hF⟩ := hT
  have he (t : Dir G n) : ∑ x:Site n, p.direct*‖dColor G n 1 t (x,plaquette coda)‖^2 ≤ gaugeFiscal (H i) t t := by
      rw [metric_pair _ hv hi _ _ hF, Fintype.sum_prod_type]
      refine Finset.sum_le_sum fun z hz=> ?_
      let v (x : PlaqAxes) := p.direct * ‖dColor G n 1 t (z,plaquette x)‖^2 + ‖ellLine (M i) (z,x) t‖^2
      have hq : ∑ x,v x = _ := Finset.sum_congr rfl fun x _=>Eq.symm <| congr_arg₂ (·+·) (congr_arg _ (real_inner_self_eq_norm_sq ..)) (real_inner_self_eq_norm_sq (ellLine (M i) (z,x) t)) -- real_inner? 
      exact le_trans (le_add_of_nonneg_right (sq_nonneg _)) ((Finset.single_le_sum (f:=v) (fun x (_ : x∈Finset.univ)=>by unfold v; positivity [p.quadratic_pos.le]) (Finset.mem_univ coda)).trans_eq hq)
      
  have hs' (t : Dir G n) := stored_fiscal (H i) hi hF hs hv t
  change p.direct * ((n.val:ℝ)^2) ≤ α i v + α i w
  rw [show α i v = gaugeFiscal (H i) v v from hs' v,show α i w=gaugeFiscal _ _ _ from hs' w]
  have hN : (Fintype.card (Site n):ℝ)=((n.val:ℝ)^4:ℝ) := by rw [YM.Lattice.site_card,Nat.cast_pow]
  calc
     _ = ∑ x:Site n,p.direct * (1/(n.val:ℝ)^2) := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hN]; field_simp [show ((n.val:ℝ)≠0) from by exact_mod_cast n.property.ne']
     _ ≤ (∑ x:Site n, p.direct*‖dColor G n 1 v (x,plaquette coda)‖^2) + (∑ x:Site n, p.direct*‖dColor G n 1 w (x,plaquette coda)‖^2) := Finset.sum_le_sum (fun x _ => (mul_le_mul_of_nonneg_left (tone_bill a x ha hm) p.quadratic_pos.le).trans_eq (by rw [mul_add])) |>.trans_eq Finset.sum_add_distrib
     _ ≤ _ := add_le_add (he _) (he _)
end YM.UVExt.Paths
