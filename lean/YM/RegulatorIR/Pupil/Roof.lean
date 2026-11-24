import YM.RegulatorIR.Pupil.Lucent

/-!
# Test-line coefficient absolute bounds
Fitting per native t. Shadow smallness not truncation; bound polynomial
terms with the full Ward pole power. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Laurent
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{f:Side}{I Y:Type}{p k u m r n:ℕ}
variable {H C d a:ℝ≥0∞}

def Wt (x v:Cover):ℝ := 1+(size (v-x):ℝ)
def St (x v:Cover):ℝ≥0∞:= 1+ Momentum.extent (v-x)
lemma capsS (x y:Cover): 1 ≤ Wt x y:=by unfold Wt; linarith [show 0≤(size (y-x):ℝ) by positivity] -- fails
lemma st_def (x y: Cover) : St x y= ENNReal.ofReal (Wt x y):=by unfold Wt St Momentum.extent; rw [ENNReal.ofReal_add (by simp) (by positivity)];simp
lemma st_step (p v:Cover)(i:Axis) : St p (v+step i) ≤ 2*St p v:=by
 have hp: Momentum.extent (Lattice.step i:Cover)=(1:ℝ≥0∞):=by unfold Momentum.extent size; simp only [step_apply]; rw [sum_eq_single i];simp;intro j _ hj;simp [hj];simp
 unfold St; rw [show v+step i-p=(v-p)+step i by abel]; apply le_trans (add_le_add_right (Momentum.extent_add ..) 1)
 rw [hp,← add_assoc,two_mul]; exact add_le_add_right (show 1≤1+Momentum.extent (v-p) from le_self_add) _
lemma st_w (x:Tuple (Long I) r)(p:Cover)(j:Fin r) : St p (area (x j))≤ wall p 1 1 x:=by unfold St Momentum.wall; rw [pow_one]; apply add_le_add_right; apply le_trans _ (Finset.single_le_sum (fun (i:Fin r) _=>show 0 ≤ awayZ p (x i) 1 from bot_le) (mem_univ j)); unfold awayZ award; rw [Nat.cast_one,inv_one,one_mul,one_smul,extent_rev]
lemma w_imp (p:Cover)(x: Tuple (Long I) r) : wall p 1 1 x ^u= wall p 1 u x:=by unfold Momentum.wall; rw [pow_one]
lemma olderW (p:Cover) (k u:ℕ) (h:k ≤u)(x:Tuple (Long I) r): wall p 1 k x≤ wall p 1 u x:=by unfold Momentum.wall; exact pow_le_pow_right₀ le_self_add h

lemma golden {X Y : G.Color}: ‖(X,Y)‖ₑ=max ‖X‖ₑ ‖Y‖ₑ := by rw [← ofReal_norm,← ofReal_norm,← ofReal_norm,Prod.norm_def,ENNReal.ofReal_max]
def TightF (p:Cover)(H:ℝ≥0∞) (A:BEdge G) := ∀ x: Edge Cover,‖A x‖ₑ≤ H*St p x.1
def TightS (p:Cover)(H:ℝ≥0∞)(A:Cover→G.Color) := ∀ x,‖A x‖ₑ≤ H*St p x
lemma tight_trip {A:BEdge G}{σ:Cover→ G.Color}{p:Cover} (h:TightF p H A)(hk:TightS p H σ)(x:Edge Cover) : ‖violet A σ x‖ₑ≤ (H+2*H)* St p x.1:=by
 rw [show ‖violet A σ x‖ₑ=max ‖A x‖ₑ ‖(σ x.1,σ _ )‖ₑ from ?_,golden]
 rw [add_mul]; apply max_le (le_trans (h x) le_self_add); apply max_le ((hk x.1).trans le_self_add)
 apply le_trans (hk _); apply le_trans (mul_le_mul_right (st_step p _ x.2) H)
 rw [← mul_assoc,mul_comm H]; exact le_add_self
 rw [← ofReal_norm,violet,Prod.norm_def];simp_rw [ENNReal.ofReal_max,ofReal_norm]

lemma route_bound (p:ℕ) : ∃ c:ℝ≥0∞,c≠⊤∧∀ x:Trip G,∀ v:G.ColorIndex, ‖coeff p (routeS G v x)‖ₑ≤ c*‖x‖ₑ^(p+1):=by
 obtain ⟨c,hc,h⟩:= sing_price (G:=G) p 1; refine ⟨c,hc,?_⟩; intro x v; rw [song_jet]
 by_cases hx: x=0
 · rw [hx,← song_jet,routeS];simp_rw [trackzero, PiLp.zero_apply,tale_const,map_zero];simp
 have hh:=norm_pos_iff.mpr hx
 let y:= ‖x‖⁻¹ • x;have he:x=‖x‖ • y:=by unfold y; rw [smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
 have hY: ‖y‖≤1:=by unfold y; rw [norm_smul]; simp [hh.ne']
 rw (occs:=.pos [1]) [he]
 rw [show song G p v (‖x‖ • y)=‖x‖^(p+1)*song G p v y from jet_smul ..,enorm_mul]
 apply le_trans (mul_le_mul_right (h _ hY _) _); rw [mul_comm _ c]; rw [← ofReal_norm, Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^(p+1)), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

-- per slot × full footprint ν meter. Upper used later only for r=3,4.
def belt (x:ℕ)(c:ℝ≥0∞)(G:Gauge):ℝ≥0∞:= Classical.choose (route_bound (G:=G) x) * (c+2*c)^(x+1)
def billow (G:Gauge)(c:ℝ≥0∞)(k:ℕ):ℕ → ℝ≥0∞ -- need prev decreasing rank not k.
 | 0=> ‖coeff k (1:ℝ⟦X⟧)‖ₑ
 | r+1=> ∑ i∈ antidiagonal k,belt i.1 c G * billow G c i.2 r
termination_by n=>n
lemma costs_b (h:C≠⊤)(p n): billow G C p n≠⊤:=by induction n generalizing p with
 | zero=>rw [billow]; finiteness
 | succ n ih=> rw [billow]; refine ENNReal.sum_ne_top.mpr (fun i _=> ENNReal.mul_ne_top (ENNReal.mul_ne_top ((route_bound (G:=G) i.1).choose_spec.1) (ENNReal.pow_ne_top (by finiteness))) (ih _))

variable {A:BEdge G}{σ:Cover→G.Color}{x: Cover} {c:ℝ≥0∞}(h:TightF x c A)(hh:TightS x c σ)
include h hh
lemma wave_fee (p:Tuple (Foot G) r)(e:ℕ) : ‖coeff e (pip (vow (shadowU A σ)) p)‖ₑ ≤ billow G c e r * wall x 1 (r+e) p:=by
 let v:= vow (shadowU A σ); change ‖coeff e (pip v p)‖ₑ≤ _
 induction r generalizing e with
 | zero=> rw [billow]; unfold pip; simp only [univ_eq_empty]; apply le_trans _ (mul_le_mul_right (wall_one ..) ‖coeff e (1:ℝ⟦X⟧)‖ₑ); rw [mul_one]; simp
 | succ r ih=>
    rw [billow, sum_mul]; let y:=p 0; let q:=Fin.tail p;let t:= violet A σ y.1
    have hp(i): ‖coeff i (v y)‖ₑ≤ belt i c G * wall x 1 (i+1) p:=by
       apply le_trans ((route_bound (G:=G) i).choose_spec.2 t y.2)
       apply le_trans (mul_le_mul_right (pow_le_pow_left' (tight_trip h hh y.1) (i+1)) _); rw [mul_pow,← mul_assoc]
       apply mul_le_mul_right; rw [← w_imp x p];apply pow_le_pow_left'; exact st_w p x 0
    rw [show pip v p=v y * pip v q from Fin.prod_univ_succ _,coeff_mul]; apply (enorm_sum_le ..).trans; apply sum_le_sum;intro i hi;rw [enorm_mul]
    apply le_trans (mul_le_mul' (hp i.1) (ih (p:=q) _)); rw [mul_mul_mul_comm]
    let u:= wall x 1 1 p
    apply mul_le_mul_right; have he: wall x 1 1 q≤ u:=by unfold u Momentum.wall q; rw [Fin.sum_univ_succ]; simp only [pow_one]; apply add_le_add_right; exact le_add_self
    rw [← w_imp x p, ← w_imp x q]; apply le_trans (mul_le_mul_right (pow_le_pow_left' he _) _); apply le_of_eq
    rw [show wall x 1 1 p=u from rfl,← pow_add,show i.1+1+(r+i.2)=r+1+e from by have ht:=mem_antidiagonal.mp hi;omega]; exact w_imp x p
end YM.RegulatorIR.Pupil
