import YM.FVA2.Scalar

/-!
# Compute the Master wick line in based positions

`vectorLine` & `siteVector` use lattice steps at mesh n. There is no
leading 1/2 in the answer: Master stores K, but an ordinary gaussian
*covariance* corresponds to Chill. Sites of the inversion quotient are
not ordinary half-mode boundary points; we must keep the image term
also when the positions tested lift to the inversion fixed set.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Green
open MS MS.Koszul MS.Tone MS.Orbit MS.Landau MS.Swirl MS.Swirl.Near Lattice Finset
open MS.Momentum Based MS.Cylinder
variable {G : Gauge} {n : Side}
abbrev Bos (i : Axis) (a : G.ColorIndex) : Branch G Axis := (gauge i,a)
abbrev KV (i : Axis) (a : G.ColorIndex) : Branch G Axis := (anti i,a)
abbrev SiteC (a : G.ColorIndex) : Branch G Axis := (ghost,a)
abbrev Bfield (a : G.ColorIndex) : Branch G Axis := (gaugeC,a) -- denotes B (NOT bar)

lemma straight (a b : Branch G Axis) (x y : Site n) :
    Chill (cov G n false) (a,x) (b,y) = ∑ p : Site n, scaleZ n * Bass G a b (Coord p) * Bloch.cell p (x-y) := by
  let ξ:=basisM G n; let C:=Orbit.mat n (FinalK G);
  rw [cov,Modes.induce_chill]; change ∑ _i:FixedMode G n,∑ _j:FixedMode G n, Chill C _i _j * (ξ _i (a,x)*ξ _j (b,y))=_
  simp_rw [Fintype.sum_prod_type (α₁:= Branch G Axis)]
  rw [Finset.sum_eq_single a]; rotate_left
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
    rw [show ξ (i,j) (a,x)=0 from (by unfold ξ basisM; rw [need id hi,zero_mul])]; ring
  · simp
  refine Finset.sum_congr rfl (fun p _ => ?_); rw [Finset.sum_eq_single b]; rotate_left
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _
    rw [show ξ (i,j) (b,y)=0 from (by unfold ξ basisM; rw [need id hi,zero_mul])]; ring
  · simp
  rw [Finset.sum_eq_single (-p)]; rotate_left
  · intro i _ hi; rw [chillOff _ _ _ _ hi,zero_mul]
  · simp
  rw [ChillK]; unfold ξ basisM; simp_rw [show ∀ a : Branch G Axis,(way id a a : ℂ)=1 from fun _=> only id _,one_mul]; rw [sub_eq_add_neg x, Bloch.cell_add,cellNeg]

-- image: no s≠Omega(s) requirement
abbrev kind (a : Branch G Axis) : ℂ:= gscore (a,(0:QP))
def reflPos (a : Atom Axis) (y : Site n) := match a.1 with
     | some i => -y-step i
     | none => -y

lemma kind_a (i : Axis) (b : Bool) (a : G.ColorIndex) : kind ((some i,b),a) = -1 := by rfl
lemma kind_c (b : Bool) (a : G.ColorIndex) : kind ((none,b),a)=1 := by rfl

lemma flag_site (b : Bool) (a : G.ColorIndex) (p : QP) : flag ((none,b),a) p=1 := by change bill p 0=_; exact right0 _
lemma phase_turn (i : Axis) (p : QP) :
    bill p (offset (some i,false)) ^2 = bill p (embed (step i)) := by rw [Tone.Frame.centr i,rightadd,pow_two]; rfl

lemma spun_position (a : Branch G Axis) (y p : Site n) :
    (iota G n).spin (a,p) * basisM G n (a,-p) (a,y) =
             kind a * basisM G n (a,p) (a,reflPos a.1 y) := by
    rw [iota_spin]; unfold Orbit.switch basisM
    simp_rw [show (way id a a:ℂ)=1 from only id a, one_mul, cellNeg p]; rw [mul_assoc]; congr 1
    rcases a with ⟨⟨_ | i,b⟩,a⟩; change flag _ _ ^ 2 * _ = _; rw [flag_site,one_pow,one_mul]; rfl
    change bill (-Coord p) (offset (some i,false))^2*_ = Bloch.cell p (-y-step i)
    rw [phase_turn,sub_eq_add_neg (-y),Bloch.cell_add,Bloch.cell_inverse p (step i), cellStep, Tone.opp, mul_comm]

lemma spun (j a : Branch G Axis) (p y : Site n) :
    (iota G n).spin (j,p) * basisM G n (j,-p) (a,y) =
      kind a * basisM G n (j,p) (a,reflPos a.1 y) := by
  by_cases h:j=a; subst j; exact spun_position ..
  unfold basisM; rw [need id h]; ring

open MS.Orbit.Cog
lemma quotient (a b : Branch G Axis) (x y : Site n) :
     Chill (cov G n true) (a,x) (b,y) = Chill (cov G n false) (a,x) (b,y) +
       kind b * Chill (cov G n false) (a,x) (b,reflPos b.1 y) := by
   let C := Orbit.mat n (FinalK G); let S := iota G n; let ξ:= basisM G n
   have hc i j : Chill (Master G n true) i j= Chill C i j + S.spin (S.mode j)*Chill C i (S.mode j) := by
      change 2*(C i j + (imageW S C i j))=_; unfold imageW Chill; ring
   have hr (i : FixedMode G n) : (∑ j:FixedMode G n,S.spin (S.mode j)*Chill C i (S.mode j)*(ξ i (a,x)*ξ j (b,y)))=∑ j:FixedMode G n, kind b*(Chill C i j*(ξ i (a,x)*ξ j (b,reflPos b.1 y))) := by
      rw [← Equiv.sum_comp S.axis (fun j : FixedMode G n => S.spin (S.mode j)*Chill C i (S.mode j)*(ξ i (a,x)*ξ j (b,y)))]; refine Finset.sum_congr rfl (fun j _=> ?_)
      change S.spin (S.mode (S.mode j))*Chill C i (S.mode (S.mode j))*(ξ i (a,x)*ξ (S.mode j) (b,y))=_; rw [S.perm j]
      have hχ : S.spin j * ξ (S.mode j) (b,y) = kind b * ξ j (b,reflPos b.1 y) := spun ..
      linear_combination (norm:=ring) (Chill C i j * ξ i (a,x)) * hχ
   simp_rw [cov, Modes.induce_chill, hc, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
   congr 1; exact Finset.sum_congr rfl fun i _=> hr i

def vectorLine (i j : Axis) (z : Site n) : ℝ := (if i=j then kernel 1 z else 0) - fwd i (back j (kernel 2)) z

def siteVector (j : Axis) (z : Site n) : ℝ := -back j (kernel 1) z -- z=x-y (c at x, K at (y,j))

lemma bass_cK (a : G.ColorIndex) (p : Site n) (j : Axis) : Bass G (SiteC a) (KV j a) (Coord p)= -ds (-p) j * (symbol p:ℂ)⁻¹ := by
   rw [neg_step_formula]; unfold Bass Landau.choir; rw [if_pos (show a=a from rfl),flag_site]; change 1*bill (-Coord p) (offset (some j,false)) * (Complex.I * (((waveStep p j)/(symbol p):ℝ) : ℂ))=_; rw [Tone.opp]; unfold stepPhase; push_cast; ring
lemma bass_AA (a : G.ColorIndex) (p : Site n) (i j : Axis) : Bass G (Bos i a) (Bos j a) (Coord p)=
     (if i=j then (symbol p:ℂ)⁻¹ else 0) - ds p i * ds (-p) j * ((symbol p:ℂ)⁻¹)^2 := by
   -- de-phase p2_i.
   rw [neg_step_formula]; conv_rhs => arg 2; lhs; lhs; rw [pos_step_phase] 
   unfold Bass Landau.choir; rw [if_pos (show a=a from rfl)]; change stepPhase p i * bill _ _ * (((precision i j _)/(symbol p)^2:ℝ):ℂ)=_
   rw [Tone.opp]; unfold Landau.precision delta; change stepPhase p i* (stepPhase p j)⁻¹ * ((((if i=j then symbol p else 0) - waveStep p i*waveStep p j)/(symbol p)^2 :ℝ): ℂ)=_
   by_cases h:i=j; swap
   · rw [if_neg h,if_neg h]; push_cast; ring_nf; simp [mul_comm]
   subst j; rw [if_pos rfl,if_pos rfl, mul_inv_cancel₀ (show stepPhase p i≠0 from Tone.nonz _ _), one_mul]
   by_cases hv:p=0; subst p; simp
   push_cast; have hm : (symbol p:ℂ)≠0:= by exact_mod_cast (symbol_pos hv).ne'
   field_simp [hm,(show stepPhase p i≠0 from Tone.nonz _ _)]; ring_nf; simp [mul_comm]; ring

lemma fwdReal (i j : Axis) (z : Site n) :
    ((fwd i (back j (kernel 2)) z : ℝ):ℂ)= fwd i (back j (kernelC 2)) z := by
   simp_rw [fwd_of,back_of,Complex.ofReal_sub,real_kernel]
lemma vector_fourier (i j : Axis) (x : Site n) :
    (vectorLine i j x:ℂ)=∑ p : Site n, scaleZ n * ((if i=j then (symbol p:ℂ)⁻¹ else 0) - ds p i * ds (-p) j *((symbol p:ℂ)⁻¹)^2 ) * Bloch.cell p x := by
   unfold vectorLine; rw [Complex.ofReal_sub,fwdReal,kernelC,map_sum,map_sum,Finset.sum_apply ]
   simp_rw [mul_sub,sub_mul,Finset.sum_sub_distrib]; apply congr_arg₂ (·-·)
   · split
     next h => simp_rw [real_kernel,termwise,pow_one]
     next h => simp
   refine Finset.sum_congr rfl (fun i _ => ?_); rw [map_smul, map_smul,cell_back,map_smul, cell_fwd]; simp only [Pi.smul_apply, smul_eq_mul]; ring
lemma site_fourier (i : Axis) (x : Site n) :
    (siteVector i x:ℂ)=∑ p : Site n, scaleZ n *(-ds (-p) i * (symbol p:ℂ)⁻¹)* Bloch.cell p x := by
   unfold siteVector; rw [Complex.ofReal_neg, show (↑( (back i) (kernel 1) x):ℂ)= back i (kernelC 1) x from (by simp_rw [back_of,Complex.ofReal_sub,real_kernel]),kernelC,map_sum,Finset.sum_apply, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,cell_back]; simp only [Pi.smul_apply, smul_eq_mul,pow_one]; ring

lemma cov_among (a b : Branch G Axis) (x y : Site n) (i : Bool) (h : ∀ q : Site n, Tail a.1 b.1 (wave (Coord q))=0) : Chill (cov G n i) (a,x) (b,y) = 0 := by
  have hc (x y : Site n) : Chill (cov G n false) (a,x) (b,y)=0 := by rw [straight]; unfold Bass Landau.choir; simp_rw [h,ite_self,mul_zero,zero_mul]; rw [Finset.sum_const_zero]
  cases i; exact hc x y
  rw [quotient,hc,hc,mul_zero,zero_add]
lemma cov_color (a b : Branch G Axis) (h : a.2 ≠ b.2) (x y : Site n) (i : Bool) :
    Chill (cov G n i) (a,x) (b,y)=0 := by
  have hc (x y : Site n) : Chill (cov G n false) (a,x) (b,y)=0 := by rw [straight]; unfold Bass Landau.choir; simp_rw [if_neg h,mul_zero,zero_mul,Finset.sum_const_zero]
  cases i; exact hc x y
  rw [quotient,hc,hc,mul_zero,zero_add]

lemma straight_cK (a : G.ColorIndex) (x y : Site n) (j : Axis) : Chill (cov G n false) (SiteC a,x) (KV j a,y)=
    (siteVector j (x-y) : ℝ) := by rw [straight,site_fourier]; simp_rw [bass_cK]
lemma straight_AA (a : G.ColorIndex) (x y : Site n) (i j : Axis) : Chill (cov G n false) (Bos i a,x) (Bos j a,y)=
    (vectorLine i j (x-y) : ℝ) := by rw [straight,vector_fourier]; simp_rw [bass_AA]

theorem contracted_vector (x y : Site n) (i j : Axis) (a : G.ColorIndex) : Chill (cov G n true) (Bos i a,x) (Bos j a,y)=
     (( (vectorLine i j (x-y)-vectorLine i j (x-(-y-step j))) : ℝ):ℂ) := by rw [quotient,kind_a,straight_AA,straight_AA]; push_cast; unfold reflPos; ring

theorem contracted_ghost (x y : Site n) (j : Axis) (a : G.ColorIndex) : Chill (cov G n true) (SiteC a,x) (KV j a,y)=
     ((siteVector j (x-y)-siteVector j (x-(-y-step j)) : ℝ):ℂ) := by rw [quotient,kind_a,straight_cK,straight_cK]; push_cast; unfold reflPos; ring

end YM.FVA2.Green
