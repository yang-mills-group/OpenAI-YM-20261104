import YM.FormalBulk08.Reef.Safe

/-! Mesh top Wilson germ. Scalar reference prior = probability Haar at all sites.
Consistent kinetic reset seed over CUT history. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free Work.F08 Work.F05 Stationary Tree Wilson
open Series Jets Wick Orb PowerSeries Matrix UVExtension.Free
open scoped Topology BigOperators Matrix ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def fundamental (G : Gauge) (n : Side) := Wilson.energy ∘ input G n
theorem front : ContDiffAt ℝ ω (fundamental G n) 0 := by
   unfold fundamental Wilson.energy Function.comp; refine ContDiffAt.sum (fun x _=> Work.F03.price_smooth (A:=fun z:Jets.Rays (wire G n)=>faceValue (input G n z) x) ?_)
   change ContDiffAt ℝ ω (fun z=>G.mat (faceValue (represent (arm G n 1 z)) x)) _
   unfold faceValue; exact ContDiffAt.comp (g:=fun (a:Bid.Dir G n) => G.mat (travel (represent a) _ _)) (f:=arm G n 1) _ (by
      rw [map_zero]; exact Push.writes _ _) (arm G n 1).contDiff.contDiffAt

def force (G : Gauge) (n : Side) := patron G (Exterior.d 1 n)
lemma prime (k : ℝ) (hk : 0<k) (j:ℕ)(hj:4≤j) : kernelP G k (Train.top j) n = (force G n)ᵀ*(force G n) := by
   obtain ⟨γ,σ,v,E,hγ,hs,hv,hE,H⟩:= bid_bed k 0 hk (le_refl _) hj
   let a : Clip:=⟨γ,γ/32,1,hγ,by positivity,by linarith,one_pos⟩
   obtain ⟨M,hM,-,-,-,h⟩ := H a (le_refl _) (Train.top j)
   rw [kernelP,←hM.diag,h rfl n, Precision.K]; simp [force,patron_mul,patron_star]
lemma current (x : Jets.Rays (wire G n)) (y : Face (Per n)) (j : G.ColorIndex) : Work.F03.faceCurl y (arm G n 1 x) j=(force G n*ᵥ x) (y.1,plaquette y.2,j) := (congr_fun (Flat.paint_eats (d 1 n) x j) (y.1, plaquette y.2)).symm
lemma power_two (x : Jets.Rays (wire G n)) : dotProduct (force G n*ᵥ x) (force G n*ᵥ x)=∑ y:Face (Per n),‖Work.F03.faceCurl y (arm G n 1 x)‖^2 := by
   change (∑ i: Site n × TypeFace 2 × G.ColorIndex, _)=∑ y: Site n × PlaqAxes,_; simp_rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro x' _; rw [← Equiv.sum_comp plaqEquiv]; apply Finset.sum_congr rfl; intro i _
   rw [←real_inner_self_eq_norm_sq]; simp only [PiLp.inner_apply,RCLike.inner_apply]; simp_rw [current]; rfl
lemma landmark :
    let T := fundamental G n
    T 0=0 ∧ fderiv ℝ T 0=0 ∧ ∀ x y, iteratedFDeriv ℝ 2 T 0 ![x,y]=dotProduct (force G n*ᵥ x) (force G n*ᵥ y) := by
   intro T; apply Work.F03.hessian_of_limit (front.of_le le_top)
   · intro x
     change Tendsto (fun t : ℝ => Wilson.energy (represent (arm G n 1 (t • x))) / _) _ _
     simp_rw [Wilson.energy,power_two,Finset.sum_div, map_smul]; refine tendsto_finsetSum _ (fun i _=> Work.F03.price_limit (V:=fun t=> faceValue (represent (t • arm G n 1 x)) i) ?_ (Work.F03.face_deriv i _))
     simp [link_one,faceValue]
   · intro x y z; rw [Matrix.mulVec_add,add_dotProduct]
   intro a b; exact dotProduct_comm ..

def seed (G : Gauge) (n : Side) := - afterX (paste (fundamental G n)) 2
lemma wax : X^2 * seed G n = - paste (fundamental G n) := by
   rw [seed,mul_neg,after_rope]
   intro i hi; obtain ⟨h,h',-⟩:= landmark (G:=G) (n:=n); interval_cases i
   · rw [paste_first,h,map_zero]
   apply orbit_ext;intro x; rw [trace_paste]; simp [PertExtension.Series.Radial.jet,h',traceP]
lemma seed_first (k : ℝ)(hk:0<k)(j)(hj:4≤j) : coeff 0 (seed G n)=crunch (kernelP G k (Train.top j) n) := by
   apply orbit_ext; intro x;rw [seed,map_neg,after_one,Nat.add_zero,show traceP x (-_)=_ from (map_neg (MvPolynomial.aeval (R:=ℝ) x) _),crunch_value, prime k hk j hj]
   change -traceP x ((coeff 2) (paste (fundamental G n)))=_
   rw [trace_paste,PertExtension.Series.Radial.jet,show (fun _:Fin 2=> x)=![x,x] from funext fun i=>by fin_cases i <;> simp, landmark.2.2,←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]; norm_num; ring
lemma seed_ward : Civic (seed G n) := by
   intro s x I inst a b k ha hb e g hu hv hh
   apply mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R:=Glyphs ℝ I)))
   have ht (u:Jets.Rays I → Jets.Rays (wire G n)) : roam ℝ (motor u) X=X := change_X _
   have he (p:Jets.Rays I → Jets.Rays (wire G n)) : X^2 * roam ℝ (motor p) (seed G n)= -roam ℝ (motor p) (paste (fundamental G n)) := by
      nth_rw 1 [← ht p,← map_pow]; rw [←map_mul,wax,map_neg]
   rw [he a,he b,←paste_steps _ a (front.of_le le_top) (e.of_le le_top) ha,←paste_steps _ b (front.of_le le_top) (g.of_le le_top) hb];
   apply congr_arg Neg.neg; apply paste_replace; filter_upwards [hh] with z hz; simp only [Function.comp_apply,fundamental,hz,energy_gauge,energy_pull]
end YM.FormalBulk08.Reef
