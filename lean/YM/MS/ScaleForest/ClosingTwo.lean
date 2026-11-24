import YM.MS.ScaleForest.UtterPass
/-!
# Finish the triangle with the closing shell

This is where the transverse pole part actually enters, on the D part
without its `-1/ε`. Use the legitimately holomorphic quotient
numerator by itself at specialization (after the general theory). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I:Type} (X Y:Pupil) (x:E4) {F:Mob G} (s:ℝ)

lemma shell_contour (μ:ℝ) (h: Form0 false F): closeG (cleanJet G s) 0 μ F 0 []=∫ p,trc (cleanJet G s 0) p (F 0) [] ∂planeF:= by
   rw [closeG_eq, Pi.smul_apply,Pi.smul_apply];
   have hv:= fze ((cursor (G:=G) false).ok.forms false) 4 s; rw [ prim_0 G s ] at hv;
   let U:= cleanJet G s; have he:= Path.lowN (m:=0) h.price hv.price h.token hv.token []; rw [Nat.cast_zero] at he; rw [he,fee_T0]; simp only [Arc.pitch,Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one, one_smul ]; unfold Ccy; rw [plank, integral_smul_measure, ENNReal.toReal_ofReal room_pos.le]; rfl

-- swapping arguments can change momentum signs. need two orientations; account before using integration
variable (p:QP) {φ:QP→Ω G→ℂ} {L:Rip G}
private lemma allot_dot (p q:QP) (K:Rip G)(z:Ω G)(b:ℂ)(ht:Radiant K (m:=0) q b)(hp:q=p∨q= -p):
    (∑ i:Shaft G 0,∑ j:Shaft G 0,2*K 0 (rod i) (rod j) q*allot X Y x p (-p) i j z ) =
      premium X Y z * (Φ x p * (portfolio X Y z.1 z.2 p*b)) := by
    let c:=premium X Y z * Φ x p; let F(a:Shaft G 0):= Cur X z.1 p a; let H(a:Shaft G 0):=Cur Y z.2 (-p) a; have hh: stableA q H:= by obtain he:= antenna_right (m:=0) (-p) Y z.2; rcases hp with rfl|rfl <;> first| exact he| (have ht:= he.mirror; rw [neg_neg] at ht; exact ht)
    change (∑ i:Shaft G 0,∑ j:Shaft G 0,2*K 0 (rod i) (rod j) q*(c*F i*H j))= _;
    simp_rw [ show ∀ i j:Shaft G 0,2*K 0 (rod i) (rod j) q*(c*F i*H j)=c*F i*(2* K 0 (rod i) (rod j) q *H j) from fun i j=> by ring,← Finset.mul_sum, fun i=>ht.focus i H hh ]; unfold c F H portfolio; simp_rw [ Finset.sum_mul, Finset.mul_sum ]; exact Finset.sum_congr rfl (fun i _=> by ring)

lemma couples (hp: aim F p (-p)= fun i j=> stained X Y x p (-p) i j (φ p)) :
    2*trc (cleanJet G s 0) p (F 0) []= ∑ z:Ω G, premium X Y z*(salute' X Y z.1 z.2 x p s+salute' X Y z.1 z.2 x (-p) s)*φ p z := by
    obtain h := jet_act (m:=0) (G:=G) p s; let B:=shining (m:=0) p s; let t(a b:Shaft G 0):= cleanJet G s 0 (rod a) (rod b) p
    rw [at_trc, h.all _ (fun i j hh=> by rw [hh, zero_mul]) ]; change 2*(∑ i:Shaft G 0,∑ j:Shaft G 0,t i j*aim F p (-p) i j) = _; rw [hp]; unfold stained; simp_rw [ Finset.mul_sum ];
    let g(i j : Shaft G 0)(z:Ω G):=2*t i j* tinct X Y x p (-p) i j z
    let C:= Shaft G 0 -- `∑z∑i∑j`
    have hv (z:Ω G): (∑ i:Shaft G 0,∑ j:Shaft G 0,g i j z) = premium X Y z*(salute' X Y z.1 z.2 x p s+salute' X Y z.1 z.2 x (-p) s) := by
       unfold g tinct t; simp_rw [ mul_add, Finset.sum_add_distrib];
       rw [ allot_dot X Y x p p _ z B h (Or.inl rfl) ]; have hq:= allot_dot X Y x (-p) p _ z B h (Or.inr (neg_neg p).symm);
       rw [neg_neg] at hq; rw [ Finset.sum_comm ]; -- forall rewrite h swap by nested sums
       rw [ show (∑ i:Shaft G 0,∑ j:Shaft G 0, 2*cleanJet G s 0 (rod j) (rod i) p * allot X Y x (-p) p i j z) =_ from Eq.trans ( Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> by rw [h.swap j i] ))) hq ]; unfold B salute'; rw [shine_parity]
    simp_rw [ show ∀ i j:Shaft G 0,∀ z,2*(t i j*(tinct X Y x p (-p) i j z *φ p z))=g i j z*φ p z from fun i j z=> by unfold g; ring ]; -- binder z
    simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Shaft G 0)) (t:=Finset.univ (α:=Ω G)), ← Finset.sum_mul, hv]

variable (μ:ℝ)
lemma cog_full (hF:Form0 false F)(he:∀ p: QP,aim F p (-p)= fun i j=> stained X Y x p (-p) i j (φ p))(h:∀ p:QP,φ p=φ (-p))(hp:∀ z:Ω G, Integrable (fun p=> salute' X Y z.1 z.2 x p s*φ p z) planeF) :
    closeG (cleanJet G s) 0 μ F 0 []=∑ z:Ω G,premium X Y z * ∫ p:QP, salute' X Y z.1 z.2 x p s*φ p z ∂planeF:= by
    rw [shell_contour s μ hF]; apply mul_left_cancel₀ (a:=(2:ℂ)) (by norm_num); rw [ ← integral_const_mul ]; simp_rw [ fun p=> couples X Y x s p (he p) ];
    let f(z:Ω G)(p:QP):= salute' X Y z.1 z.2 x p s*φ p z; let W(z:Ω G)(p:QP):= premium X Y z*(f z p+f z (-p));
    simp_rw [ show ∀ z:Ω G,∀ p:QP,premium X Y z*(salute' X Y z.1 z.2 x p s+salute' X Y z.1 z.2 x (-p) s)*φ p z=W z p from fun z p=> by unfold W f; rw [← h p]; ring ];
    have hU (i:Ω G): Integrable (W i) planeF:= ( (hp i).add (hp i).comp_neg ).const_mul (premium X Y i); rw [ integral_finsetSum _ (fun i _=> hU i), Finset.mul_sum ]; refine Finset.sum_congr rfl (fun i _=> ?_); unfold W; rw [integral_const_mul,integral_add (f:=f i) (hp i) (g:=fun t=>f i (-t)) (hp i).comp_neg, integral_neg_eq_self ]; unfold f; ring
end YM.MS.ScaleForest.Triangle
