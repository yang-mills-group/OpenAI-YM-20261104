import YM.MS.ScaleForest.Sunshine
/-!
# Evaluate the continued cross at parameter 0 on our rank-two trees

We may do this inside the ODE for an honestly finite (at finite upper)
family such as the *numerator* of the pole-quotient. Derive from the actual
between-pin angular integral with all constants (`room` not hidden) and
iterate over all signed available slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open scoped Topology ContDiff
variable {G : Gauge} (X Y:Pupil) (x:E4) {m:ℕ} (p q:QP) (s:ℝ)
local notation "K"=> cursor false
local notation "L"=> cleanJet G
local notation "A" => Theater.out x
local notation "M" => enrol
variable {Z F:Mob G}

abbrev Ω (G:Gauge):= Name G × Name G
abbrev premium (z: Ω G) : ℂ:= (X.density z.1.1:ℂ)*(Y.density z.2.1:ℂ)
abbrev allot (i j:Shaft G 0) (z:Ω G) := premium X Y z * Φ x p * Cur X z.1 p i * Cur Y z.2 q j
abbrev tincture (i j:Shaft G 0)(V:Ω G→ℂ):=∑ z:Ω G, allot X Y x p q i j z * V z
lemma prim_0 (G:Gauge)(s:ℝ): pulse 4 s (cursor false).half= cleanJet G s:= by change pulse 4 s (pickLine _ _) = _; rw [pulse_line,pA]
lemma plank : planeF= ENNReal.ofReal room • Px 0:= (by unfold Snap.planeF room Px covMeasure; simp [Axis])

private lemma healing_p (p q:QP) (i j:Shaft G 0) : aim (rephase A Z) p q i j= Φ x p * Φ x q * aim Z p q i j:= by
    unfold aim; rw [rephase_test]; change Tone.bill (Theater.out x) (onPlane 0 (net _))*_= _; rw [net_cons,net_cons,show net ([]:Legs (Shore G 0))=(0:QP) from rfl,add_zero]; change Tone.bill (Theater.out x) (p+q)*_= _; rw [Tone.rightadd]

structure Portrait (X:Pupil)(F:Mob G)(v:QP→QP→ℂ): Prop where
    rank: Goods 2 F
    refAt (p q:QP)(i j:Shaft G 0) : aim F p q i j=v p q* aim (enrol X G 0).symbol p q i j
variable {f g : QP→QP→ℂ}
lemma Por_base (X:Pupil)(G:Gauge): Portrait X (M X G 0).symbol (fun _ _=>1) := ⟨ (enrol X G 0).slots, fun _ _ _ _=> (one_mul _).symm⟩
lemma Por_left (X:Pupil) {ι:Type}[TopologicalSpace ι][FirstCountableTopology ι](w:ι) (L':ℝ) (h:G.Simple): Portrait X
    ( absNom L' (bed (armBranch X (vertex (ghostR G)))) s w) (fun p q=> Highβ G (m:=0) p s+Highβ G (m:=0) q s) := by
    constructor; exact (Planted.observing L' s w (bed (armBranch X (vertex (ghostR G)))) trivial).2; exact fun p q i j=> arm_along L' p q h s w X i j

-- integral gluing: nonhomogeneous factors arbitrary, momentum net not discarded
abbrev Christ (f g:QP→QP→ℂ)(z:Ω G)(w:QP):= (f w p*g (-w) q)*salute' X Y z.1 z.2 x w s

-- define the cross numerator before q integration with external ports assignment
private def CrossM (w : QP)(i j:Shaft G 0): ℂ:=
   2* ∑ a,∑ b, oneCross (cleanJet G s) (rephase A Z) F (m:=0) w a b [armI i p] [armI j q]

lemma presents (μ:ℝ)(hz:Form0 false Z)(hf:Form0 false F)(w:Legs (Shore G 0)) :
    pinned (cleanJet G s) 0 μ A Z F 0 w=∫ r:QP,2*cutTree (cleanJet G s) (rephase A Z) F (m:=0) r w ∂planeF := by
    obtain Q:=(cursor (G:=G) false).ok; have ht:= congr_fun (pinned_here (n:=0) (fze (Q.forms false) 4 s) (pulsed_closed Q.even s) (a_rev _ _ Q.rev) hz hf A μ) w; rw [Nat.cast_zero,fee_T0,Arc.pitch] at ht; simp only [ Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one,Complex.ofReal_one,one_mul ] at ht; rw [ ← prim_0, ht,plank,integral_smul_measure, ENNReal.toReal_ofReal room_pos.le ]; rfl
variable {X Y}
lemma assigned (hF:Portrait X Z f)(hZ:Portrait Y F g)(i j:Shaft G 0)(w:QP) :
   CrossM (Z:=Z) (F:=F) x p q s w i j=tincture X Y x p q i j (fun z=> Christ X Y x p q s f g z w) := by
   let R:= cleanJet G s; obtain ht:= jet_act (G:=G) (m:=0) w s; let r(i j:Shaft G 0):=R 0 (rod i) (rod j) w; let B:=shining (m:=0) w s; let V a :=aim Z w p a i; let N a:= aim F (-w) q a j
   have he (a:Shaft G 0): ∑ b:Shaft G 0, 2*r a b * N b=B* N a:= by
      apply ht.focus a N; obtain hp:=(( GoodAim.mark (m:=0) Y ).direct (-w) q j).mirror; rw [neg_neg] at hp;
      intro u; unfold N; simp_rw [ hZ.refAt, mul_left_comm (_:ℂ) (g (-w) q), ← Finset.mul_sum, hp u, mul_zero ]
   unfold CrossM; rw [ ht.all ]; swap; · intro i j h; simp only [oneCross,h,zero_mul]
   let c:=Φ x w* Φ x p
   have hX : (∑ a:Shaft G 0, ∑ b:Shaft G 0, 2*R 0 (rod a) (rod b) w*(c*V a)*N b)= c*B*∑ a:Shaft G 0,V a*N a:= by
      simp_rw [Finset.mul_sum ]; exact Finset.sum_congr rfl (fun a _=> by
         change (∑ b:Shaft G 0,2 * r _ b * (c*V a)* N b)= _
         simp_rw [ show ∀ b,2 * r a b* (c*V a)* N b=c * V a * ( 2*r a b*N b) from fun b=>by ring, ← Finset.mul_sum, he ]; ring)
   -- substitute now.
   simp_rw [ Finset.mul_sum, oneCross, show ∀ b:Shaft G 0, parity (rod b)=false from fun _=> rfl,cross_false,one_mul ];
   simp_rw [ show ∀ a:Shaft G 0, rephase A Z 0 [(rod a,w),armI i p]=_ from fun a=> healing_p x w p a i ];
   rw [show (∑ a:Shaft G 0, ∑ b:Shaft G 0, _)=_ from (show _= c*B*∑ a:Shaft G 0,V a*N a from (by convert! hX using 1; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> ?_; change 2*(r a b*( c * V a)*N b) = _; change _ =2*r a b*(c*V a)*N b; ring))];
   unfold V N; simp_rw [ hF.refAt,hZ.refAt,witness X,witness Y,Finset.mul_sum, Finset.sum_mul ];
   unfold tincture Christ salute' portfolio; -- regroup Ω
   simp_rw [ Finset.mul_sum, Finset.sum_mul ]; rw [ Finset.sum_comm (s:=Finset.univ (α:=Shaft G 0)) ]; conv_rhs=> rw [Fintype.sum_prod_type_right]
   simp_rw [Finset.mul_sum ]; refine Finset.sum_congr rfl fun a _=>?_;
   rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun i _=> ?_; unfold allot premium c B; ring

lemma Cut_flux (w:QP)(i j:Shaft G 0)(hF:Portrait X Z f)(hZ:Portrait Y F g) :
   2*cutTree (cleanJet G s) (rephase A Z) F w [armI i p,armI j q] = CrossM (Z:=Z) (F:=F) x p q s w i j+CrossM (Z:=Z) (F:=F) x q p s w j i:= by
   let U:=rephase A Z; have he:Goods 2 U:= fun m l ht=> by unfold U; rw [rephase_test,hF.rank m l ht,mul_zero];
   unfold cutTree; simp only [ scatter_cons,scatter_nil, show ∀ i:Shaft G 0, ∀ p, field parity (armI i p)=false from fun _ _=>rfl,cross_false, one_mul, Finset.sum_apply]; unfold oneCross;
   simp only [show ∀ i: Shore G 0,F 0 [i]=0 from fun i=>hZ.rank 0 _ (by simp),show ∀ i:Shore G 0,rephase A Z 0 [i]=0 from fun i=> he 0 _ (by simp),mul_zero,zero_mul,Finset.sum_const_zero,add_zero,zero_add]; rw [mul_add,add_comm]; rfl

lemma expense_cross (μ:ℝ)(hz:Form0 false Z)(hf:Form0 false F)(hF:Portrait X Z f)(hZ:Portrait Y F g)
    (i j:Shaft G 0){T:QP→ QP → Ω G→ℂ} (ht : ∀ p q:QP, ∀ z:Ω G, Integrable (Christ X Y x p q s f g z) planeF ∧
      (∫ w:QP,Christ X Y x p q s f g z w ∂planeF)=T p q z) :
    aim (pinned (cleanJet G s) 0 μ A Z F) p q i j=tincture X Y x p q i j (T p q)+tincture X Y x q p j i (T q p) := by
   let r(p q:QP)(i j:Shaft G 0):= fun w:QP=> CrossM (Z:=Z) (F:=F) x p q s w i j
   have he (p q:QP)(i j:Shaft G 0): Integrable (r p q i j) planeF∧( ∫ w:QP,r p q i j w ∂planeF)=tincture X Y x p q i j (T p q):= by
      unfold r; simp_rw [assigned x p q s hF hZ]; unfold tincture; have hh (z:Ω G):= (ht p q z).1.const_mul (allot X Y x p q i j z)
      constructor; exact integrable_finsetSum _ fun i _=> hh i; rw [integral_finsetSum _ fun i _=> hh i]; simp_rw [integral_const_mul, fun i=>(ht p q i).2];
   unfold aim; rw [ presents x s _ hz hf ]; simp_rw [ Cut_flux x p q s _ i j hF hZ]; erw [integral_add (he p q i j).1 (he q p j i).1]; exact congr_arg₂ _ (he p q i j).2 (he q p j i).2

end YM.MS.ScaleForest.Triangle
