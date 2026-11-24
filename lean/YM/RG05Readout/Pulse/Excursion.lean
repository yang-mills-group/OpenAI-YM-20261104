import YM.RG05Readout.Pulse.Nearby
/-!
# Normalized physical field top coordinate against test.Read WZ.

Integral expression of ACTUAL finite family report. Powers restored exactly
 no inserted numerator perturbation.Domain small aperture n.B. equivalent
 in calendars even with full relative profile (Taylor at all taps) and all
 simultaneous crops. Still before taking ANY OPE limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pulse
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "G!"=>C.S.gridPoint
local notation "o!"=> C.S.place
local notation "ρ₀"=>C.S.radius p
local notation "W!"=> Wave V
local notation "J!"=> Cloud V
section shuttle
variable (C) (p) (N) (b)
noncomputable def gate (m N d:ℕ):ℂ:= (C.S.a N)^4 * ((C.S.a m:ℂ)/(C.S.a N:ℂ))^d
noncomputable def fieldC (m N p d:ℕ)(v:Palette C d)(f:Body): Goods G (C.side N p):= gate C m N d • ∑ z: Site (C.side N p), stepUp t! z (entrance C d N p v 0 (restricted C N p z f))
noncomputable def multi (m N p:ℕ)(s:V→ℕ)(v:(i:V)→ Palette C (s i)): Wave V →ₗ[ℂ] Goods G (C.side N p):=(∏ i:V, gate C m N (s i)) • ∑ t: V→Site (C.side N p), harpoon s v t ∘ₗ fork (C.S.a N) (fun i=>C.S.place (t i))
variable (s:V→ℕ)(v:(i:V)→ Palette C (s i))(q:ℝ) (f:Wave V)
local notation "H"=> multi C m N p s v
lemma from_fields (w: V→Body): H (joint Finset.univ w)= fun x=>∏ i:V, fieldC C m N p (s i) (v i) (w i) x:=by
    unfold fieldC multi; funext x; simp_rw [LinearMap.smul_apply, LinearMap.sum_apply,LinearMap.comp_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Finset.prod_mul_distrib,Fintype.prod_sum]; apply congr_arg ((∏ i:V,gate C m N (s i)) * ·); refine sum_congr rfl fun i _=> ?_; let T:= fun j=> restricted C N p (i j) (w j); exact hooked s v i T _ -- implicit
/-- Relative profile held at physical center y. -/
noncomputable def rel {V: Type*}[Fintype V](q:ℝ)(f:Wave V)(y:E4): Wave V := fork q⁻¹ (fun _=> q⁻¹ • (-y)) f
noncomputable def physicalEra {V:Type}[DecidableEq V][Fintype V](q:ℝ)(Ψ:Wave V)(g:Body)(C:Family G)(m p N:ℕ)(s:V→ℕ)(v:(i:V)→ Palette C (s i)) : Goods G (C.side N p) := fun U=> (∏ _i:V, (q:ℂ)⁻¹ ^4)*∫ x:E4, g.val x*((multi C m N p s v) (rel q Ψ x) U)
omit [DecidableEq V] in
lemma rel_taken (y: V→ Site X!)(z:E4): fork (C.S.a N) (fun i=> C.S.place (y i)) (rel q f z)= cameo C p N q f z y:=by
    unfold rel cameo; rw [fly_fork]; apply congr_arg (fun v : Cloud V=>fork (q⁻¹*A N) v f); funext i; change q⁻¹ • (-z)+q⁻¹ • o! (y i)=q⁻¹ • (o! (y i)- z); rw [sub_eq_add_neg,smul_add,add_comm]
lemma whereat (z:E4) : H (rel q f z)=(∏ i:V,gate C m N (s i)) • ∑ w:V→ Site X!,harpoon (N:=N) (p:=p) s v w (cameo C p N q f z w):=by
    unfold multi; simp_rw [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,rel_taken]
-- genuine continuous stencil charges iff filtering in support or Power high
lemma where_cont (m:ℕ)(u:Config G X!) : Continuous (fun z:E4=> (multi C m N p s v) (rel q f z) u):=by
     simp_rw [whereat,Pi.smul_apply, Finset.sum_apply]; let a:= ∏ i:V,gate C m N (s i); refine Continuous.const_smul (g:=fun z:E4=>∑ t:V→Site X!, harpoon s v t (cameo C p N q f z t) u) ?_ a; apply continuous_finsetSum; intro i _; unfold cameo; refine continuous_fee s v i f _ (continuous_pi (fun j=> ?_)) _; fun_prop
variable {C p N b} (h:b ≤ N)
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
local notation "U"=> fun w: V→Site X!=> harpoon (C:=C) (p:=p) (N:=N) s v w
local notation "Y"=> scalp (C:=C) s v
lemma money (m d:ℕ): gate C m N d=gate C m b d*ratioX (r) d:=by
    unfold gate ratioX; push_cast; let T':ℂ:= (r).count.val; have ht:T'≠0:=by unfold T'; exact_mod_cast (r).count.property.ne'
    have hz:A N*(r).count.val=A b:=C.S.embeds_scale _; have he: (A N:ℂ)*T'=(A b:ℂ):=by unfold T'; exact_mod_cast hz
    have hp : (A N:ℂ) ≠ 0:=by exact_mod_cast (C.S.a_pos N).ne'
    change _= _*(T'^d/T'^4); rw [← he]; field_simp; rw [← mul_pow]; field_simp
-- tuple ancestry bijection relative to z
noncomputable def walks (z:Site Y!): (V→Site Y!) × (V→T) ≃ (V→Site X!) where
    toFun s i:=(r).assemble (s.1 i+z,s.2 i)
    invFun t :=(fun i=> (r).parent (t i)-z,fun i=>(r).residue (t i))
    left_inv x:=Prod.ext (by funext i; dsimp only;rw [Ratio.assemble_parent]; exact add_sub_cancel_right ..) (funext fun i=>Ratio.assemble_res ..) -- lint
    right_inv t:= by funext i; dsimp only; rw [sub_add_cancel]; exact Ratio.unpack_at ..
variable {B R:ℝ}(hq:0<q)(hΨ:∀ x∈tsupport f.val,∀ i:V, ‖x i‖≤R)(hp:q*R+2*C.S.a b<C.S.radius p)(hρ:B+q*R<C.S.radius p)
include hΨ hq hp hρ
lemma car (m:ℕ) (z:Site Y!)(τ:E4)(ht:τ∈Native.box)(he:‖voyager C p b z τ‖≤ B):
    let y:=voyager C p b z τ
    (multi C m N p s v) (rel q f y)= (∏ i:V,gate C m b (s i)) • ∑ o:V→ Site Y!, stepUp t! ((r).embed z) (Y o h (cropX f o q τ)):=by
    intro y; let K:= walks h (V:=V) z; rw [whereat,← Equiv.sum_comp K, Fintype.sum_prod_type]; simp_rw [money (C:=C) (p:=p) h,Finset.prod_mul_distrib,mul_smul,Finset.smul_sum]; refine sum_congr rfl fun o _=> ?_;
    unfold scalp; rw [LinearMap.sum_apply,Records.rot_sum,Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_; rw [LinearMap.smul_apply,Records.rot_scalar]; let t:=fun j:V=> (r).assemble (o j,i j); let u':=K (o,i); let d':=(r).embed z; have hw: (fun i=> t i+d')=u':=by
        funext i'; unfold u' K; change (r).assemble _+d'=(r).assemble (_, i i'); unfold Ratio.assemble;rw [show (r).embed (_+_)=_ from (r).root.map_add (o i') z]; rw [Ratio.root_embed,Ratio.root_embed,add_right_comm]
    let Z:=fork ((↑(r).count.val:ℝ)⁻¹) (fun j=>placeR (r) (i j)) (cropX f o q τ); change _=(∏ x,gate C m b (s x)) • ((∏ i:V, ratioX (r) (s i)) • stepUp t! d' (U t Z)); rw [show stepUp t! d' (U t Z)=U u' Z from (shift_hook s v t d' Z).trans (by rw [hw])] -- maybe
    apply congr_arg ((∏ i:V, gate C m b (s i)) • ·);apply congr_arg ((∏ i:V,ratioX (r) (s i)) • ·); exact (diving h s v f o q hq hΨ z τ ht he i hp hρ).symm
omit hΨ hq hp hρ
-- unweighted Pulse function root at cutoff source
noncomputable def meet (u:V→Site Y!) (g:Body) (U':Config G X!) : ℂ:= ∫ x in Native.box,g.val x*((Y u h) (cropX f u q x)) U'
local notation "X0"=> meet s v q f h
lemma meet_lives (u:V→Site Y!)(g:Body)(U':Config G X!) : IntegrableOn (fun x=>g.val x*(Y u h (cropX f u q x) U')) Native.box :=by
   apply ContinuousOn.integrableOn_compact Pert.Cellular.cells_compact; apply Continuous.continuousOn; refine (body_smooth g 1|>.continuous).mul (wave_cont s v u h f _ (continuous_pi (fun j=>?_)) U'); fun_prop
-- combine spectrum.PulseTess. ANC.Budget.F.
local notation "p₀"=> ∏ _i:V,(q:ℂ)⁻¹^4
noncomputable def premiums {V:Type}[Fintype V] (C:Family G)(s:V→ℕ)(m b:ℕ)(q:ℝ):ℂ:= ∏ i:V,((q:ℂ)⁻¹^4 * gate C m b (s i))
local notation "p₁"=> premiums C s m b q
noncomputable def constellation (m:ℕ)(g:Body): Goods G X!:= premiums C s m b q • ∑ i:V→ Site Y!, meet s v q f h i g
include hΨ hq hp hρ
lemma registry (g:Body)(hB:B+A b<ρ₀)(hv: ∀ x∈ support g.val, ‖x‖≤ B): physicalEra q f g C m p N s v= (A b:ℂ)^4 • ∑ z:Site Y!, stepUp t! ((r).embed z) (constellation s v q f h m (restricted C b p z g)):=by
   funext U'; let F(x):=g.val x*(multi C m N p s v (rel q f x) U'); let Y':=(Λ h p);
   let f₀ z:=restricted C b p z g
   have ht(z:Site Y!): (∫ x in Native.box,F (voyager C p b z x)) =(∏ i:V,gate C m b (s i))*∑ o:V→Site Y!,stepUp t! ((r).embed z) (X0 o (f₀ z)) U':=by
       let T₁ : Config G X!:=Lattice.pull 1 ((r).embed z) U'; let a:= ∏ i:V,gate C m b (s i)
       let Y₁(o:V→Site Y!)(x:E4):= (f₀ z).val x*(Y o h (cropX f o q x) T₁); have hw:(∫ x in Native.box,F (voyager C p b z x))= ∫ x in Native.box,a*∑ o: V→Site Y!,Y₁ o x:=by
           refine setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet fun x hx=> ?_; let t:=voyager C p b z x; unfold F; by_cases he:t∈support g.val
           · rw [car s v q f h hq hΨ hp hρ m z x hx (hv t he),Pi.smul_apply,smul_eq_mul, Finset.sum_apply]; change g.val t*(a*∑ i:V→Site Y!,_)=_; rw [mul_left_comm (g.val t) a, Finset.mul_sum (a:=g.val t)]; rfl
           have hT:(f₀ z).val x=0:=notMem_support.mp he; rw [show g.val _=0 from hT]; unfold Y₁; simp_rw [hT,zero_mul]; simp
       rw [hw,integral_const_mul, integral_finsetSum (μ:=volume.restrict Native.box) Finset.univ (fun i (_:i∈@Finset.univ (V→Site Y!) _) => show Integrable (Y₁ i) _ from meet_lives s v q f h i (f₀ z) T₁)]; rfl
   obtain ⟨-,he⟩:= coverings F ((body_smooth g 1|>.continuous).mul (where_cont C p N s v q f m U')) (fun x hx=> hv x (by contrapose! hx; apply notMem_support.mpr; unfold F; rw [notMem_support.mp hx,zero_mul])) hB -- check argument order
   change p₀ * (∫ x,F x)=_; rw [he,Finset.mul_sum]; simp_rw [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,mul_sum]; refine Finset.sum_congr rfl fun i _=>?_; rw [ht i]; unfold constellation premiums; rw [Records.rot_scalar,Records.rot_sum, Pi.smul_apply,Finset.sum_apply,Finset.prod_mul_distrib]; let p:=A b; change p₀* ((p^4) • ((∏ i:V,gate C m b (s i))* _))=(p:ℂ)^4*((p₀* _) * _); rw [Complex.real_smul]; push_cast;ring
end shuttle
end YM.RG05Readout.Pulse
