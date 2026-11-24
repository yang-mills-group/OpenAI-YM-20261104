import YM.FVA2.XReg.Continuum
/-!
# The concrete measurement of the coupling

Same center protocol, same missing/vacuum slots in b3. Don't multiply smeared
arrays for this test; apply Detector on the unsmeared positions first. Exhibit
also the corresponding MS partner at the common scale, and prove convergence to
it (needed for reparametrization).

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Choice
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique Pivot CoverTest Higher State
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
section calculus
open Rose
variable {I:Type*}{P:Filter I}
abbrev Harmony (P: Filter I)(f:I→ Cn)(g:Cn): Prop:= ∀ i:ℕ,Tendsto (fun j=> coeff i (f j)) P (𝓝 (coeff i g))
namespace Harmony
variable {x y:Cn}{f g:I→ Cn}
lemma add (F: Harmony P f x)(H:Harmony P g y): Harmony P (fun i=> f i+g i) (x+y) := by intro i; simp_rw [map_add]; exact (F i).add (H i)
lemma sub (F: Harmony P f x)(H:Harmony P g y): Harmony P (fun i=> f i-g i) (x-y) := by intro i; simp_rw [map_sub]; exact (F i).sub (H i)
lemma mul (F: Harmony P f x)(H:Harmony P g y): Harmony P (fun i=> f i*g i) (x*y):= by intro i; simp_rw [coeff_mul]; exact tendsto_finsetSum _ (fun i _=> ( F i.1 ).mul ( H i.2 ))
lemma smul (F:Harmony P f x)(c:ℂ): Harmony P (fun i=> c • f i) (c • x):= by intro i; simp_rw [map_smul]; exact (F i).const_smul c
lemma cycle {C:I→ℕ→ Point G 6 3} {K:ℕ→Point G 6 3}(H:Pieces P C K): Harmony P (fun i=> b3 (batchT (C i))) (b3 (batchT K)):= by
    let Q(w:Badge)(i:I):= batchT (C i) w; have ht (w: Badge): Harmony P (Q w) (batchT K w):= by unfold Q; intro i; simp_rw [batchT,coeff_mk]; exact H i _
    unfold b3; exact add (sub ( ht Finset.univ ) ( add ( add (mul (ht _) (ht _)) (mul (ht _) (ht _))) (mul (ht _) (ht _)))) (smul (mul (mul (ht _) (ht _)) (ht _)) 2) -- order
lemma C_R [ P.NeBot ] (F:Harmony P f x)(H:∀ᶠ i in P,CoreR (f i)): CoreR x:= by
    apply of_star; intro i; apply tendsto_nhds_unique _ (F i); exact (F i).star.congr' (H.mono fun j hj=> coinR hj i)
end Harmony
lemma b3_p (K:ℕ→Point G 6 3)(p:Cn)(h:Rooted p): b3 (batchT (substitute p K))=(b3 (batchT K)).subst p:= by
    have ht: HasSubst (S:=ℂ) p:= HasSubst.of_constantCoeff_zero' ( (coeff_zero_eq_constantCoeff_apply _).symm.trans h ); unfold b3; simp only [show ∀ j:Badge, batchT (substitute p K) j= (batchT K j).subst p from fun j=>Reg.Point.moves K _ h, ← coe_substAlgHom ht,map_add,map_mul,map_sub,map_smul]
lemma star_p {x y:Cn}(h:CoreR x)(s:CoreR y)(H:Rooted y) : CoreR (x.subst y):= by unfold CoreR; rw [FPS.substitute_ringHom _ x ((coeff_zero_eq_constantCoeff_apply _).symm.trans H), h,s ]
lemma cert {x:Cn}(h: constantCoeff x=0): Rooted x:= (coeff_zero_eq_constantCoeff_apply _ ).trans h
lemma licence (x:Cn) (h:Rooted x) : HasSubst (S:=ℂ) x:= HasSubst.of_constantCoeff_zero' ((coeff_zero_eq_constantCoeff_apply _).symm.trans h)
end calculus
open Rose
variable (ν:ℝ)(Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(S: Prescription (Press.portDeck G)){O:Booked (Press.portDeck G)} (T: MS_Data G O)
abbrev trace (V:Normalize.Store G)(x:Points 3): Cn:= b3 (batchT (wall ν V T 6 x))
def sky : Cn:= μ (fun i=> (Rose.test K).applyTo (fun x=> coeff i ( trace ν T V x )))
local notation "c"=> ( (( c_T K:ℝ ):ℂ)⁻¹ )
abbrev tune (z: Cn) : Cn:= c • (z-C ( coeff 0 z ))
def choice : Cn:= tune K (sky ν K T)
abbrev prospects (m: Mesh): Cn:= ( Rose.chosen Y K m ).subst (Dframe.reset ν S m)
lemma star_q (m:Mesh): CoreR ( prospects ν Y K S m ):= star_p (of_star (fun _=> real_c ..)) (genuine ..) (share ..)
lemma g0 (m:Mesh): Rooted ( prospects ν Y K S m ) := Point.circle _ _ ( cert ( Rose.zero_choice .. ) ) ( share .. )
lemma proper : Rooted ( choice ν K T ):= by unfold Rooted choice tune; rw [ map_smul,map_sub,PowerSeries.coeff_C, if_pos rfl,sub_self,smul_zero ]
variable (h:G.Simple)(hs: TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hv: Ace.UnitP S)
include h hs hr hv
protected theorem Det : Harmony Front (fun i=> (Rose.Detector Y K i).subst (Dframe.reset ν S i)) (sky ν K T):= by
    let q:= reset ν S; let f (l:Sample 3):= (together Y V l).subst (q l.F); have H(x:Points 3)(hx:x∈conf 3): Harmony (Gate x) f (trace ν T V x):= by
        have H:= Harmony.cycle (C:=fun i:Sample 3=> substitute ( q i.F ) ( cooked Y V 6 i )) ( show Pieces (Gate x) _ (wall ν V T 6 x) from fun k p=> moveT ν Y V S T h hs hr hv p k x hx ); exact ( show f=(fun i=> Rose.b3 ( batchT (substitute (q i.F) ( cooked Y V 6 i )) )) from funext (fun i=> ( b3_p _ _ (share ..) ).symm ) ) ▸ H -- rew direction
    intro k; let y:= Rose.test K; let t:Sample 3→ MS.Book.Convolve.T ℂ := fun i j=> coeff j (together Y V i); let F:= fun x=> coeff k (trace ν T V x);
    have hP := Photo.sees_test (conf 3) y F ( conf_open _ ) (show Senses _ (fun i=> coeff k (f i)) _ from fun x hx=> H x hx k) (fun _ _ _=> rfl ) y.tsupport_subset; unfold sky; rw [coeff_mk]; apply hP.congr; intro i; unfold f; simp_rw [← Constants.actual_subst _ ( q _ ) ( share .. ),coeff_mk]; rw [← Constants.actual_subst _ (Dframe.reset ν S i) (share ..), coeff_mk, CoverTest.sub_s i (q:=q) y (ζ:=t) ]; change _=(substitute (q i)) (fun j=> coeff j (Detector Y K i)) k; simp_rw [Rose.detector]; rfl
-- convergence actual measured $φ_g$. Need real.S.Token. $
omit h hs hr hv
lemma tune_p (x y:Cn)(he: Rooted y): (tune K x).subst y=tune K (x.subst y):= by
    unfold tune; rw [ show coeff 0 (x.subst y)= coeff 0 x from ?_, ← coe_substAlgHom (licence y he), map_smul, map_sub, coe_substAlgHom (licence y he), subst_C ]; rfl
    rw [ ← Constants.actual_subst _ _ he, coeff_mk,pay0 ] -- rhs unknown
include h hs hr hv
theorem forecast : Harmony Front (prospects ν Y K S) (choice ν K T):= by
    have ht:= Choice.Det ν Y K S T h hs hr hv; have hf : ∀ i,prospects ν Y K S i=tune K (( Detector Y K i ).subst ( Dframe.reset ν S i )):= fun i=> tune_p K _ _ (share ..)
    intro i; simp_rw [hf]; apply Harmony.smul _ c i; apply Harmony.sub ht _; intro j; simp_rw [ coeff_C ]; split_ifs; exact ht 0; exact tendsto_const_nhds

lemma token : CoreR ( choice ν K T ):= Harmony.C_R ( forecast ν Y K S T h hs hr hv ) ( Eventually.of_forall fun _=> star_q .. )
omit h hs hr hv
lemma stating_one (x y:Cn)(hy:Rooted y): coeff 1 (x.subst y)=coeff 1 x * coeff 1 y:= by rw [FPS.coeff_substituted _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans hy ) ]; simp [ Finset.sum_range_succ ]
include h hs hr hv
theorem stance : coeff 1 ( choice ν K T )=1:= by
    have he:= xc Y K h; apply tendsto_nhds_unique ( forecast ν Y K S T h hs hr hv 1 ); unfold prospects; simp only [ Dframe.reset, stating_one _ _ ( share .. ), Program.ann, mul_one ]; exact he
end YM.FVA2.Reg.Choice
