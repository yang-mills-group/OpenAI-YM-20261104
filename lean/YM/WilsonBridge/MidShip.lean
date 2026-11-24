import YM.WilsonBridge.WaveReaders
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
/-!
# One-mode sampling factors. Exact symbol comparison at the massless endpoint.

Do NOT assume perfect point evaluations past a stencil's declared rank. Integrated over
the physical link. With its own ell_i factor per leg, relates midpoint convention. The
endpoint power budget `Left.char` will allow canceling ell per mode, no bound in the tails.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonBridge.Sailing
open Reader Function Finset Filter Set MeasureTheory
open PertExtension PositionX Next.Rank
open MS Book Koszul Cylinder Lab Native Native.Studio Sew MS.Theater
open Plane Native.Chart Tone Tone.Frame Landau Detect Wire
open scoped ContDiff Topology BigOperators RealInnerProductSpace
open InnerProductSpace Momentum Lattice CellsInt
open Complex (I)
variable {G:Gauge}{N:Type} {d i j:ℕ}
local notation "Χ"=> Draft.DotFlip (G:=G) (P:= QP)

-- Fourier phase on the REAL continuum point. Norm estimates global.
def mρ (p:QP) (x:E4):ℂ:= Complex.I * (↑(inner ℝ (fixF p) x):ℂ)
def χ (p:QP)(x:E4)(t:ℝ):ℂ:= bill (t • p) (Theater.out x)
lemma mρ_s (p:QP):Continuous (mρ p):= continuous_const.mul (Complex.continuous_ofReal.comp ( continuous_const.inner (𝕜:=ℝ) continuous_id ))
lemma mρ_t (p:QP)(x:E4)(k:ℕ) : mρ p x ^ k= hitϑ k * ↑((inner ℝ (fixF p) x)^ k):= by unfold hitϑ mρ; push_cast; rw [mul_pow]
lemma cash_t (p:QP)(x:E4)(t:ℝ): χ p x t= Complex.exp ((t:ℂ)*mρ p x):= by
    have he:pairing (t • p) (Theater.out x)= t*inner ℝ ( fixF p ) x:= by
        simp only [pairing, Pi.smul_apply, smul_eq_mul,PiLp.inner_apply,Finset.mul_sum,mul_assoc]; apply Finset.sum_congr rfl; intro i _; congr 1; exact mul_comm .. -- fix inner_apply
    unfold χ bill mρ; rw [he,Complex.ofReal_mul]; congr 1; ring
lemma cashS (p:QP) (t:ℝ): Continuous (fun x:E4=> χ p x t):= by simp_rw [cash_t]; exact Complex.continuous_exp.comp (continuous_const.mul ( mρ_s .. ))
@[simp] lemma cash₀ (p:QP)(x:E4): χ p x 0=1:= by simp [χ]
lemma cashA (p:QP)(x y:E4)(t:ℝ): χ p (x+y) t= χ p x t*χ p y t:= by unfold χ; rw [map_add,rightadd]
lemma cash_N (p:QP)(k:ℕ)(x:E4)(t:ℝ): HasDerivAt (fun t:ℝ=> (mρ p x)^k * χ p x t) ((mρ p x)^(k+1) * χ p x t) t:= by
    simp_rw [ cash_t ]; have he: HasDerivAt (fun t:ℝ=>(t:ℂ)*mρ p x) (mρ p x) t:= by simpa using! (Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const (mρ p x); -- #check
    apply ((he.cexp).const_mul _).congr_deriv; rw [pow_succ]; ring
-- kernel on an edge and its Taylor operators

def whole (p:QP)(a:Axis)(k:ℕ)(x:E4)(t:ℝ):= east a (fun y:E4=> (mρ p y)^k * χ p y t) x
lemma wholeD (p:QP)(a:Axis)(k:ℕ)(x:E4)(t:ℝ): HasDerivAt (whole p a k x) (whole p a (k+1) x t) t:= by
    let Y (s:ℝ):=x+s • basis a
    let F (k:ℕ)(t s:ℝ):= ( mρ p (Y s) )^k * χ p (Y s) t; let b(s:ℝ):= ‖mρ p (Y s)‖^(k+1); have hy:Continuous Y:=continuous_const.add (continuous_id.smul continuous_const); have he (k:ℕ)(t:ℝ):Continuous (F k t):=(( mρ_s p |>.comp hy).pow k).mul (( cashS p t ).comp hy)
    apply ( intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F k) (F':=F ( k+1 )) (x₀:=t) (s:=Set.univ) Filter.univ_mem (.of_forall fun t=> (he k t).aestronglyMeasurable) ((he k t).intervalIntegrable ..) ((he (k+1) t).aestronglyMeasurable) (bound:=b) ( Eventually.of_forall fun i _ t _=>?_ ) (( mρ_s p |>.comp hy|>.norm ).pow (k+1) |>.intervalIntegrable ..) (Eventually.of_forall fun i _ t _=> cash_N p k _ t) ).2
    unfold F χ; rw [norm_mul,norm_pow,Tone.bill_norm,mul_one]
lemma wholeI (p:QP)(a:Axis)(k:ℕ)(x:E4): iteratedDeriv k (whole p a 0 x)=whole p a k x:= by
    induction k with | zero=>rfl | succ k h=> rw [iteratedDeriv_succ,h]; exact funext fun t=> (wholeD p a k x t).deriv
lemma wholeS (p:QP)(a:Axis)(x:E4): ContDiff ℝ ∞ (whole p a 0 x):= by
    rw [contDiff_iff_iteratedDeriv]; exact ⟨fun k hk=> by rw [wholeI]; exact continuous_iff_continuousAt.mpr fun t=>(wholeD p a k x t).continuousAt, fun k hk=>by rw [wholeI]; exact fun t=>(wholeD ..).differentiableAt ⟩
lemma whole_read (p:QP)(a:Axis)(x:E4)(k:ℕ): reading k (whole p a 0 x)=hitϑ k * ↑(east a (fun y=> amount k*(inner ℝ (fixF p) y)^k) x):= by
    rw [reading, wholeI, whole]; unfold east; simp_rw [cash₀,mul_one,mρ_t]; let f (i:ℝ):=(inner ℝ (fixF p) (x+i • basis a))^k
    let L:=Complex.ofRealCLM; rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]; change amount k • (hitϑ k*(∫ i:ℝ in 0..1,L (f i))) = _; rw [L.intervalIntegral_comp_comm]; rw [Complex.ofReal_mul,Complex.real_smul]; unfold L; change ((amount k:ℂ)*(hitϑ k * ↑(∫ i:ℝ in 0..1,f i)))=hitϑ k*( ↑(amount k) * ↑(∫ i:ℝ in 0..1,f i)); ring
    exact (show Continuous f from (Continuous.inner (𝕜:=ℝ) continuous_const (show Continuous (fun i:ℝ=> x+i • basis a) from (by fun_prop))).pow k).intervalIntegrable ..

-- mode-specific sampling cost returns unphased ell
def takeW (u:Lane4 G): ℝ→ℂ:= match u with
   | (((some a,false), _),p)=> whole p a 0 ((- (1/2):ℝ) • basis a)
   | _=> fun _=>1
lemma ellt (p:QP)(a:Axis)(c:Conn G)(t:ℝ): takeW (waveForm p a c) t= whole p a 0 ((- (1/2):ℝ) • basis a) t:= rfl
lemma ell1 (u:Lane4 G): takeW u 0=1:= by rcases u with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> simp [takeW,whole, east]
lemma ells (u:Lane4 G): ContDiff ℝ ∞ (takeW u):= by rcases u with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> first| exact contDiff_const| exact wholeS ..
lemma cervical (p:QP)(a:Axis)(c:Conn G)(x:Cover)(t:ℝ):
    takeW (waveForm p a c) t * bill (t • p) (embed x+ Frame.z a)=whole p a 0 (mapZ x) t:= by
    let A:=mapZ x + (1/2:ℝ) • basis a; have he:Theater.out A = embed x+Frame.z a := by unfold A; rw [map_add,map_smul]; congr 2; ext i; simp [Tone.embed]
    rw [ ellt, ← he ]; unfold whole east; simp only [pow_zero,one_mul]; rw [ ← intervalIntegral.integral_mul_const ]; apply intervalIntegral.integral_congr; intro i hi; rw [ ← show χ p A t=bill (t • p) (Theater.out A) from rfl]; dsimp only; rw [← cashA, show ((-(1/2):ℝ) • basis a+i • basis a)+A = mapZ x+i • basis a by unfold A; module]
-- vector link charge.No projected trajectories.
open Tensor

def trip (i:ℕ)(x:Edge Cover): Feet G i →ₗ[ℝ] G.Color where
    toFun p:= east x.2 (diagonal (p.val x.2)) (mapZ x.1)
    map_add' v w:= by rw [show diagonal ((v+w).val x.2)= diagonal (v.val x.2) + diagonal (w.val x.2) from rfl, east_add .. ]; rfl; exact (diag_smooth _ 1).continuous; exact (diag_smooth _ 1).continuous
    map_smul' c X:= by rw [show diagonal ((c • X).val x.2)= c • diagonal (X.val x.2) from rfl, east_scale]; rfl
lemma tripGrad (i:ℕ)(x:Edge Cover)(X:Head G (i+1)) : trip i x ((gradS G i) X)= diagonal (X.val ()) (mapZ (x.1+step x.2))-diagonal (X.val ()) (mapZ x.1):= by
    change east x.2 (diagonal ((stepL G Unit i x.2 X).val ())) _=_; rw [stepL,workL, mapZ_step ]; change east x.2 ( Maxwell.grad x.2 (diagonal (X.val ()))) _=_; rw [lights _ ( diag_smooth _ 1 )]; rfl

def cycle (x:Cover)(a b:Axis)(i:ℕ) : Feet G i→ₗ[ℝ] G.Color:= trip i (x,a)+trip i (x+step a,b)-trip i (x,b)-trip i (x+step b,a)
lemma cycling (x:Cover)(a b:Axis)(i:ℕ)(X: Head G (i+1)) : cycle x a b i ((gradS G i) X)=0 := by
    unfold cycle; simp_rw [LinearMap.sub_apply,LinearMap.add_apply,tripGrad]; rw [add_right_comm x]; abel
lemma sculpt (X:Feet G i)(x:Cover)(a b:Axis): cycle x a b i (carve G i X)=cycle x a b i X:= by rw [carveΩ,map_sub,map_smul,cycling,smul_zero,sub_zero]
lemma cycle₀ (X:Feet G 0)(x:Cover)(a b:Axis): cycle x a b 0 X=0:= by
    rw [← sculpt]; have hz:=house X; rw [weightT] at hz; rw [show carve G 0 X=0 from (Submodule.mem_bot ℝ).mp hz,map_zero]
lemma retrip (s:Cover)(a b:Axis)(X:Feet G (d+1)): cycle s a b (d+1) X= CellsInt.test (yard G d X) a b s:= by
    rw [cigar]; dsimp only [Pi.sub_apply,CellsInt.stepValue]; have he (u:Axis)(x:Cover): CellsInt.trail (yard G d X) u x= trip (d+1) (x,u) (carve G (d+1) X):= rfl
    simp_rw [he]; rw [← sculpt X ]; unfold cycle; simp only [LinearMap.add_apply, LinearMap.sub_apply]; abel

lemma edge_test (x:Cover)(p:QP)(a b:Axis)(c k: Conn G)(t:ℝ): takeW ( waveForm p a c ) t * paywave (waveForm (t • p) a c) (formAt b k x) = if a=b ∧ c=k then whole p a 0 (mapZ x) t else 0:= by
    rw [ show paywave _ _= _ from please (x,b) a c k (t • p) ]; unfold matchA; by_cases h:c=k <;> by_cases hz:a=b
    · subst h; subst hz; simpa only [if_true,and_self] using cervical p a c x t
    all_goals simp [*,Ne.symm] -- inspect
lemma test_result (x:Cover)(p:QP)(a b:Axis)(c k:Conn G) : reading i (fun t:ℝ=> takeW ( waveForm p a c ) t * paywave ( waveForm ( t • p ) a c ) (formAt b k x)) = hitϑ i* (↑( trip i (x,b) ( speak i a p (cl G c) ) k):ℂ):= by
    let J:= speak i a p (cl G c); let z:=mapZ x; let f:=diagonal (J.val b); let h:= fun i':Axis=> (fun s:E4=> diagonal (J.val i') s); simp_rw [edge_test];
    unfold trip; dsimp only [LinearMap.coe_mk, AddHom.coe_mk];
    suffices hu: (east b (h b) z) k= if a=b ∧ c=k then east a (fun y=> amount i * (inner ℝ ( fixF p ) y)^i ) z else 0 by
        change reading _ _=hitϑ i * ↑((east b (h b) z) k); rw [hu]; by_cases hk:a=b∧c=k; simp_rw [if_pos hk]; exact whole_read p a z i; simp_rw [if_neg hk]; simp [ reading ]
    unfold east; let L:= EuclideanSpace.proj (𝕜:=ℝ) k; change L (∫ r:ℝ in (0:ℝ)..1,h b (z+r • basis b))= _; rw [ ← L.intervalIntegral_comp_comm ?hnt ];
    have hy(y:E4) : L (h b y)=if a=b ∧ c=k then amount i * (inner ℝ ( fixF p ) y)^i else 0:= by
       by_cases ht:a=b; swap; · simp [h,ht, L, J, speak,away _ _ _ (Ne.symm ht),Tensor.diagonal]
       rw [← ht ]; unfold h J speak Tensor.diagonal; rw [wearing]; by_cases hk:c=k <;> simp [ht,hk,map_smul,Ne.symm,cl,L] -- inspect
    simp_rw [hy]; split
    next hk=> simp_rw [hk.1]; -- after substituting b etc
    next hk=> simp
    case hnt=> exact east_int _ _ (diag_smooth (J.val b) 1).continuous
lemma print_L (d:ℕ)(w:LatticePT.Atom G):
     let K(i:ℕ):Witness G i:= Complex.ofRealCLM.toLinearMap ∘ₗ LinearMap.proj (Heat.Ray.address w) ∘ₗ Beamer.sweep i
     Heat.Ray.print d (MvPolynomial.X w)=∑ i∈ Finset.range (d-1), page i (K i):= by
    intro K; apply Labels.eval_ext; intro X; rw [Heat.Ray.display_jet, map_sum,Spindle.text, MvPolynomial.aeval_X ]; simp_rw [ bookX ]; change ((Spindle.oneGlow d (Source.Drops.trunk d X) (w.1.offset,w.1.plaq) w.2:ℝ):ℂ)=_; rw [Spindle.glows]; let L:=EuclideanSpace.proj (𝕜:=ℝ) w.2
    change (L (∑ i∈ Finset.range (d-1), CellsInt.test _ _ _ _):ℂ)=_; rw [map_sum,Complex.ofReal_sum ]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Source.Drops.expand, dif_pos (Finset.mem_range.mp hi) ]; rfl
end YM.WilsonBridge.Sailing
