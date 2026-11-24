import YM.SignedWilsonExpansion.Belfry.Lumi
/-! # Billing GENERAL composite polynomial in stencil/pin. compact & arity caps. This
    is WHERE uniformity in norm bound is asserted: basis (ℂ) scalar-budget iid. Real
    and complex allowed. All finite lists of words, including connected/log ones, subtraction
    with true cutoff units. Only truncates transformed y. Use higher moment credit
    to attain full order-saving O(t^{p+1}). No interior derivative inside normalized supports
    required for comparison at this stage. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle.Entree
open Belfry Belfry.ScaleFits Belle -- maybe unknown
open FVA2 -- diagnostic
open FVA2.Scale Path Lesson Buffet Dancer Dancer.Drawing Dancer.SeatsW
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book
open MeasureTheory Filter Function Set Asymptotics PowerSeries XSpace XSpace.Normalize XSpace.Structure1 FVA2.Reg
open Maxwell Maxwell.Free WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.Crops MarqueQ.PorchK Commission Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d n:ℕ}{ι W F:Type}
inductive Cup (W:Type)
| val (r:ℂ) | cup (w:W) | and (p q:Cup W)| times (p q:Cup W)
variable {R:Type}[Ring R][Algebra ℂ R]
def Cup.dispense (x:W→R) : Cup W→ R | .val v=> v • (1:R) | .cup w => x w | .and p q=> p.dispense x+ q.dispense x | .times p q=> p.dispense x*q.dispense x
/-- cap ordering. Pulled through sensors & observables. -/
abbrev Fixed (L:Filter ι)(U:Set (Points n))(Y:ι→Points n→ Point G d n)(θ:ι→ℝ)(P:Way G d)(b:ℕ) := ∀ v:Tags G d n,Serves L (fun i x=>Y i x v) (fun i x=> mote P b x (θ i) v) U (θ^b)
abbrev regular (P:Way G d)(n:ℕ):Prop := ∀ b:ℕ,∀ v:Tags G d n,ContinuousOn (fun x=> Jury.fxt P x b v) ( conf n )
lemma Basket.tea {ι:Type}(L:Filter ι)(θ ε:ι→ℝ)(b:ℕ)(v:ℂ): Basket L b θ ε (fun _=> v • (1:PowerSeries ℂ)) (fun _=> v • (1:ℂ)):=by
    refine ⟨ fun i _=> Wage.unitC _,isBigO_const_const _ one_ne_zero _,?_⟩; simp_rw [map_smul,calcT, LinearMap.comp_apply,trunc_one, AlgHom.toLinearMap_apply,map_one,sub_self]; exact isLittleO_zero ..
lemma Basket.serve {x:ι→ W→PowerSeries ℂ}{y:ι→ W→ℂ}{L:Filter ι}{θ ε:ι→ℝ}{b:ℕ}(u: Cup W)(p:Tendsto θ L (𝓝 0))(s:(fun i=> θ i^(b+1))=o[L] ε)(h:∀ i,Basket L b θ ε (fun j=>x j i) (fun j=>y j i)) : Basket L b θ ε (fun i=> u.dispense (x i)) (fun i=> u.dispense (y i)):=by
    induction u with
    | cup u=> exact h u
    | val v=> exact Basket.tea ..
    | and u v i j=> exact Buffet.Basket.plus i j
    | times u v i j=> exact Buffet.Basket.eggs ( by simpa using (p.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1)) ) s i j
variable {U:Set (Points n)}(A:Roi U)(L:Filter ι){Y:ι→Points n→Point G d n}{θ:ι→ℝ}(p:Tendsto θ L (𝓝 0))(P:Way G d)(v:W→ι→Tags G d n)(k:Cup W)
local notation "E"=> diners L U
variable (t:regular P n)(w:∀ i:W,∀ j: Fin n, SeatsW.Salary ℂ L 1 (fun k=> v i k j))
abbrev formal (v:W→ Tags G d n)(u:Cup W)(x:Points n): PowerSeries ℂ:= u.dispense fun i=> Reg.Point.story ( Jury.fxt P x ) ( v i )
abbrev realistic (v:W→ Tags G d n)(X: Point G d n)(u:Cup W):ℂ:= u.dispense fun i=> X ( v i )
include A p t w
lemma nuk (b:ℕ)(T:Fixed L U Y θ P b): Basket E b (θ ∘ Prod.fst) ((θ^b) ∘Prod.fst) (fun i=> formal P (fun u=> v u i.1) k i.2) (fun i=> realistic (fun u=>v u i.1) (Y i.1 i.2) k):=by
    have he:= Wipe.expense p IsEquivalent.refl (Nat.lt_succ_self b); refine Basket.serve k (p.comp plot_le) (he.comp_tendsto plot_le) fun a=>?_
    let H:= v a; let X(u:ι):= fun x:Points n=> Y u x (H u); let F(u:ι):= fun x:Points n=> mote P b x (θ u) ( H u ); let K(u:ι×Points n):= Reg.Point.story ( Jury.fxt P u.2 ) ( H u.1 ); have hz: Serves L X F U (θ^b):=by
      refine Serves.fix (serving (F':=fun i=> vis P (θ i) b (n:=n)) (?_) H (w a)) (Eventually.of_forall fun i _ _=> rfl) (Eventually.of_forall fun i y h=> vision ..); intro x; simp_rw [vision]; exact T x
    have hK: PorchK.charge b E 1 1 K:=by
        intro i _; unfold K Reg.Point.story; simp_rw [ coeff_mk ]; refine Wage.enroll ( SeatsW.matIncome (fun y=>?_) (fun i f=>(w a i f).comp_tendsto plot_le) ); have ht:= (t i y).norm.mono A.2; obtain ⟨B,z⟩:= (A.1.image_of_continuousOn ht).bddAbove; exact IsBigO.of_bound B ( plot_in.mono fun i h=> (z (mem_image_of_mem _ h)).trans_eq (by simp) )
    let θ':= θ∘(Prod.fst:ι×Points n→ι); have hf: buys F=fun i=>calcT (θ' i) b (K i):=by
        ext1 i; unfold F buys; rw[timed]; unfold Path.mote K Reg.Point.story; simp_rw [coeff_mk]; exact Finset.sum_congr rfl fun j _=> mul_comm ..
    have ha:Tendsto θ' E (𝓝 0):= p.comp plot_le; refine ⟨hK,?_,?_⟩; · have hu:buys F=O[E](1:ι×Points n→ℝ):=hf ▸ Buffet.Basket.earns (by simpa using ( ha.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1))) hK; exact Buffet.inCash (banquet.mp hz) hu (( ( Wipe.stop p ).pow b|>.congr_right fun i=> one_pow _ ).comp_tendsto plot_le )
    change (fun i=> buys X i - calcT (θ' i) b (K i))=o[_] _ ; exact (banquet.mp hz).congr_left fun i=>by change _ - buys F i=_;rw[hf]
lemma honor (b:ℕ)(T:Fixed L U Y θ P b): Serves L (fun i x=> realistic (fun u=>v u i) (Y i x) k) (fun i x=> calcT (θ i) b ( formal P (fun u=>v u i) k x )) U (θ^b):=banquet.mpr ( nuk A L p P v k t w b T ).cost
lemma earn (b:ℕ)(T:Fixed L U Y θ P (b+1)): buys (fun i x=> realistic (fun u=>v u i) (Y i x) k - calcT (θ i) b (formal P (fun u=>v u i) k x) )=O[E]((θ^(b+1)) ∘ Prod.fst):=by
    let X(i:ι×Points n):= formal P (fun u=> v u i.1) k i.2; have he:= nuk A L p P v k t w (b+1) T; have ht:= Buffet.unfoldW ( he.purse (b+1) le_rfl ); have hv:= plot_le (U:=U) (L:=L); have hz:(fun v:ι×Points n=>(θ v.1:ℂ)^(b+1))=O[E]((θ^(b+1)) ∘ Prod.fst):=IsBigO.of_bound' ( Eventually.of_forall fun i=>by rw [norm_pow,Complex.norm_real,comp_apply,Pi.pow_apply,norm_pow] ); refine (he.cost.isBigO.add ((ht.mul hz).congr_right fun i=> one_mul _) ).congr_left (fun i=>?_); change _ - _ + _ = _ - _; rw [timed_step]; simp only [comp_apply]; abel
-- profile Budget first direct with explicit L1 times p^b power. uniform anytime after limit. no compact derivative expenses here
omit A p t w
lemma profileC {U:Set (Points n)} {x y:ι→Points n→ℂ}{T:ι→ℝ}(L:Filter ι)(p:buys (x-y)=O[diners L U]( T∘ Prod.fst ))(hx:∀ᶠ i in L,ContinuousOn (x i) (conf n))(hy:∀ᶠ i in L,ContinuousOn (y i) (conf n)): ∃ C:ℝ,0<C∧∀ᶠ i in L,∀ f:Test n,tsupport f ⊆ U → ‖f.applyTo (x i)- f.applyTo (y i)‖ ≤ ( ∫ k:Points n,‖f k‖ )*(C*‖T i‖):=by
   obtain ⟨C,h,H⟩:= p.exists_pos; refine ⟨C,h,?_⟩; filter_upwards [ diners_clause.mp H.bound,hx,hy ] with i hi hx hy f hf; unfold Test.applyTo; rw [←integral_sub (f.smearing hx) (f.smearing hy)]; let k:=C * ‖T i‖; have he(u:Points n): ‖f u*x i u-f u*y i u‖≤‖f u‖*k:=by
      by_cases h:u∈tsupport f; · rw [←mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (hi u (hf h)) ( norm_nonneg _ )
      simp [image_eq_zero_of_notMem_tsupport h]
   exact ( norm_integral_le_of_norm_le ((f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm.mul_const k) (Eventually.of_forall he) ).trans_eq (by rw[integral_mul_const])
end YM.SignedWilsonExpansion.Belle.Entree
