import YM.AllOrder.Catch.Tent
import YM.AllOrder.Fire.PriceR
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module ConnectedActivityE6 Blaze Brush
open Metric ProbabilityTheory Filter
open scoped Topology ContDiff BigOperators Classical
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X] {n k:ℕ} {f:X→ℝ}{A B C d:ℝ}
def Warrant (C a:ℝ)(n:ℕ)(x:X)(f:X→ℝ):Prop:= Rank X n f ∧ ∀ i∈closedBall x a, |f i|≤C
local notation "T"=> Warrant (X:=X)
lemma hiring (n:ℕ):∃ C:ℝ,0 ≤ C ∧∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{p a:ℝ}{f:X→ℝ}(x y:X), Warrant p a n x f→0<a→
  Warrant (‖y‖*(p*C*a⁻¹)) (a/2) n x (diff' y f):= by
 obtain ⟨F,hF,h⟩:= analytic_cost (n+1); let R:= (↑(n+1):ℝ); have ht : 0<R:=(by unfold R; positivity); let Y:= Fin (n+2)
 refine ⟨2*R*F,by positivity,?_⟩; intro X _ _ _ p a f x y hx ha; have hp:0≤p:= (abs_nonneg _).trans (hx.2 _ (mem_closedBall_self ha.le)); refine ⟨(hx.1.der y).up (by omega), fun z hz=>?_⟩
 by_cases he : y=0; subst y; simp [diff']
 have hhx:0<‖y‖:= norm_pos_iff.mpr he; let s:= a/(2*R*‖y‖); have hs:0<s:=by unfold s; positivity
 let L:= ContinuousLinearMap.toSpanSingleton ℝ (s • y); let g (t:ℝ):= f (z+L t)
 have hh(i:Y):|g i.val|≤ p := by
   apply hx.2; rw [mem_closedBall_iff_norm]; rw [show z+L (i.val:ℝ) -x=z-x+(i.val*s:ℝ) • y from (by simp only [L, ContinuousLinearMap.toSpanSingleton_apply, smul_smul]; abel)]; apply (norm_add_le ..).trans; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤ (i.val*s:ℝ))]; let v:= i.isLt
   calc _ ≤ a/2 + R*s*‖y‖:= by gcongr; exact mem_closedBall_iff_norm.mp hz; unfold R; exact_mod_cast (show i.val≤n+1 from (by omega))
        _ ≤ _:=le_of_eq (by unfold s; field_simp; ring)
 have hℓ:=h g ((hx.1.app L z).up (Nat.le_succ n)) _ hh (⟨1,by omega⟩); have hQ:someJ g 1= s*diff' y f z:= by unfold g L; change someJ (fun t:ℝ=> f (z+t • s • y)) 1=_; rw [← licensed hx.1.read.smooth.contDiffAt]; simp only [diff',map_smul,smul_eq_mul]
 apply le_of_mul_le_mul_left _ hs; calc
    s*|diff' y f z|= ‖someJ g 1‖:= by rw [hQ,norm_mul,Real.norm_of_nonneg hs.le]; rfl
    _ ≤ p*F:= hℓ.trans_eq (mul_comm ..)
    _ ≤ _:= le_of_eq (by unfold s; field_simp)
lemma measureW (j n:ℕ): ∃ C:ℝ, 0<C∧∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{p a:ℝ}{f:X→ℝ}(x:X), Warrant p a n x f→0<a→normJ j f x≤p*C*(a⁻¹)^j := by
 induction j with
 | zero=> refine ⟨1,zero_lt_one,?_⟩; intro X _ _ _ p a f x hx ha; simp only [normJ, norm_iteratedFDeriv_zero, pow_zero, mul_one]; exact hx.2 _ (mem_closedBall_self ha.le)
 | succ j ih=>
    obtain ⟨C,hC,H⟩:=ih; obtain ⟨K,hK,h⟩:= hiring n; refine ⟨1+K*C*2^j,by positivity,?_⟩; intro X _ _ _ p a f x hx ha; have hz:0≤p:= (abs_nonneg _).trans (hx.2 _ (mem_closedBall_self ha.le)); apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro v; let u:= v (Fin.last j); let L:= ContinuousLinearMap.apply ℝ ℝ u; let z(i:Fin j) := v i.castSucc; let g:= diff' u f; have hp:= H X x (h X x u hx ha) (half_pos ha); unfold normJ at *; rw [← show iteratedFDeriv ℝ j g x z= iteratedFDeriv ℝ (j+1) f x v from ?_]; swap
    · rw [show g=L ∘ fderiv ℝ f from rfl, L.iteratedFDeriv_comp_left (hx.1.read.smooth.contDiffAt.fderiv_right (m:=ω) (by simp)) le_top, iteratedFDeriv_succ_apply_right]; rfl
    let M:= ∏ i:Fin j, ‖z i‖; have hM:0≤ M:=by unfold M; positivity
    apply ((iteratedFDeriv ℝ j g x).le_opNorm z).trans; rw [Fin.prod_univ_castSucc]; change _ ≤ _ * (M * ‖u‖); refine (mul_le_mul_of_nonneg_right hp hM).trans ?_; rw [inv_div] -- fix
    calc _=p*(K*C*2^j)*(a⁻¹)^(j+1)*(M*‖u‖):= by -- parse
           rw [div_eq_mul_inv]; ring
         _ ≤ _:= by gcongr; exact le_add_of_nonneg_left zero_le_one
lemma signW (j n:ℕ): ∃ C:ℝ,0<C∧∀ (X:Type) [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{p a:ℝ}{f:X→ℝ}(x:X), Warrant p a n x f→0<a→ Brush j (p*C) (a⁻¹) f x := by
 choose f hp hx using (fun k=> measureW k n); let S:= range (j+1); refine ⟨1+∑ i∈S,f i,add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg (fun i _=> hp i|>.le)),?_⟩; intro X _ _ _ p a F x hX ha; have h:0≤p:= (abs_nonneg _).trans (hX.2 _ (mem_closedBall_self ha.le)); refine ⟨hX.1.read.smooth.contDiffAt.of_le le_top,by positivity, fun i hi=> (hx i X x hX ha).trans ?_⟩; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ h) (by positivity); exact (single_le_sum (f:=f) (fun x _=> hp x|>.le) (show i∈S from mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
-- Scale u(t)=β^-? bounding paying hats with exact support power
namespace Warp
open Catch Catch.Clock
variable {ι:Type*}{Q:Clock ι} (V:ι→Type) [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)][∀ i,FiniteDimensional ℝ (V i)]{b x t:ι→ℝ}{f:(i:ι)→ V i→ℝ}{y z:∀i,V i}
local notation "P"=> Q.book (fun i=> closedBall (y i) (b i))
local notation "M"=> Q.Meter
lemma action (k:ℕ)(h:∀ᶠ i in Q.rail,Rank (V i) n (f i))(he:(P).Meter (fun i=> f i.1 i.2.1) C)(ht:∀ᶠ i in Q.rail,0<b i): Catch.Cover Q k C (fun i=>(b i)⁻¹) f y:= by
 intro e hv; obtain ⟨T',hT,H⟩:= signW k n; obtain ⟨p,hp,hq⟩:= exists_between hv; filter_upwards [Q.booked (fun i=> closedBall (y i) (b i)) (fun i j=> |f i j|≤ Q.cost i^p)|>.1 (he p hp),h,ht,Q.slack hq T'] with i hi hI hx hp; apply (H (V i) (y i) ⟨hI,hi⟩ hx).climb (le_trans (mul_comm _ _).le hp.le) le_rfl
end Warp
end YM.AllOrder.Fire
