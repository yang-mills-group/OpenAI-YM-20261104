import YM.WilsonCoeffUV.Winding.Receipt
/-!
# Mark constructors and interval-purchase scope for any inherited bulk census
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries Bank.Mosaic Bank.Carp
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β T:Type}{V:Type}{G:Gauge}{D k:ι→ℕ}{Ñ:ChartRatio G}{m N i j r e a l f:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}{E H:Credit}{Q:Realm G (e+1) E}{R: Levels G}
lemma price_leaf {p:ℕ}(s:ℝ)(h:0<s)(α:Type)[Fintype α]: 0≤ priceM α p s + tiePay α p (s/4) + 1:= add_nonneg (add_nonneg (priceMP _ _ h) (tie_non (show 0<s/4 from by positivity))) zero_le_one
-- receipt includes points outside cleared hull only in tor widths.

variable [DecidableEq ι]
def diamond (G:Gauge)(e r:ℕ)(s:ℝ):= 1+∑ i∈Finset.range (1+r+e), (priceM (Hooks G) i s+tiePay (Hooks G) i (s/4)+1)
lemma diamond_nn (G:Gauge)(p:0<s):1≤ diamond G e r s:= le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>price_leaf s p _)
lemma wins (G:Gauge)(p:0<s)(q:i<1+r+e) : priceM (Hooks G) i s+tiePay (Hooks G) i (s/4)+1≤ diamond G e r s:=by
    unfold diamond; exact (Finset.single_le_sum (f:=fun i=> priceM (Hooks G) i s+tiePay (Hooks G) i (s/4)+1) (fun _ _=> price_leaf s p (Hooks G)) (Finset.mem_range.mpr q)).trans (le_add_of_nonneg_left zero_le_one)

def flowOne (Q:Realm G (e+1) E)(Z:Finset ι)(K:family G D)(m N:ℕ)(v:Q.anchor≤m)(o: m<N)(s:ℝ)(b:0<s)(y:ι→Cover)(z:ι→ Site (loose Q.draws m).L)(h:K ∅=0)(t:Eu k K)(A:ℝ)(a:0≤ A)
    (x:safeB (chartIn (loose Q.draws m) y z) K Z e s A)(n:Side): PackOne Z D k e (holt Q m v s b):= by
    let R:=Q.draws; let I:= holt Q m v s b; let V:= cloVent Q m N n v o s b; let r:= mass k Z; let d:=diamond G e r s; have hp:1≤d:=diamond_nn G b; have hv:=emera_far Q.draws Q.hG Q.green (show m+1≤ N from o) (n*(loose Q.draws m).L)
    have hb: I.s≤ s/32:= min_le_left ..
    refine ⟨V,y,z,repaint K,hv.1,hv.2,?_,repose t,d*A,mul_nonneg (zero_le_one.trans hp) a,?_⟩
    · unfold repaint; rw [h,remake_zero]
    intro S q j l i; let X:=chartIn I.P y z
    change MarkU X S (Bank.Carp.plume ((K S).2 j i) (n*I.P.L)) ((K S).2 j i) _ _
    rw [mul_pow]
    have hA:0≤ A^S.card:= pow_nonneg a _; have hB:0≤ d^S.card :=pow_nonneg (zero_le_one.trans hp) _; by_cases w:S=∅
    · subst S; rw [h]; change MarkU X _ (Bank.Carp.plume 0 _) 0 _ _; rw [Bank.Carp.plume_zero]; exact MarkU.zero.more (mul_nonneg hB hA)
    by_cases he: 1+r+e ≤ i
    · rw [(t S).coverN _ _ ?_,Bank.Carp.plume_zero]; exact MarkU.zero.more (mul_nonneg hB hA); have ht: mass k S ≤ mass k Z:=by unfold mass; exact Finset.sum_le_sum_of_subset q
      omega
    let u:=Finset.nonempty_iff_ne_empty.mpr w; refine ((plumeW (x _ q _ l _) u b).mono hb).more ?_; apply mul_le_mul_of_nonneg_right _ hA; exact (wins (e:=e) (r:=mass k Z) G b (by omega)).trans (by change d≤ d^S.card; exact le_self_pow₀ hp (Nat.ne_of_gt (Finset.card_pos.mpr u)))
lemma rimMoney (G:Gauge)(i j e:ℕ)(h:i≤ e): ∃ d:ℕ,∀ I:Gear G,∃ A:ℝ,0≤A ∧ ∀ C: Rally (e+1) 0 I, rimJ C.P.moving i j ≤ A*C.x^d:=by
    let S:= Finset.range (i+1); let V:= Fin i.succ
    have H (t:V):∃ d:ℕ,∀ I:Gear G,∃ A:ℝ,0≤A∧∀ C:Rally (e+1) 0 I, ‖PowerSeries.coeff (i-t.val) (C.P.moving^t.val*(C.P.moving⁻¹)^j)‖≤A*C.x^d:=by
       obtain ⟨d,H⟩:= titles (G:=G) (e:=e+1) (i:=i-t.val) (by omega) 0 t.val j; refine ⟨d,fun I=>?_⟩; obtain ⟨b,p,h⟩:= H I; exact ⟨b,p,fun C=> (h C).main⟩
    choose d H using H; let w:=∑ i,d i; refine ⟨w,fun I=>?_⟩; choose c f g using fun i=>H i I; refine ⟨∑ i,c i,Finset.sum_nonneg fun i _=> f i,fun t=>?_⟩; unfold rimJ; rw [← Fin.sum_univ_eq_sum_range,Finset.sum_mul]; apply Finset.sum_le_sum; intro a _; exact (g a t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ t.rich (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ a))) (f a))
lemma flowBolt (Q:Realm G (e+1) E)(Z:Finset ι)(K:family G D)(m N:ℕ)(v:Q.anchor≤m)(o:m<N)(s:ℝ)(b:0<s)(y:ι→Cover)(z:ι→Site (loose Q.draws m).L)(h:K ∅=0)(g:Eu k K)(A:ℝ)(a:0≤A)(x:safeB (chartIn (loose Q.draws m) y z) K Z e s A)(n:Side)(J):
   Blue.mix (ratioHigh Q.draws Q.paid N m) ((flowOne Q Z K m N v o s b y z h g A a x n).cabinJ J)= ((logO Q.draws Q.paid m N K k) J).2:= (onSide Q.draws Q.paid m N K k h g Q.hG Q.green o J).symm
end YM.WilsonCoeffUV.Winding
