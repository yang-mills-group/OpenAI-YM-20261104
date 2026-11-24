import YM.FormalOPE.RG10.Horizon.Carry
/-! # Short-distance coefficient cost families using all far exteriors

At fixed geometry (absolute test re-announcements). No degeneration past budget.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Panel.Consumer
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}
  {d e n : ℕ} (X: Vantage F) (h:Street Z R) (hc:∀ n,Continuous (fun s=> coeff n (R.flow.psi s)))
local notation "W" => R.flow.warp
abbrev seat (j:Deck F d) : Seats F d:= Pi.single j 1
lemma seating (Z:Seats F d): Z= ∑ i:Deck F d, Z i • seat i := by ext1 j; rw [Finset.sum_apply]; simp [seat,Pi.single_apply, mul_ite]
lemma remained (j:Deck F d) (s:ℝ): W s ∘ seat j=seat j:= by funext i; by_cases h:i=j<;>simp [h, seat]
lemma paying (j:Deck F d) (s:ℝ): trail R s (seat j)= C (Real.exp (-s* Deck.price F d j)) • (fun a=> ((R.route d).lift s) j a):=by
 unfold trail; rw [remained]; ext1 i; change ∑ a, seat j a * _=_; rw [Finset.sum_eq_single_of_mem j (mem_univ _)];
 · simp only [seat,Pi.single_eq_same,one_mul]; exact Passe.lift_entrance (R.route d) ..
 intro a ha h; rw [seat,Pi.single_eq_of_ne h,zero_mul]
lemma bigger (j:Deck F d) (h : d ≤ e) : promote h (seat j) = seat (Deck.climb F h j) := by
 apply unique (proceeds ..); constructor
 · intro i; by_cases hv:j=i; subst i; simp [seat]
   simp only [seat,Pi.single_eq_of_ne (Ne.symm hv),Pi.single_eq_of_ne ((Deck.climb_inj F h).ne (Ne.symm hv))]
 intro i hh; apply Pi.single_eq_of_ne ..; rintro he; exact hh ⟨j,he.symm⟩

include h hc
theorem journey (hδ:∀ n i j,Continuous (fun s=>coeff n ((R.route d).train s i j))) (r:ℕ)(j:Deck F d) :
    Polys (fun s=> Real.exp (s * Deck.price F d j) * coeff r (imply R Z X s d (seat j))) := by
 let K (s:ℝ) : Seats F d := fun a=> (R.route d).lift s j a; let f:= lean R Z X d; let G(s):=f (K s); let w:=Deck.price F d j
 have he (s:ℝ): imply R Z X s d (seat j)= C (Real.exp (-s*w))* W (-s) (G s) := by
   have hx:=shape_cost (U:=seat j) X s h; rw [paying,map_smul,smul_eq_mul] at hx;
   have ht:=congr_arg (W (-s)) hx; rw [map_mul, Flow.at_const] at ht;
   rwa [show W (-s) (W s (imply R Z X s d (seat j))) =_ from by simpa only [neg_neg] using (R.ok.neutral (-s) (imply R Z X s d (seat j)))] at ht
 have ht r : Polys (fun s=>coeff r (G s)) := by
   have hk s : G s= ∑ i, K s i * f (seat i):= by unfold G; nth_rw 1 [show K s= _ from seating (K s)]; simp [map_sum] -- rw both?
   simp_rw [hk,map_sum, coeff_mul]; apply Polys.sum; intro _ _; apply Polys.sum; intro _ _; exact ((R.route d).uniform_lift hδ ..).muls (Polys.const _)
 have hx(s:ℝ): Real.exp (s*w) * Real.exp (-s*w) =1 := by simp [Real.exp_neg]
 simp_rw [he,coeff_C_mul,← mul_assoc]; change Polys fun s=> Real.exp (s*w) * Real.exp (-s*w)* _; simp_rw [hx,one_mul]
 simpa only [neg_neg] using (R.ok.fares hc (n:=r) (f:=fun s=>G (-s)) (fun i _ =>(ht i).stretch)).stretch
omit h hc

section chorus
-- Halo basis exteriors already reflected and reexpressed one at a time in the collector matrices
variable (R Z) (B:Apertures.Halo) (s:ℝ)

def blade (j:Deck F d): Seats F d := fun i=> C ((swing d upright) j i)

def exhibit (j: Deck F d): Vantage F := ⟨1,Arrangements.Halo.ribbon B,d, fun _=> blade j⟩
-- expense in actual pair matrix
private lemma self_raise (U:Seats F d) : promote (le_refl d) U=U:= by
 apply unique (proceeds ..); exact ⟨fun _=>rfl,fun i h=> (h ⟨i,rfl⟩).elim⟩
private lemma duet (L:Test 2)(i: Deck F d)(b:Seats F d) : detect R Z L ![seat i,b]= ∑ j:Deck F d, b j* R.adjust Z d (Apertures.Halo.qd L i j) := by
 unfold detect valuation
 let Q:=Deck F d; let t (p:Q×Q):= R.adjust Z d (Apertures.Halo.qd L p.1 p.2)*(seat i p.1*b p.2); let K:=(finTwoArrowEquiv Q)
 rw [Fintype.sum_equiv K _ t (fun p=> ?_),Fintype.sum_prod_type,sum_eq_single_of_mem i (mem_univ _)];
 · apply sum_congr rfl; intro j _; unfold t; simp [mul_comm,seat]
 · intro j _ h; apply sum_eq_zero; intro _ _; simp [t, seat, Pi.single_eq_of_ne h]
 refine congr_arg₂ (· * ·) ?_ ?_
 · refine congr_arg (fun u:Fin 2→ Deck F d=> R.adjust Z d ⟨⟨2,L⟩,u⟩) ?_; change p=![p 0,p 1]; ext1 i; fin_cases i <;> rfl
 change (∏ j:Fin 2,![seat i,b] j (p j)) = seat i (p 0)*b (p 1); simp [Fin.prod_univ_succ]

theorem hearty (i j:Deck F d) : imply R Z (exhibit B j) s d (seat i)=B.Lens R Z d s i j := by
 unfold imply; rw [seen_on,found]; let U:=trail R (-s) (blade j); change see R Z (fun _:Fin 1=>U) (silver (Arrangements.Halo.ribbon B) s) (fun _:Fin 1=>seat i)=_
 erw [extension R Z (k:=d) _ _ _ le_rfl le_rfl]; simp_rw [Function.comp_def, self_raise]; rw [show Fin.append (fun _:Fin 1=> seat i) (fun _:Fin 1=>U)=![seat i,U] from by ext1 x; fin_cases x <;> rfl,duet]
 unfold U trail; simp_rw [show W (-s) ∘ blade j= blade j from funext (fun i=> R.flow.at_const _ _), Matrix.vecMul,dotProduct, Finset.sum_mul]
 unfold silver Apertures.Halo.Lens; rw [Arrangements.Halo.squared,Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]; rw [sum_comm]
 apply sum_congr rfl; intro a _; apply sum_congr rfl; intro z _;
 change ((C ((swing (F:=F) d upright) j a)* R.drive (-s) d a z)*_)=(_* R.drive (-s) d a z)* C ((swing d upright) j a); ac_rfl

lemma heartbeat (g:Seats F d) (i:Deck F d): imply R Z (exhibit B i) s d g=(g ᵥ* B.Lens R Z d s) i:=by
 conv_lhs=>rw [seating g]
 rw [map_sum]; simp_rw [map_smul,hearty,smul_eq_mul]; rfl
end chorus
end YM.FormalOPE.RG10.Panel.Consumer
