import YM.MS.Vista.BranchC
/-!
# Viewing.Unfurl.Budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}[NormedAddCommGroup E][NormedSpace ℝ E]{S:Scale I}
 {K L:I→Latch.Edge G}{X Y:I→Law G}{h x y:I→ℝ}{A:I→Cover}
structure Fund (S:Scale I)(K:I→Latch.Edge G)(A:I→ℝ): Prop where
    cost : Price S K A
    perk : PerK K
    room : ∀ i,1≤ S.length i
abbrev tinted (K:I→Latch.Edge G) (v:I) : Latch.Edge G:=fun i j q=> (aisle q:ℂ)*K v i j q
lemma tint (h:Fund S K x): Sheet S x (tinted K):= fun i j=> folding (h.cost.2 i j) (veiled h.perk i j) h.room
-- plane vs mesh all.Op.B.Phase.A.Lev
variable {μ ν:I→Measure QP}
structure VistaQ (S:Scale I)(μ ν:I→Measure QP): Prop where
   folds : ∀ i (F:QP→ℂ),pinQ F→Continuous F→(∫ p,(aisle p:ℂ)* F p∂ν i)= ∫ p,F p ∂μ i
   mint : Mint S ν 5
   sector : glob S ν 5
def Radar (S:Scale I)(v:I→ℝ)(p:I→Cover)(μ:I→Measure QP): Prop:= ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ (f:I→ QP×E→ℂ) (x:I→ℝ), pole S f x→∀ j:ℕ, Bound S (waveInt (fun i=> be (p i)) μ f) (fun i=>x i*fee S i * (S.length i / v i)^j)
lemma routineQ (S:Scale I): VistaQ S (fun _=> μzone) (fun _=>planeF):= ⟨ fun i F hp hv=> shineZ hv (pin_C hp),fun E _=> tom _ _ (by omega), Tall _ _ (by omega)⟩
variable {Γ:I→Side}
lemma μSize (Γ:I→Side)(i:I): ψstep (Γ i)=tier/(Γ i|>.val:ℝ):= rfl
-- measure career
lemma ν_engine (h:∀ i,S.length i ≤ ( Γ i|>.val:ℝ)): ∀ i,S.length i*ψstep (Γ i)≤tier:= fun i=>le_trans (mul_le_mul_of_nonneg_right ( h i ) ( ψpp _ |>.le)) (le_of_eq (by rw [μSize Γ i]; obtain he:= Bloch.side_pos (Γ i); field_simp ))
lemma f_cap (h:∀ i,S.length i ≤ ( Γ i |>.val:ℝ)): VistaQ S (fun i=>σcap (Γ i)) (fun i=>totalS (Γ i)):= by
   let b(i):=ψstep (Γ i); have hb(i:I):0<b i:= ψpp _; refine ⟨ fun i F hf hx=> ( smoothP hf hx (Γ i))|>.trans (siteI (Γ i) F|>.symm),fun E _=> spending hb rising.le (ν_engine h) ( show 5>4 by omega ),local_p hb rising.le (ν_engine h) ( show 5>4 by omega ) ⟩ -- namespace
-- continuity & membership. Need touchF assumption for using F not measure.
def Visible (X:I→Law G): Prop:= Voiced X∧∀ i,TouchF (fun _=> X i)
abbrev payF (b:Bool)(K:I→Latch.Edge G)(F:I→Law G)(w:Lengths G)(t:I)(q:QP):= ∑ i:BH G,∑ j:BH G,K t i j q * F t ((i,q)::(j,Opp b q)::w)
lemma A_Fr (h:Fund S K x)(i:I): flex (fun _=> K i):= fun a b=> ((h.cost.1 a b).smooth i).comp contDiff_snd
lemma tasteβ (K: I→Latch.Edge G)(b:Bool)(p:I→Cover)(F:I→Law G)(t:I)(w:Lengths G)(q:QP): (aisle q:ℂ)*wait b (p t) (K t) (F t) w q= be (p t) q * payF b (tinted K) F w t q := by unfold wait payF tinted; simp_rw [  Finset.mul_sum, mul_assoc, mul_left_comm (aisle q:ℂ) ]; -- ignores revert order likely
lemma mint_pc (h:Fund S K x)(hp:Visible X)(b:Bool)(i:I)(w:Lengths G): pinQ (wait b ( A i ) ( K i ) ( X i ) w) ∧ ContDiff ℝ ∞ (wait b ( A i ) ( K i ) ( X i ) w) := by
   constructor
   · intro p q he; unfold wait; have hx: congrQ ( Opp b p ) ( Opp b q ):= by cases b; exact he.opp; exact he
     rw [ show be (A i) p = be (A i) q from φ_per _ he ]; refine congr_arg _ ( Finset.sum_congr rfl fun i' _=> Finset.sum_congr rfl fun j _=>?_ ); exact congr_arg₂ _ (h.perk i i' j he) (hp.1 i _ _ (.cons ⟨rfl,he⟩ (.cons ⟨rfl,hx⟩ ( asc _) )))
   have hv:= Hz b ( A i ) ( hp.2 i ) (w:= City.station w) (station_t w) (A_Fr h i) (contDiff_const (c:=0)) (K:=fun x:QP=>x) contDiff_id; simpa only [station_w] using hv
lemma portPC (he:VistaQ S μ ν)(hp: Fund S K x)(hf:Visible X)(i:I)(b:Bool)(w:Lengths G): Θ_pc b (μ i) (A i) (K i) (X i) w = ∫ q, be ( A i ) q * payF b (tinted K ) X w i q ∂ν i := by obtain ⟨h,hT⟩:= mint_pc (A:=A) hp hf b i w; refine Eq.trans (he.folds i _ h hT.continuous|>.symm ) ?_; simp_rw [ tasteβ ] -- μpoint
end YM.MS.Vista
