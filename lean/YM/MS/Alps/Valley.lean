import YM.MS.Alps.Locus
/-!
# Path scaling supports and projection

Curt proof for RHeight. Note extra $-2z+2m,z= -ε$. All W. CovMeasure in beta separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
  {m:ℕ}
lemma mass_sail (k:Touch G m E)(t:E): mass (sail k t)=mass k:= sail_dim ..
lemma s_p_vector (F:Mob G)(W:Touch G m E)(x:E)(t:ℝ)(a:ℂ): fieldVal (plow a t F m) W x=amount (a+(mass W:ℂ)) t*fieldVal (F m) W (exp t • x):= by
   unfold fieldVal plow; rw [mass_sail]; congr 2; unfold sr sail; rw [List.map_map]; simp only [Function.comp_def,map_smul]
variable {z:UScale I}{U:I→ Rip G}{F:I→Mob G}{a:I→ℝ}{v:I→ℝ}{p q:ℝ}
variable (hv:∀ i,v i ≤ p) (hp:∀ i,q ≤ v i)
lemma steady_amount (k:ℂ)(q p:ℝ) : ∃ C:ℝ,0<C∧∀ i∈ Set.Icc q p, ‖amount k i‖≤C := by
   have hx : Continuous (fun i=> ‖amount k i‖):= ( Differentiable.continuous (fun i:ℝ=> (amountD k i).differentiableAt)).norm; obtain ⟨C,hC⟩:=((isCompact_Icc (a:=q) (b:=p)).image (f:=fun i=> ‖amount k i‖) hx|>.bddAbove); exact ⟨max C 1,lt_max_of_lt_right zero_lt_one,fun i hi=>(hC (Set.mem_image_of_mem _ hi)).trans (le_max_left ..)⟩ -- β unknown types
include hv hp
lemma guard_price (k:ℂ): scaleC z 1 (fun i=>‖amount k (v i)‖) := by obtain ⟨C,h,hC⟩:= steady_amount k q p; exact ⟨C,h,0,fun i x hx=>by simpa using hC _ ⟨hp i,hv i⟩⟩
lemma plowP (h: fell z a F)(k:ℂ): fell z a (fun i=> plow k (v i) (F i)):= by
   intro m E _ _ _ w; let x := k+(mass w:ℂ); convert! (at_rate (E:=E) (guard_price (z:=z) hv hp x)).mul (limitF (h m E w) hv) using 1; ext; rw [s_p_vector]; ext; simp
lemma pulseP (h:rib z a U)(k:ℂ): rib z a (fun i=>pulse k (v i) (U i)):= by
   intro m c d; let s:= k-(wfield c:ℂ)-(wfield d:ℂ); have hi:= at_rate (E:=SectorP m) (z:=z) (guard_price (v:=v) hv hp s); convert rails_mul (limitL (h m c d) hp hv) hi using 1; funext i x; exact mul_comm (amount s (v i)) _; simp
variable {U:Rip G}{F:Mob G}{b: Bool}
omit hv hp
lemma powder (h:kPrice F)(a:ℂ)(s:ℝ): kPrice (plow a s F):= plowP (p:=s) (q:=s) (v:=fun _:Unit=>s) (fun _=>le_rfl) (fun _=>le_rfl) h a
lemma priced1 (h:rPrice U)(a:ℂ)(s:ℝ): rPrice (pulse a s U):= pulseP (p:=s) (q:=s) (v:=fun _:Unit=>s) (fun _=>le_rfl) (fun _=>le_rfl) h a
lemma fseed (h:Form0 b F)(a:ℂ)(s:ℝ): Form0 b (plow a s F):= ⟨powder h.price _ _, Stays h.token ..⟩
lemma fze (h:Knot b U)(a:ℂ)(s:ℝ): Knot b (pulse a s U):= ⟨priced1 h.price _ _,mead h.token ..⟩

end YM.MS.Alps
