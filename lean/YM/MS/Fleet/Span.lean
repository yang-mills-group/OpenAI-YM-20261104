import YM.MS.Fleet.Drive
/-!
Precision lemma for multilinear transport of `Crew` to `Fields`. Here Q=0 required on subsets
with at least two distinct sites (=marks, use no bare contact insertions). No separation condition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W}
 {F H:Glade G I}{X:Rake.Dance G I W}{Q:Seeds G I W}{n:ℕ}
variable (c:Berth ( W:=W ) ( I:=I )) {A:Faces I}
local notation "Ψ"=> ( outside L )
local notation "m0"=> (fun (_:I)=>planeF)
local notation "ιW"=> ( Orbit.uniform G I )
open Rake.Geo Vane Land
local notation "ρk"=> ( constantP G I (LowP G) )
local notation "Y"=> ( constantP G I (PlanetL G) )
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Rake.Geo I}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
lemma π_src (T:Prescription B) (A:Faces I)(S:Finset W)(L':I→Side) (T':∀ s j,Toned ( X s j )) (t:ℝ)(n:ℕ)(i:I):
 (Vista.fort (outside L') A ιW (Scope G (Wind.skyline G T.team) R.η) 0 X S n i (exp t)) = (((exp t:ℝ) :ℂ)⁻¹) • frameL ( anchorC c S i )
      ((sailP m0 Y (voyage c X S n)+Rake.multi m0 (info c) ρk Y (initials R T) (voyage c X S) (voyage c X) n S) i t) := by
    suffices hx: frameL (anchorC c S i) _ = ( exp t:ℂ) • _ from by rw [hx,inv_smul_smul₀ (by norm_cast; exact (exp_pos t).ne')]
    unfold Vista.fort campus multi; rw [ Vista.idle_d (D:=0) rfl, add_zero ]; unfold archB; simp only [ Pi.add_apply, map_add, Finset.sum_apply, smul_add, Finset.smul_sum,map_sum ]
    refine congr_arg₂ _ ( ( τuis (T' S n) (anchorC c S) (L:=L') A i t ).trans (smul_add ..) ) (congr_arg₂ _ ( lights T (R:=R) (anchorC c S) n i t (X S) ) ( Finset.sum_congr rfl fun p hp=> Finset.sum_congr rfl fun j hj=>?_)); exact ( π_joins c A p hp i t _ _ (L:=L') (T' p j.1) (T' _ _) ).trans ( smul_add .. )


private lemma fee_curve {f:ℝ→ℂ} (h:Continuous f)(x:ℝ): IntegrableOn (fun t:ℝ=> exp t • f ( exp t )) ( Iic x ):= by
   let s:= Set.Icc (0:ℝ) (exp x); obtain ⟨ C,hC ⟩ := ( isCompact_Icc (a:=0) (b:=exp x)|>.image h.norm ).bddAbove; apply Integrable.mono' ( ( integrableOn_exp_Iic x ).mul_const C ) (Continuous.aestronglyMeasurable (by fun_prop)); filter_upwards [ae_restrict_mem (μ:=volume) (s:=Set.Iic x) measurableSet_Iic] with t ht; rw [norm_smul,Real.norm_of_nonneg (exp_pos _|>.le)]; exact mul_le_mul_of_nonneg_left (hC ( Set.mem_image_of_mem _ (show exp t∈s from ⟨ exp_pos _|>.le, exp_monotone ht⟩))) ( exp_pos _ |>.le )
omit [LinearOrder W] in
lemma curve (h:Modal F H)(x:Faces I)(hu:Toned H)(hv:∀ i,F i 0=0): let V:=vessel F x; let P(i:I)(t:ℝ): Law G:= (exp t :ℂ) • vessel H x i t; collect V ∧ Job.train false P∧ V=Job.river P := by
   intro V H'; let B(i:I)(F:Law G):= unload ( x i ) F; have ht (F:Law G)(i:I)(l: List (Lane4 G)): B i F l=(hook weightψ l*be (-x i) (net l))* F l:= by rw [show B i F=sleeve weightψ ( lodging (- x i) F ) from rfl, sleeve_here,lodg, ← mul_assoc];
   let p(F:Glade G I)(i:I)(l:Legs (Lane4 G))(s:ℝ):= B i (F i s) l
   obtain ⟨k,hk⟩:= h.cap; have he(i:I)(l:Lengths G)(t:ℝ): H' i t l= exp t • p H i l ( exp t ):= by rfl
   have hD(i:I)(l:Lengths G)(s:ℝ): HasDerivAt ( p F i l ) ( p H i l s ) s:= by unfold p; simp_rw [ ht ]; exact ( h.pace .. ).const_mul _
   have hP: Job.train false H':= by intro i s l _; simp_rw [he]; refine fee_curve ?_ s; unfold p; simp_rw [ht]; exact (hu.touch i |>.at_const _ l contDiff_id |>.continuous.const_mul _) -- lemma name Wind
   refine ⟨ ⟨ k,fun i t l hl=>?_ ⟩, hP,funext fun i=>funext fun s=> funext (fun l=>?_ ) ⟩; · change B i _ _ = 0; rw [ ht,hk i ( exp t ) l hl,mul_zero]
   change p F i l (exp s) = ∫ r in Set.Iic s, H' i r l; have hd:= fun t:ℝ=> ( hD i l ( exp t ) ).scomp t ( Real.hasDerivAt_exp t ); rw [ integral_Iic_of_hasDerivAt_of_tendsto' ( f:=(p F i l ∘ Real.exp) ) (m:=0) ( fun t ht=> he i l t ▸ hd t ) (hP i s l (fun v=> Bool.noConfusion v)) ?_,sub_zero]; rfl; have hx : p F i l 0=0:= by unfold p; rw [ ht, hv i,Pi.zero_apply,mul_zero ]
   rw [← hx]; exact ( ( hD i l 0 ).continuousAt.tendsto ).comp tendsto_exp_atBot
end YM.MS.Fleet
