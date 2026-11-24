import YM.MS.Rock.InTown
/-!
# Route integrability at compact support

All moment shifts use actual full measure. ProperSpace operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Landau Arts Pilot Spin Arc Wire Path
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  {b c: Bool}{m:ℕ}{A B:ℝ}{U V:Rip G}{F H:Mob G}
variable (hf:kPrice F)(hH:kPrice H)(hu:rPrice U)(hv:rPrice V)
include hf hH hu
lemma column_cost {w f: tagSmooth E (Cfield G m) (SectorP m)}(hx:Trail w)(hy:Trail f)(a b:Cfield G m): Continuous fun x:E=> radius Landau.parity (U m) a b (F m) (H m) (walk0 w x) (walk0 f x):= by
   let d(x:E): SectorP m:= -net (walk0 w x); -- p universe stuck fix
   have he: ContDiff ℝ ∞ d:= hx.net0.neg; have hr := (turf_cost hf m (hx.cons a d he)).continuous; have hh:= (turf_cost hH m (hy.cons b (-d) he.neg)).continuous
   have hp(x:E): degree (field Landau.parity) (walk0 w x)= degree (field Landau.parity) w:= by clear he hx hr hh d; induction w with| nil=>rfl |cons i l ih=> simp only [walk0] at *; rw [List.map_cons,degree_cons,degree_cons (x:=i)]; rw [ih]
   unfold radius; simp_rw [hp]; exact ( ((continuous_const.mul (((hu m a b 0).smooth ()).continuous.comp he.continuous)).mul (continuous_const.mul hr)).mul hh )
include hv
lemma hitsAt (n:ℕ)(l r: Legs (Shore G n))(a e i j:Cfield G n)(hA:rock A V): Integrable (hits Landau.parity (U n) (V n) (F n) (H n) l r a e i j) (Px n) := by
   unfold Px; refine far_support _ ?_ (A:=A) ?_ volume; · unfold hits; refine ((hv n a e 0).smooth ()).continuous.mul (continuous_const.mul ?_); convert! column_cost hf hH hu (plain0 l |>.cons a (id:SectorP n→ SectorP n) contDiff_id) (plain0 r|>.cons e ( -id) contDiff_id.neg) i j using 1; ext; rw [show ∀ (x:SectorP n),walk0 ((a,id):: constX _ l) x=(a,x):: l from ?_, show ∀ (x:SectorP n),walk0 ((e,-id)::constX _ r) x=(e,-x)::r from ?_] <;> (intro x; unfold walk0; simp; exact plainX .. ) -- syntax
   intro x hx; unfold hits; rw [hA n _ _ _ hx,zero_mul]
lemma maintenance (n:ℕ)(hA:rock A V)(hr:Reverse (V n) Landau.parity): Heat.Route (U n) (V n) Landau.parity (F n) (H n) (Px n) where
   lf i j a b c d:= hitsAt hf hH hu hv n i j a b c d hA -- syntax
   rf i j a b c d:= by
       let R :=restL Landau.parity (U n) (V n) (F n) (H n) i j a b c d; let L:=hits Landau.parity (U n) (V n) (F n) (H n) i j b a c d; have ht : Integrable L volume:=hitsAt hf hH hu hv n i j b a c d hA
       change Integrable R MeasureTheory.volume; rw [show R=L ∘ Neg.neg from funext (fun i=>by nth_rw 1 [← neg_neg i]; exact RL hr ..)]; exact (Measure.measurePreserving_neg _).integrable_comp_of_integrable ht
   shift := by intro i j a b c d; unfold Px; exact integral_sub_left_eq_self ..
   flip := by intro i j a b c d; unfold Px; exact integral_neg_eq_self ..
end YM.MS.Rock
