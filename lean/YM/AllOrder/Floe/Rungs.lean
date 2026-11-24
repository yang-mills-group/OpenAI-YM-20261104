import YM.AllOrder.Floe.Fortune
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Aero Pace Rent Iron PriceCompiler Bloch
namespace PlanV
variable (g:G.Simple) (A:ℕ→Stage)(d f:ℕ→ℝ)(U:MapPrices)
-- Constrain target by outside ticket, to reuse low path startup or neighbouring widths. D positive possibly very small.
variable (N:ℕ)(T:Age) (S S' s s': Fees)(hS:∀ i,0<S i)(hS':∀ i,0<S' i)
section
lemma sharpen {ι : Type*}(v:Finset ι)(P:ι→ℝ→Prop)(h:∀ i∈v,∃ w:ℝ,0<w∧∀ u,0<u→u≤w→ P i u):∃ w:ℝ,0<w∧∀ u,0<u→u≤ w → ∀ i∈v,P i u:= by
 induction v using Finset.induction_on with
 | empty=> exact ⟨1,zero_lt_one,fun a _ _=> by simp⟩
 | insert i s ht ih=> obtain ⟨p,hp,H⟩:=ih fun i hi=>h i (mem_insert_of_mem hi); obtain ⟨q,hq,hg⟩:= h i (mem_insert_self ..); refine ⟨min p q,lt_min hp hq,fun a ha he x hx=>?_⟩; rcases mem_insert.mp hx with hh|hh; rw [hh]; exact hg a ha (he.trans (min_le_right ..)); exact H a ha (he.trans (min_le_left ..)) x hh
lemma pre_eq (q:Stage) {σ a C:ℝ} (h:PriorDue G q.clip a q.width q.paths S S' b ε N T C σ) (H:∀ i, Age.before i T→S i=s i)(hv:S' T=s' T)(hV:∀ i,i.e < T.e→S' i=s' i): PriorDue G q.clip a q.width q.paths s s' b ε N T C σ := by
 refine ⟨⟨h.reach.pos,h.reach.slant, (fun i hi=> hV i hi ▸ h.reach.spark i hi),fun hk=> hv ▸ h.reach.june hk, fun hk=> hv ▸ h.reach.castle hk⟩, ?_⟩
 obtain ⟨u,φ,he,hV,hν,H₀,h'⟩ :=h.good; exact ⟨u,φ,he,hV,hν,H₀, fun i hi=> H i hi ▸ h' i hi⟩
include g hS hS'
lemma anchor (p:Stage)(q: Stage)(C B δ:ℝ)(hp:0<C)(h:0≤B)(ht:0<δ) : ∃ u:ℝ,0<u ∧ ∀ (s' s:Fees),0 < s' T→ s' T ≤ u→ (∀ i, Age.before i T→ s i=S i) → (∀ i,i.e<T.e→ s' i=S' i) → ∃ v:ℝ, PriorDue G q.clip p.width q.width q.paths s s' C δ N T B v:= by
 let f:= T.prereq (tape T.e); have hf i (hi:Age.before i T):i∈f:= Finset.mem_filter.mpr ⟨Age.in_scope.mpr (le_iff_lt_or_eq.mpr (by rcases hi with hi|hi; exact Or.inl hi; exact Or.inr hi.1)),hi⟩
 obtain ⟨u,hu,hU⟩:= sharpen f (fun i v=>v≤leaseF (S i) N) (fun i _=>⟨_, lease_pos (hS i) _, fun _ _ h=>h⟩); obtain ⟨v,hv,hξ⟩:=sharpen f (fun i v=> Sparkle G (S' i) v (T.r-1) i.r) (fun i _=> Aero.sparkle G (S' i) (hS' i) _ _); obtain ⟨Q,hQ,hη⟩:= angles G q.clip q.width q.paths q.width_pos q.paths_pos.le (T.r-1); let c:=min C (min u (leaseF p.width N)); have hc:0<c:= lt_min hp (lt_min hu (lease_pos p.width_pos _)); let x:= mills c N T
 have hx:0<x:= by
    unfold x mills; dsimp only; apply div_pos; unfold weaker; apply div_pos (Rail.widthG_pos (soprano N hc _)) (by positivity); norm_num
 let y:=min δ (min x (min v Q)); have hy:0<y:=lt_min ht (lt_min hx (lt_min hv hQ)); obtain ⟨u₀,h0,hr⟩:= Aero.july G g y B hy h
 have hP : ∃ u₁:ℝ,0<u₁∧∀ z,0<z→ z≤ u₁→ 3≤T.r→ Castle G y z T.r:=by by_cases ht:3≤T.r; obtain ⟨u,h,H⟩:=Aero.towersK G y T.r hy ht; exact ⟨u,h,fun i x h _=> H i x h⟩; exact ⟨1,by norm_num,fun _ _ _ hx=> (ht hx).elim⟩
 obtain ⟨u₁,hν,hP⟩:= hP; refine ⟨min u₁ u₀,lt_min hν h0,fun s' s he hl h' hx=> ⟨y,⟨?_,c,hc,(min_le_right ..).trans (min_le_right ..), min_le_left ..,?_,?_,?_⟩⟩⟩
 · refine ⟨hy,hη _ hy ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))),fun i hi=> hx i hi ▸ hξ y hy ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))) i (hf _ (Or.inl hi)), fun hz=>hr _ he (hl.trans (min_le_right ..)),hP _ he (hl.trans (min_le_left ..))⟩ -- Eq orientation likely h'.symm ▸
 · exact (min_le_right ..).trans (min_le_left ..)
 · exact min_le_left ..
 intro i hi; rw [h' i hi]; exact hU c hc ((min_le_right ..).trans (min_le_left ..)) i (hf i hi)
end
end PlanV
end YM.AllOrder.Floe.Step
