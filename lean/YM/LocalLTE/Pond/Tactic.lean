import YM.LocalLTE.Pond.Elsa
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
-- template post.All reorder. use q≤J grade and one residual. telescopic. Integral.
open Averaging Song Refrain Ovens Payments
section math
variable (R c p) (M:ℕ)
def labelsX (u:Config G n) := u
def stairs (f:EKey n→ Pot G n) (F:ℕ→ EKey n→ Pot G n): ℕ→ EKey n→Pot G n := fun k=> if k=M+1 then f - F M else if k=0 then F 0 else (F k)-(F (k-1))
-- Post uses ℕ encoded. duplicate summables.Stuff. Ensure grade record PLAIN after rotation
abbrev Rol (M:ℕ)(n:Side):= Seat n × (Fin (M+2) × EKey n)
abbrev Fol (n:Side):= ℕ ⊕ Spikes n
-- grades and rotate orbit FULL lattice. Note layout rank numbering.Consequences.
def sands (i:Fin (M+2) × EKey n):= Price.tubeX R p X i.2
def bells : Pipes G n where
   reg:= Song.revolve (sands p R X M) ∘ numbering (Rol M n)
   kernel:= (shelves X R p).kernel
   softer:= Sum.elim ((shelves X R p).softer) (fun i=>(Price.ridge R p i).support) ∘ numbering (Fol n)
   sites i:= by change (Sum.elim ((shelves X R p).softer) (fun i=>(Price.ridge R p i).support) (numbering (Fol n) i)).Nonempty; cases numbering (Fol n) i; exact (shelves X R p).sites _ -- edit
                next j=> exact ⟨_,(Price.ridge R p j).anchor⟩
local notation "R₀" => archive X R c g
-- need fill branch True.D.alpha tested.
def silt (Δ α:ℝ) (F:ℕ→ EKey n→ Pot G n) (i: Fin (M+2) × EKey n) := stairs M (R₀ α Δ) F i.1.val i.2
def azures (Δ α:ℝ) (F:ℕ→ EKey n→ Pot G n) : Tap G n where
   regular:= Song.choir (Price.silt c R X g M Δ α F) ∘ numbering (Rol M n)
   forced:=g.hardRead
   logarithm:= Sum.elim (fill X R c p g α Δ|>.logarithm) (fun i=>Price.remises Δ α p R i) ∘ numbering (Fol n)
-- arithmetic
section
variable {G₁: Type}[AddCommGroup G₁] (a:ℝ→G₁)
lemma bridged {α:Type} [AddCommGroup α] (h:ℕ→α)(m:ℕ) : ∑ i∈Finset.range (m+1), (if i=0 then h 0 else h i -h (i-1)) = h m:=by
    induction m with
    | zero=> simp
    | succ m ih=> rw [Finset.sum_range_succ,ih,if_neg (by omega),Nat.add_sub_cancel]; abel
lemma rounded (i:EKey n)(e:EKey n→Pot G n)(f:ℕ→ EKey n→Pot G n)(b:ℝ)(Y:Support n)(U:Config G n): ∑ j: Fin (M+2), masked b Y (stairs M e f j i) U= masked b Y (e i) U:=by
   rw [Fin.sum_univ_eq_sum_range (fun j=> masked b Y (stairs M e f j i) U)]
   by_cases h:Healthy b Y U
   · simp_rw [masked_eq _ _ _ _ h]; rw [Finset.sum_range_succ,stairs,if_pos rfl]
     rw [Finset.sum_congr rfl (g:=fun k=> if k=0 then f 0 i U else f k i U - f (k-1) i U) (fun j hj=> by have hx:= Finset.mem_range.mp hj; unfold stairs; rw [if_neg (by omega)]; split <;> rfl), show ∑ j∈ Finset.range (M+1), _=_ from bridged (fun j=> f j i U) M]; change f M i U+(e i U- f M i U)= _; ring
   simp_rw [masked_ne _ _ _ _ h]; simp
end
end math
end YM.AnalyticBridge.VerifiedReset.Collection.Price
