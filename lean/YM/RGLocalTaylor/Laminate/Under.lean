import YM.RGLocalTaylor.Laminate.Ahead

/-!
# Horizon invariant for marked log (no param-derivative pose on cutoff assumed)

same thresholds/B/chart. Also empty column exactly coincides with unmarked
Mayer even off-mask. These are on native unanchored pre-reset representation.
No claim of compatibility across prescriptions clipping on different post
support-with-costs addresses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March Captain
namespace Laminate
open RG01.Survive Trees Merge Palette Gas Ursell Marker GridApprox.Nil
open MergeProof.Accent AnalyticBridge VerifiedReset Quotes Next.Foundations
variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ)(H)
    {τ:Type} [DecidableEq τ] {Cen : Marker.Census τ}(o': τ→Site c) (p:BudgetPoint) (y:ι→Poly Cen) (cost:τ→ℝ) (keep:H.fragrances→ℕ→Prop) (z:H.fragrances)
-- proof across all Field.
lemma horizonHold (h: k≤l) (hp:∀ n,keep z n→ n≤k) : stained M' rA y z (χ:=χ) keep k=stained M' rA y z (χ:=χ) keep l:= by
  funext V; unfold stained
  let f (t:Flight M' z k)(i:Option (Fin z.fst)) : VoucherL M' S l:= ((t i).1, Fin.castLE (by omega) (t i).2)
  let A n:= univ.filter (passenger M' z keep (k:=n)); have Ht (n) t (hv:t∈ A n) (i:Option (Fin z.fst)): (t i).2.val ≤ k:=
       le_trans (single_le_sum (f:=fun i:Option (Fin z.fst)=> (t i).2.val) (fun _ _=> Nat.zero_le _) (mem_univ i)) (hp _ (mem_filter.mp hv).2.2)
  apply Finset.sum_bij (fun t _=> f t)
  · intro t h; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2 ⟩
  · intro a ha b hb hh; exact funext fun i=>Prod.ext (congr_arg (fun v:VoucherL M' S l=>v.1) (congr_fun hh i)) (Fin.ext (congr_arg (fun (t:VoucherL M' S l)=> t.snd.val) (congr_fun hh i)))
  · intro t hv; let g (i:Option (Fin z.fst)):VoucherL M' S k:= ((t i).1, ⟨(t i).2.val,lt_trans (Nat.lt_succ_of_le (Ht _ _ hv i)) (Nat.lt_succ_self _)⟩); exact ⟨g,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩
  intro t hv; unfold grain paints; apply congr_arg₂ (· • ·) _ rfl; apply congr_arg; unfold columnKey; congr 1; refine prod_congr rfl fun i _=>?_; unfold f mint rector; congr 1; let b: Fin (k+1):=⟨(t i).2.val,Nat.lt_succ_of_le (Ht k t hv i)⟩; exact congr_fun (commonColumn (χ:=χ) _ _ _ b (Fin.castLE (by omega : k+1≤l+1) b) rfl) V

private lemma adopts (F' : Team R)(hv:F'.own=∅) (p:Molecule S) (t:ℕ): Laminate.scopeM F' p H (χ:=χ) k t=Mayer.atLeaf H p χ k t := by
  unfold Laminate.scopeM Mayer.atLeaf Team.signs; rw [hv,image_empty, sdiff_empty]; split
  · funext V; unfold Mayer.coefficient; refine sum_congr rfl fun i _=>?_ ; let f:= partner F' H; let g:= leg H (own p)
    apply congr_arg (fun s:Insert T=> s.onLog H χ p V)
    change Insert.mk _ = Insert.mk _; congr! 1; funext F X z; change ∏ i'∈ p,(Mayer.payload H p f i i').value X z=∏ i'∈p,(Mayer.payload H p g i i').value X z; exact prod_congr rfl fun i hi=> by unfold Mayer.payload; rw [dif_pos hi,dif_pos hi]
  rfl

omit [Fintype ι] in
lemma parity (t:VoucherL M' S k) (p:H.ThinP) (he : t.fst.val=∅) (V:Config G c): mint M' rA p (χ:=χ) V t = Mayer.issue H χ k p t.2 V:= by
  unfold mint rector packPrice; let X:= team M' t.1
  have hv:X.own=∅:= by unfold X team; dsimp only; rw [he,image_empty]
  rw [show ∏ i ∈ t.fst.val,rA i=1 from by rw [he,prod_empty],one_mul]; change column X _ _ _ _ _= _; unfold Mayer.issue column; have hy:X.signs S=∅:=by unfold Team.signs; rw [hv,image_empty]
  rw [if_pos (show X.signs S⊆ p.val from hy ▸ empty_subset _)]; unfold Laminate.excess; simp_rw [adopts _ X hv]; unfold frontLoad; rw [hy,sdiff_empty, Mayer.dad]; rfl
end Laminate
end YM.RGLocalTaylor
