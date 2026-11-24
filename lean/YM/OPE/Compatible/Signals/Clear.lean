import YM.OPE.Compatible.Maestro.UniformGrid
/-!
# Fixed clearance price. Exterior independent of point locations and phase. Not yet every touching ratio relief. Consumes only full receipts on a subfilter near the issued trajectory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG Wilson Cells Extraction Word Spec
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F : Extraction.Order}{S:Table C.book} (U : Final C F S)
variable {I J X: Type}[Fintype I][Fintype J]
variable {x:I→ Cover} {y:J→ E4} {f : ℕ×ℕ → C.label 0} {B r d m n k W : ℕ} {δ A : ℝ}
variable (w:J→ C.book.Token){v:I→ C.book.Token}{c:ℝ}
omit [Fintype J] in
lemma ClearOf.steered (h : ClearOf (0:E4) y c)(hr:2*C.S.a r<c)(ht:r ≤ k): Apart (2*C.S.a k) y∧ApartFrom (2*C.S.a r) (sole (0:E4)) y:=
   ⟨fun _ _ g=> lt_of_lt_of_le (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (C.S.strictAnti.antitone ht) zero_le_two) hr) (h.spread _ _ g),fun _ _=>lt_of_lt_of_le hr (h.openSpace _)⟩
include U
lemma prepared_some : ∀ᶠ k:ℕ in atTop,∃ p:J→ℝ, Prepared (C:=C) w F k p:=by
    let r(i:J):ℝ:=1+‖(w i).2‖; choose z h X hX hx using fun i=> U.room.copies.centered (w i).1 1 (r i) zero_lt_one (by unfold r; positivity)
    filter_upwards [eventually_all.mpr fun i=> eventually_ge_atTop (z i)] with k hk
    refine ⟨fun j=> X j*(C.S.a k)^(-(↑(w j).1:ℝ)-1)+1,?_⟩; constructor; intro j; rw [Extraction.Order.fused]; exact (hx _ _ (hk j) 1 one_pos).mono fun _ hi=> hi.mono fun _ ⟨hn,hN⟩=>by
       obtain ⟨hu,hv⟩:= hN (w j).2 (le_add_of_nonneg_left zero_le_one) 0; exact ⟨hn,hu,hv⟩
-- scaled bound
lemma clear_of_res (hc:0< c)(h:Org.Grill C F) : ∀ᶠ k:ℕ in atTop,∃ B:ℝ, 0 ≤ B ∧ ∀ (W:ℕ), k ≤ W → ∀ {I:Type}[Fintype I][DecidableEq I]{x:I→ Cover}(v:I→ C.book.Token){f A:ℝ} {d n:ℕ} {q:C.label d}, Survival (C:=C) F k n W f A v x d q → Screen (C.S.gridPoint W ∘ x) → ∀ y:J→ E4, ClearOf 0 y c → Injective (beside (C.S.gridPoint W ∘ x) y) → ∀ p:Viewers U, ‖observe (spectator U p) (beside (C.S.gridPoint W ∘ x) y) (beside v w)-observe (spectator U p) (beside (sole (0:E4)) y) (beside (sole (⟨d,q⟩: C.book.Token)) w)‖ ≤ f * B:=by
    have hw:=C.S.shrinks; obtain ⟨b,hb⟩:= ((hw.const_mul 2).eventually (by rw [mul_zero]; exact gt_mem_nhds hc)).exists; have hh:(Tendsto (fun i=> (1:ℝ)*(2*(5*C.S.a i))) atTop (𝓝 0)):=by simpa only [mul_zero] using (((hw.const_mul 5).const_mul 2).const_mul 1)
    obtain ⟨i,he,hi⟩:= ((hh.eventually (gt_mem_nhds (C.S.a_pos b))).and (eventually_ge_atTop b)).exists; have hx:Tendsto (fun k=> (↑(Fintype.card J):ℝ)*(2*(3*C.S.a k))) atTop (𝓝 0):=by simpa only [mul_zero] using (((hw.const_mul 3).const_mul 2).const_mul (↑(Fintype.card J):ℝ))
    obtain ⟨j,hj,hn,Y,hY⟩:= ((hx.eventually (gt_mem_nhds (C.S.a_pos i))).and ((eventually_ge_atTop i).and (prepared_some U w))).exists
    filter_upwards [eventually_ge_atTop i] with k hk
    refine ⟨∏ u,Y u,hY.cost, fun W hW I _ _ x v f A d n q hp hx y hy hI p=>?_⟩
    obtain ⟨ρ,z,hρ,hf,hq,hu,hZ⟩:=hp.wins
    have hg:Cards.Hall C.S b i k i j 1 (Fintype.card J):=⟨hi,le_rfl,hk,hn,by simpa only [Nat.cast_one] using he,hj⟩; obtain ⟨hP,hZ'⟩:= hy.steered hb hi
    have hv:= viewing_admits U h ((hi.trans hk).trans hW) hx hP hZ' hI hg hf hq hu hY
    have hz:= hZ'.together (mul_nonneg zero_le_two (C.S.a_pos _).le) (injective_of_subsingleton _) (hP.coin (mul_nonneg zero_le_two (C.S.a_pos _).le))
    rw [← glance_sees U p _ _ hI,← glance_sees U p _ _ hz,← map_sub]; exact (glance_bound ..).trans hv
end YM.OPE
