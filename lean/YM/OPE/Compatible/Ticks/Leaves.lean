import YM.OPE.Compatible.Ticks.NewLine
/-! Initialize all leaf paths from their *own* aperture k. Above k,
no lump of growth in dimension, already at its true annotation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C){V:Type}[Fintype V][DecidableEq V] (P:Ensemble V)
variable {N p k j b d:ℕ}{E o:Track C.path V p}
set_option quotPrecheck false
variable (v:C.label d)
local notation "F"=>C.labels.level d
local notation "g"=> fun x y=>stepUp (P.move x) (o N x) (C.O N p v 0) y
variable {a:ℝ}
lemma fresh_line (h:C.Makes)(hb:1 ≤ b)(hk:C.ref 0 ≤ k)(hm:C.ref d ≤ j)(hK:k ≤ j+1)(hN:j<N)
    (he:Migrating C.path k p N E)(hz:Migrating C.path (j+1) p N o)(hZ:∀ i:ℕ,k ≤ i → i < j+1 → (C.path.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i)
    (hx:∀ i,j+1 ≤ i→ i ≤ N→ ∀ x:V, x≠P.v→ o i x=affine (P.move x).1 (E i x) (o i P.v))
    (hv:0<a)(hW:2*a* Next.Rank.Spindle.paid C d (j+1) N p v ≤ fly C.path.levels d (j+1)):
    ∃ L:Line A P N p k N b E o, L.w k=Run.Below C.path a (j+1) k ∧ Budges P C.path N p (far C.path.levels N) (L.w N) (E N) (L.X N) g ∧
      ∀ i:ℕ,j+1 ≤ i→ i ≤ N→ Stamp (N:=N) P (C.localSection d) (E i) ((C.factory d N p).entries i ((C.factory d N p).terminal.symm v)) (L.X i):=by
    let w:=purse (2*a) (near C.path.levels) (j+1); have ha:= mul_pos (show 0<(2:ℝ) from by norm_num) hv
    obtain ⟨X,hX,hB,hS,c,hc,h'⟩:=harvest h A.buy.system hN hm ha hW hz fun x i hi he => hx i hi he x -- hv lemma
    obtain ⟨Q,hQ,hQ'⟩:= Line.roll_below A P h hk hK hN ⟨fun i hk hi=> he.mare i hk (hi.trans_le hN)⟩ c (hX.marks (j+1) le_rfl hN) ((congr_fun (hX.steers (j+1) le_rfl hN) P.v) ▸ h') (le_trans (mul_le_mul_of_nonneg_right (by linarith only [hv]) (norm_nonneg _)) hc) hv (hX.steers _ le_rfl hN|>.symm) hZ (b:=b)
    let σ:Line A P N p (j+1) N b E o:=⟨X,w,hX,Creep.purse_stay C (2*a) ha hb⟩
    let v':=σ.damp (1/2:ℝ) (by norm_num) (by norm_num); have heq: Q.w (j+1)=v'.w (j+1):=by
       rw [hQ',Run.below_main]; change a=(1/2:ℝ)*purse (2*a) _ (j+1) (j+1); unfold purse; rw [marines _ _ _ (fun _=>ha)]; ring
    obtain ⟨L,hL,hU⟩:=Line.continueW Q v' hQ heq
    refine ⟨L,((hL k hK).1).trans (congr_fun hQ' _),?_,fun i hi ht=> ((hU i hi).2).trans (show _=X i from rfl) ▸ hS i hi ht⟩
    rw [(hU N hN).1,(hU N hN).2]; obtain ⟨B,t,hh,he'⟩:= hB.patent; refine ⟨v'.hold.fees N hN le_rfl,hB.mark, ⟨B,t,hh,?_,he'.2⟩,hB.writes⟩
    by_cases ht:0 ≤ t; · exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hB.pos.le) (by norm_num : (1/2:ℝ)≤ 1)) ht).trans he'.1
    refine le_trans (mul_nonpos_of_nonneg_of_nonpos (v'.hold.fees N hN le_rfl|>.le) (le_of_not_ge ht)) ?_; change 0 ≤ (Real.sqrt _)⁻¹/4; positivity
end YM.OPE.Allot
