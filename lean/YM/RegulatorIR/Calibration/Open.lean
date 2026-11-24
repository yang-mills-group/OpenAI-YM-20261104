import YM.RegulatorIR.Calibration.Aloft

/-!
# Affine increments on Rank 2 transport

We cannot assume T converges in order to estimate/construct the clocks
needed by T. Use *one coefficient* valuation transport; applies at any
prior readings. Time steps free of composition radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X: Type} {e r u:ℕ}
section
variable {W:Packet (Geometry.Long X) (r+1)}{F:ℝ≥0∞} {l:ℝ}
lemma paid_to(h:0<l)(H:localQ (Momentum.path h X u) W F): Held W u (((1+r*5:ℝ≥0∞)^u)*F):=by
 intro x; let P:= Momentum.path h X u
 apply le_trans _ (mul_le_mul_right (H 0 x) ((1+r*5:ℝ≥0∞)^u)); unfold Stalk.scopeQ quota; change _ ≤ _ * (∑' v: Hold (0:Fin (r+1)) x, ‖W v.val‖ₑ*(P.diameter v.val)); rw [← (holding0 x r).tsum_eq,← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro z;
 apply le_trans (mul_le_mul_right (living z x h) _); rw [mul_left_comm];exact le_rfl
end
section Circuit
variable {R:Type} {M:R→ℕ}{n:Page M→Side} (S:Circuit M n){K:KernelChoices}(Y:Program K) (G:Gauge)(Z:∀ P:Patch,P.Branches K G) (s:Page M→ Scale)
local notation "Q"=> S.payroll Y G Z
local notation "Tr"=> S.lane Y G Z
local notation "H₁"=> S.scroll_j Y G
local notation "T₁"=> S.devices Y G Z
variable (f:Flap M)
lemma joint_h (i: Flap M) : Vacuum ((T₁ s i).jVac ((Q s).bulk i.prev)):= ((S.dialect Y G Z s).frames i).joint_vac_shape ((Q s).cap_b (Halo.essential (Tr s)) _) (Halo.essential (Tr s) i)
lemma flits : Billed (T₁ s f).driftL∧ Billed (Function.swap (S.sails Y G f)) := ⟨billed_supp (F:= (T₁ s f).driftL) (q:=(S.dialect Y G Z s|>.ceilingRoom.cone 0 f)) (clockpost _ _ _ _ _ _ _|>.1) (ENNReal.add_ne_top.mpr ⟨panes_p S Y G f 0,by finiteness⟩), billed_supp (x:=fm G (S.l f.next)) (y:=fm G (S.l f.prev)) (q:= Tariff.native _ (S.l_p f.next) 0) (chargeP S Y G _ _|>.2) (panes_p S Y G f 0)⟩
include Z
lemma top_K (w:R) : many (beginF G) 2 2=coil (H₁ (Page.opening M w)):=by
 let i:= Page.opening M w;let p: Page M→Scale:= fun _=>Clocks.flat; obtain ⟨h,hv,hc⟩:= con S Y G Z p i; change Layer.Sym _ _ (H₁ i) at h; change Billed (H₁ i) at hc; rw [show H₁ i=finer moon from S.crust_top _ _ _] at h hc; rw [S.crust_top]; exact launched (S.dual i) (S.comet i) h (S.l_p i) hc (S.stands _)
lemma cost_token (j:Page M) (e:ℕ): Pupil.costM ((Q s).bulk j e 2):=by -- namespace
 obtain ⟨c,hc,H⟩:= kernel_b S Y G Z s 3 j e 2; let C:= ((1+ (↑(1:ℕ):ℝ≥0∞)*5)^3)* c
 apply Rules.star_paid (show C≠⊤ from ENNReal.mul_ne_top (by finiteness) hc) (le_refl 3); exact paid_to (S.l_p j) H
lemma warmedUp (w:R) (e:ℕ) (h:0<e) : (Q s).bulk (Page.opening M w) e 2= biases (s (Page.opening M w)) e • coil (H₁ (Page.opening M w)):=by
 rw [← top_K S Y G Z]; have he:= primary_high _ (Circuit.serene G s w) h (le_refl 2) (by omega);
 exact (he.trans (by rw [Nat.add_sub_cancel] )) -- arg s extra? dot
lemma fenestra (w:R) {t:Page M→Scale}(H:Squares e (tale (s (Page.opening M w)).beta) (tale (t (Page.opening M w)).beta)) : Matches e ((Q s).bulk (Page.opening M w)) ((Q t).bulk (Page.opening M w)):=by
 intro i hi; ext1 r;ext1 p; change (∑' j,Circuit.mural G s w j i r p)= ∑' j,Circuit.mural G t w j i r p; apply tsum_congr; intro j; exact congr_fun (congr_fun (stageM (Circuit.serene G s w j) (Circuit.serene G t w j) (fun p=>plain_agree _ _ H p j) i hi) r) p
lemma add_k (i:Flap M) (e:ℕ) (h:0<e): (T₁ s i).addon e = Warm.mainL K (S.pactP i) G (Z _) e+∑ k∈ Finset.antidiagonal e,biases (s i.prev) k.1 • Warm.mainR K (S.pactP i) G (Z _) (k.2+2):= fullK K _ _ (Z _) (T:= S.rail K i) rfl rfl (S.wheeled G Z s i) e h
lemma slims (i:Flap M) {t:Page M→Scale} (h: Squares e (tale (s i.prev).beta) (tale (t i.prev).beta)): GridM (T₁ s i) (T₁ t i) e:=by
 refine ⟨rfl,rfl,fun j hj=>?_⟩;by_cases hp:0<j
 · rw [add_k _ _ _ _ _ _ _ hp, add_k _ _ _ _ _ _ _ hp]; apply congr_arg; apply sum_congr rfl;intro p ht;rw [show biases (s i.prev) p.1=biases (t i.prev) p.1 from h p.1 (by have he:= mem_antidiagonal.mp ht;omega)]
 have hv:j=0:=by omega
 subst j; rw [vacuum_lo _ (show Vacuum (T₁ s i).addon from Halo.essential (Tr s) i),vacuum_lo _ (show Vacuum (T₁ t i).addon from Halo.essential (Tr t) i)]
lemma winding (w:Flap M){t:Page M→Scale}(h: Squares e (tale (s w.prev).beta) (tale (t w.prev).beta))(H:Matches e ((Q s).bulk w.prev) ((Q t).bulk w.prev)):Matches e ((Q s).bulk w.next) ((Q t).bulk w.next):=by
 rw [← (Q s).step_v,← (Q t).step_v]; exact (slims _ _ _ _ _ _ h).log_step H
end Circuit
end YM.RegulatorIR.Calibration
