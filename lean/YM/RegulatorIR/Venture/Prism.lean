import YM.RegulatorIR.Venture.Offspring

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
variable {X:Type}{W:X→Type}{e p r:ℕ}
section Static
variable {G:Gauge}
lemma comparison_token (V B:Orders (Foot G))(h:W1 V p)(hv: W1 B p): W1 (V-B) p:=by
 have he(δ : Foot G→PowerSeries ℝ)(hp:(Function.support δ).Finite)(i:ℕ): rhymeR δ (V-B) 2 i=rhymeR δ V 2 i-rhymeR δ B 2 i:=by
    unfold rhymeR;simp_rw [← sum_sub_distrib]; apply sum_congr rfl;intro j _;apply sum_congr rfl;intro t _
    unfold rhyme; rw [← (pledge (V j.1 t) (k:=j.2) hp).tsum_sub (pledge (B j.1 t) (k:=j.2) hp)];exact tsum_congr fun x=>sub_mul ..
 have hh(A:BEdge G)(H:(Function.support A).Finite): (Function.support (vow (fun _=> hue A))).Finite:= (hue_finite H).subset fun i hi hh=> hi (by change tale (fun _=>hue A i)=0;rw [show hue A i=0 from hh];exact (tale_const _).trans (map_zero _))
 exact ⟨fun x σ hx hp i hi=> by rw [he _ (pledgeR hx hp),he _ (hh x hx), h.grade _ _ hx hp _ hi,hv.grade _ _ hx hp _ hi],fun x hx b i hi=> by rw [he _ (hh _ (gives_beast hx)),he _ (hh x hx), h.signed x hx b _ hi,hv.signed x hx b _ hi],fun x hx b i hi=> by rw [he _ (hh _ (gives_vbadge hx)),he _ (hh x hx), h.adjoints x hx b _ hi,hv.adjoints x hx b _ hi]⟩
lemma subtracts {T V:Packet X r}(h:Limits T)(hv:Limits V): Limits (T-V):=by rw [sub_eq_add_neg, ← neg_one_smul ℝ]; exact add_l h (tilt_l hv _)
lemma scaled_p {K:Packet (Long X) (r+1)}{c:ℝ≥0∞}{u:ℕ}(h:Held K u c)(v:ℝ): Held (v • K) u (‖v‖ₑ*c):=by intro x; exact (quota_times (Momentum.anchored x K) (wall (Momentum.area x) 1 u) v).trans_le (mul_le_mul_right (h x) _)
lemma neg_s {T V:Packet X r}(h:IsSym T)(hp:IsSym V):IsSym (T-V):=by rw [sub_eq_add_neg,←neg_one_smul ℝ]; exact symmetric_add h (symmetric_scale hp _)
lemma neg_r {V W:Orders X}(h:Ranks e V)(hp:Ranks e W):Ranks e (V-W):=by
 intro i j hj; by_contra! hx; apply hj;rw [Pi.sub_apply,Pi.sub_apply,show V i j= (0:Packet _ _) from Classical.not_not.mp (fun he=>by have := h i j he;omega), show W i j=0 from Classical.not_not.mp (fun he=>by have :=hp i j he;omega),sub_self]
end Static
section environment
variable {M:X→ℕ}{n:Page M→Side} (S:Circuit M n){K:KernelChoices}(V:Program K) (G:Gauge)(Z:∀ P:Patch,P.Branches K G)
variable (s:Page M→Scale) (i:Page M)
local notation "Q"=> S.payroll V G Z s
local notation "U"=> S.scroll_j V G
-- audited vacuum on Cover

def fullV : Orders (Foot G):= dyeX (S.scroll_j V G i) ((Q).bulk i)
local notation "T"=>fullV S V G Z s
lemma stem_h (i) : Vacuum ((Q).bulk i):= (Q).cap_b (Halo.essential (S.lane V G Z s)) _ -- s implicit
lemma grammar (i) :Ranks 2 (T i):= by
 intro e r he; unfold fullV dyeX at he; split at he
 next h=> omega
 split at he; contradiction; exact (stem_h _ _ _ _ _ _ _ _ he).2
lemma badge (p:Page M)(k:ℕ): W1 (T p) k:= illumination S V G Z s p k
lemma V_l (i:Page M) (e r): Limits (T i e r):=by
 unfold fullV dyeX; split
 next h=> have hr := h.2
          subst r;exact coil_bound (Stage.con S V G Z s i|>.2.2) -- dep rw?
 split
 next h=> refine ⟨0,by finiteness,fun v=>?_⟩; rw [Pi.zero_apply,enorm_zero]
 next h=> obtain ⟨c,h,H⟩:= kernel_b S V G Z s 0 i e r; exact bounds_from H h
lemma V_s (i:Page M) : gradedSymmetric (T i):=by
 intro e r; unfold fullV dyeX;split
 next h=> have hr:=h.2
          subst r; exact coil_s _ (Stage.con S V G Z s i|>.2.1)
 split;exact symmetric_zero; exact symmetricV _ _ _ _ _ i e r
lemma V_p (p:Page M)(h:0<e)(he:0<r): T p e r=(Q).bulk p e r:=by unfold fullV dyeX;rw [dif_neg (by omega),if_neg (by omega)]
lemma V_i (i: Page M): T i 0 2=coil (U i):=by unfold fullV dyeX;rw [dif_pos ⟨rfl,rfl⟩]
lemma V_zero (p:Page M): T p e 0=0:= by unfold fullV dyeX; rw [dif_neg (by omega),if_pos rfl]
lemma V_at (p:Page M) (h:r≠2):T p 0 r=0:=by
 unfold fullV dyeX; rw [dif_neg (by omega),vacuum_lo _ (stem_h S V G Z s p)];split<;> rfl
lemma stated_s (p)(e:ℕ)(hs:G.Simple): (Q).bulk p e 1=0:=by
 by_cases he:0<e
 · rw [← V_p _ _ _ _ _ _ he (by decide)];exact WOne.removed_one (badge _ _ _ _ _ _ _) le_rfl hs
 rw [show e=0 by omega, vacuum_lo _ (stem_h _ _ _ _ _ p)];rfl
-- valuation depending solely earlier.T Clock. alphabetical
lemma current_coat (p:Page M) (u:ℕ) : Held (coil (U p)) u (League.shareP G S u V p):=by
 let K₁:= U p; have ht:coil (U p)=( -(1/2):ℝ) • (Momentum.lamp K₁):=by ext1 i; exact (by rw [Axial.coil,Pi.smul_apply,neg_div];rfl)
 rw [ht]; intro x; let X:=(League.shareP G S u V p)
 have hx:Held (Momentum.lamp K₁) u X:= Epoch.current_read G (S.honored V p).card
 apply (scaled_p hx (-(1/2):ℝ) x).trans; apply (mul_le_mul_left _ X).trans_eq (one_mul _); rw [← ofReal_norm]; exact (ENNReal.ofReal_le_ofReal (show ‖(-(1/2):ℝ)‖≤ 1 by norm_num)).trans_eq ENNReal.ofReal_one
lemma full_r (p:Page M): Pupil.costM (coil (U p)):=by -- remove c
 let h:= current_coat S V G p 3; exact Rules.star_paid (show League.shareP G S 3 V p≠⊤ from assured 3 _ _) (le_refl _) h -- fix
end environment
end YM.RegulatorIR.Venture
