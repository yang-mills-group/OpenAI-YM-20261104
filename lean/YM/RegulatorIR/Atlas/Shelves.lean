import YM.RegulatorIR.Venture.Pap
import YM.RegulatorIR.Oracle.Choice

/-!
# Authorizations for the auxiliary (bulk & orbit comparison) vacuum policy

Gains are charged **in advance** before lengths are chosen. Damping strengthens
both the bulk and orbit-comparison demands. Polynomial sheet costs incl analytic
choices are issued *after* choosing lengths, but before choosing the depth of a
comparison/IR continuation! `SatisfiesQ` uses no history estimates on vertices
or observables.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Atlas
open Function Filter Finset Budget Uniform
open Lattice RG Gauge Prim Binding Epoch Epoch.League Geometry Step Taping Precision Oracle Venture Laurent Bloch Halo Profiles Calibration Momentum
open YM.RegulatorIR.Ledger
open scoped ENNReal NNReal Topology BigOperators Classical
variable {X: Type}{M:X→ℕ}{n:Page M→Side}{K:KernelChoices}{k p u r:ℕ}{γ:ℝ}{L:ℝ≥0∞}
variable (G:Gauge) (R:Program K)
def shirt (u j:ℕ) : ℝ≥0∞:= kernel_cap G u (R.receipt.α j) (R.receipt.Ω j)
def rent (u j:ℕ) : ℝ≥0∞:= pack_c G u (R.receipt.α j) (R.receipt.Ω j)
def careful (u r j b:ℕ):ℝ≥0∞:= fore_c G.ColorIndex r u (5-(r+1)) (rent G R u j)*(1+shirt G R u b)
def catalogue (p u j:ℕ) : ℝ≥0∞:= ∑ b ∈ Finset.range (j+1), ∑ r∈ Finset.range (p+3), careful G R u r j b
lemma owns p u j: catalogue G R p u j≠⊤:=by
 apply ENNReal.sum_ne_top.mpr;intro i _;apply ENNReal.sum_ne_top.mpr;intro r _;exact ENNReal.mul_ne_top (fore_c_f (pack_c_f G _ _ _)) (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, assured u _ _⟩)
-- L geometric power version avoiding toll rounding
lemma advances (C:ℝ≥0∞)(h:C≠⊤)(ht:γ<1):∃ s:ℕ, ∀ L:Side,s ≤ L.val → C*Momentum.award L.val ≤ ENNReal.ofReal (Real.exp (Real.log (L.val:ℝ)*-γ)):=by
 let V:=C.toReal
 have hp : Tendsto (fun t:ℕ=> (t:ℝ)^(1-γ)) atTop atTop:= (tendsto_rpow_atTop (sub_pos.mpr ht)).comp tendsto_natCast_atTop_atTop
 obtain ⟨s,he⟩:= eventually_atTop.1 (hp.eventually (eventually_ge_atTop V)); refine ⟨s,fun L hk=>?_⟩
 let x:ℝ:=L.val; have hx:0<x:=by unfold x; positivity
 have hV: V*x⁻¹≤ Real.exp (Real.log x * -γ) := by
    rw [← Real.rpow_def_of_pos hx, Real.rpow_neg hx.le, ← div_eq_mul_inv, div_le_iff₀ hx, mul_comm, ←div_eq_mul_inv]; exact (show V≤ x^(1-γ) from he _ hk).trans_eq (by rw [Real.rpow_sub hx, Real.rpow_one])
 have hy : Momentum.award L.val=ENNReal.ofReal x⁻¹:=by rw [ENNReal.ofReal_inv_of_pos hx]; unfold x Momentum.award; rw [ENNReal.ofReal_natCast]
 rw [hy]; exact (ENNReal.ofReal_le_ofReal hV).trans' (by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h])
-- pre threshold for each demanded moment (u) and rank p. For many pairs take a max. kernel+shell similar ratios

def orders (p u j:ℕ)(γ:ℝ)(H:0<γ)(he:γ<1):ℕ:= R.floor_q G u γ H he j+(advances (catalogue G R p u j) (owns G R p u j) he).choose
variable (S:Circuit M n)
variable (Z:∀ Q: Patch, Q.Branches K G)
-- post-computable prices independent histories (except stages); sweep at Ky-age.
-- gamma positivity fixed global. station/credit Peg captures alignment ref unit.

def glowPage (u j:ℕ):= shirt G R u j+ ENNReal.ofReal (R.receipt.η j)⁻¹
-- includes Smooth analytic prices. J in Patch fixed.
def readinessF (i b u:ℕ)(P:Patch):ℝ≥0∞:= (Warm.disksL K P G (Z _) i b u + Warm.disksR K P G (Z _) i b u)+Oracle.archive P K G (Z _) i b u
lemma ready_f (P:Patch){i j:ℕ}: readinessF G Z i j k P≠⊤:= ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨(Warm.disk_f K P G (Z _) _ _ _).2,(Warm.disk_f K P G (Z _) _ _ _).1⟩, archived _ _ _ _ _ _ _⟩
def lumens (u:ℕ)(P:Patch): ℝ≥0∞:= let j:=P.J; ((rent G R u j + Oracle.brick P G (R.receipt.Ω j)*ENNReal.ofReal (scar (R.receipt.α j) u))+Oracle.tariffJ P K G (R.receipt.Ω j) (R.receipt.α j) u)+ (Oracle.heatPost P K G (R.receipt.Ω j) (R.receipt.α j) (R.receipt.η j) u+Oracle.post_C P K G (R.receipt.Ω j) (R.receipt.α j) u)
def glowF (p u:ℕ)(P:Patch):ℝ≥0∞:= lumens G R u P + ∑ i∈Finset.range (p+3), ∑ j∈ Finset.range (p+3), readinessF G Z i j u P
lemma gpage_f j:glowPage G R u j≠⊤:= ENNReal.add_ne_top.mpr ⟨assured _ _ _,ENNReal.ofReal_ne_top⟩
lemma lumes_f P:lumens G R u P≠⊤:= ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨pack_c_f G _ _ _,ENNReal.mul_ne_top (by unfold brick;finiteness) ENNReal.ofReal_ne_top⟩, tariffJ_f _ _ _ _⟩, ENNReal.add_ne_top.mpr ⟨heat_fin _ _ _ _, post_f _ _ _ _⟩⟩
lemma gf_f P:glowF G R Z p u P≠⊤:= ENNReal.add_ne_top.mpr ⟨lumes_f _ _ _, ENNReal.sum_ne_top.mpr fun _ _=> ENNReal.sum_ne_top.mpr fun _ _=>ready_f G Z P⟩

structure SatisfiesQ (B: Marked M)(p u:ℕ)(γ:ℝ):Prop where
 shapeS i:B.gap i= (S.sizeL i).val
 capital : B.Structural
 depth : 3 ≤ u
 width : p+2≤u
 paid : Poly B.age_f (glowF G R Z p u ∘ S.pactP)
 accountP : Poly B.age_t (glowPage G R u ∘ S.J)
 θ_pos : 0 < γ
 θ_low : γ < 1
 smooths i:5 ≤ S.J (Flap.prev i) -- need infer
 intake (i:Flap M) : orders G R p u (S.J i.prev) γ θ_pos θ_low≤ (S.sizeL i).val

variable {B:Marked M} (H:SatisfiesQ G R S Z B p u γ)
include H
lemma hPre : ∀ i:Flap M, R.floor_q G u γ H.θ_pos H.θ_low (S.J i.prev)≤ (S.sizeL i).val:= fun i=> le_trans (Nat.le_add_right ..) (H.intake i)
lemma leadS i : Circuit.leadA S R G u i ≤ ENNReal.ofReal ((((S.sizeL i).val:ℝ)^γ)⁻¹):= R.insists G _ _ _ _ S (hPre G R S Z H) i
lemma underhood (r:ℕ)(h: r < p+3) (w: Flap M): t_budget S R G u r w*(1+shareP G S u R w.next)≤ B.coin (-γ) w:=by
 let l:= S.J w.prev; let c:= S.sizeL w; let q:= catalogue G R p u l
 let i:= S.J w.next; have hp : careful G R u r l i≤ q:= le_trans (Finset.single_le_sum (s:=Finset.range (p+3)) (f:=fun r=> careful G R u r l i) (fun _ _=> zero_le) (Finset.mem_range.mpr h)) (Finset.single_le_sum (s:=Finset.range (l+1)) (f:=fun b=> ∑ r∈Finset.range (p+3),careful G R u r l b) (fun _ _=>zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le (S.shakes w))))
 refine le_trans ?_ (le_trans (mul_le_mul_left hp (Momentum.award c.val)) ?_)
 · unfold t_budget beginsP shareP careful rent shirt; apply le_of_eq; ac_rfl
 unfold Marked.coin Marked.slope; rw [H.shapeS]; exact (advances q (owns G R p u l) H.θ_low).choose_spec c (le_trans (Nat.le_add_left ..) (H.intake w))
lemma scripts_v : Scripted S R G Z p u B γ:=by
 have hV: Poly B.age_f (lumens G R u ∘ S.pactP) := H.paid.mono fun _=> le_self_add
 have hx(i j)(hp:i≤p+2)(he:j≤p+2): Poly B.age_f (readinessF G Z i j u ∘ S.pactP):= H.paid.mono fun x=>?_ -- split
 swap
 · let f:= S.pactP x; exact le_trans (Finset.single_le_sum (s:=Finset.range (p+3)) (f:=fun j=> readinessF G Z i j u f) (fun _ _=>zero_le) (Finset.mem_range.mpr (by omega))) ((Finset.single_le_sum (s:=Finset.range (p+3)) (f:=fun i=> ∑ j∈Finset.range (p+3),readinessF G Z i j u f) (fun _ _=>zero_le) (Finset.mem_range.mpr (by omega))).trans le_add_self)
 refine ⟨⟨H.shapeS,H.capital,H.depth,fun w=>by have ht:=H.smooths w;omega,H.accountP.mono fun _=>le_self_add,fun i=>?_⟩,⟨hV.mono fun _=> le_self_add.trans le_add_self,hV.mono fun _=> le_add_self.trans le_add_self⟩, H.width,hV.mono fun _=> le_self_add.trans (le_self_add.trans le_self_add), hV.mono fun _=> le_add_self.trans (le_self_add.trans le_self_add), hV.mono fun _=> le_add_self.trans le_self_add, fun i j hp he=>(hx i j hp he).mono fun _=> le_self_add.trans le_self_add,fun i j hp he=>(hx i j hp he).mono fun _=> le_add_self.trans le_self_add, fun r _ hb=>underhood G R S Z H r (by omega)⟩
 let X:= t_budget S R G u 1 i; exact (le_mul_of_one_le_right (a:=X) bot_le (b:=1+shareP G S u R i.next) le_self_add).trans (underhood G R S Z H _ (by omega) i)
lemma wall_pay (i j) (h:i≤p)(ht:j ≤ i + 2): Poly B.age_f (fun w=> archive (S.pactP w) K G (Z _) i j u):=by
 apply H.paid.mono; intro x; let f:= S.pactP x; apply le_trans (b:=readinessF G Z i j u f) le_add_self; exact le_trans (Finset.single_le_sum (s:=Finset.range (p+3)) (f:=fun j=> readinessF G Z i j u f) (fun _ _=>zero_le) (Finset.mem_range.mpr (by omega))) ((Finset.single_le_sum (s:=Finset.range (p+3)) (f:=fun i=> ∑ j∈Finset.range (p+3),readinessF G Z i j u f) (fun _ _=>zero_le) (Finset.mem_range.mpr (by omega))).trans le_add_self)
end YM.RegulatorIR.Atlas
