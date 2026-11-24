import YM.Frontier6.Pair.Witness

set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Extraction.Lease Cells Extraction.Around OS Word MeasureTheory
open Platform Next.Extract Dash PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order} (h:PairProducer C)(hW:Extraction.Wcmain C)(hG:G.Simple)
set_option quotPrecheck false
local notation "R"=> fuga C.path.levels
omit hW
include h hG
lemma fugaPitch : Note C.S (R) (-1):=by
   obtain ⟨W,r,A,h₁,h₂,h₃⟩:= h.launches; exact fuchsia C hG h₃
variable {S T:Table C.book}{M:ℕ→Table C.book}{P:Bin T}{Y:DiffPlan S} (H:Base C F T M P S Y) (K:Final C F S) {D d t k:ℕ}
variable {s:ℝ}{j:ℕ→ℕ}
include H K hW
lemma grid_output {η:ℝ} (hg:η+(((d:ℝ)+(t:ℝ))*s+8*(s-1)) < 1/8+(d:ℝ)+(t:ℝ)) (hk:C.ref D ≤ k) (hj:∀ᶠ i in atTop,i+1 < j i) (hs:Tendsto j atTop atTop) (hr:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 s)) (v:C.label d) (u:C.label t) :
   ∃ a b : ℕ→ℝ, Note C.S a ((d:ℝ)+(t:ℝ)-(D:ℝ)-η) ∧ Note C.S b (- (D:ℝ)+(((d:ℝ)+(t:ℝ))*s+8*(s-1))) ∧ ∀ᶠ m in atTop, ∀ x:Lattice.Cover, R (m+1)/16 ≤ ‖C.S.gridPoint (j m) x‖ → ‖C.S.gridPoint (j m) x‖ ≤ 4* R m →
      ∃ z:C.label D,Priced F k (j m) x v u z (a m) ∧ ReferenceFit K z m (b m):=by
   obtain ⟨W,r,A,h₁,h₂,h₃⟩:= h.launches; let L:= C.path.levels; let p:= Stock.Tabs.chosen L 1 h.stops k; have hp:=Stock.Tabs.opened L 1 h.stops k; let c:= Accent.stakes C k p
   have hP:0 < c:=Real.exp_pos _; let x m:= exteriorReserve C m d t D η; let a m:= 3*(c/x m)
   let U:= max 1 ((C.labels.level t).coeffSize u); let V:= max 1 ((C.labels.level d).coeffSize v); have hv:0<V:=zero_lt_one.trans_le (le_max_left ..); have hu:0<U:=zero_lt_one.trans_le (le_max_left ..)
   let b m:=2*pairQuota C (j m) m d t D V U
   have he:Note C.S x ((D:ℝ)-(d:ℝ)-(t:ℝ)+η):= Note.bell_exp C.S _
   refine ⟨a,b,((Note.notes C.S 3 (by norm_num)).mills ((Note.notes C.S c hP).splits he)).swapP (by ring), ((Note.notes C.S 2 two_pos).mills (quotaPitch (d:=d) (D':=t) C hG hr hs h.stops (b:=V) (a:=U) hv hu)).swapP (zero_add _),?_⟩
   filter_upwards [captures_all C k p d t D v u F H.family h.frame h₁ V U h₃ hG h.stops hv hu (le_max_right ..) (le_max_right ..) hp (hk.trans hp.1) hr hs hj hg,eventually_ge_atTop k] with m hY hx y hl hp
   exact cashier (p:=0) H K h hG hW v u y hk hx hl hp hY (mul_lt_mul_of_pos_right (by norm_num) (div_pos hP (he.pos m))) -- param p unused has m? need check
end YM.Frontier6.Canvas
