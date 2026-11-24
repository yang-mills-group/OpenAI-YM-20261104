import YM.RegulatorIR.Oracle.Royal

/-! Exponential post costs uniform for permitted intervals. Important: does
not price a denominator for the Mark condition. Polynomial-spatial port. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge} {X Y A B : Type} {α σ σ' Ω Ω' δ δ' l s:ℝ} {q:ℕ} {n t:Side}
-- portfolio budgets on Φ and A_tr BOTH directions
variable (P: Patch)(K:KernelChoices)(G:Gauge)(B:Precision.Bed)(R:Cross P.L (TypeFace 1) (TypeFace 1))
local notation "Kp"=> blockQ G P.L
local notation "Tc"=> linksQ G
local notation "Gd"=> gardens P G

def rootCost(v:ℝ) := (moneyU P K (G:=G) v).choose
def downCost (v:ℝ) := (funded P G v).choose
def wareV (σ Ω:ℝ):ℝ≥0∞:= (Fintype.card (Co P.L (PAC G 1)):ℝ≥0∞)+Fintype.card (PAC G 1)+‖σ‖ₑ+ ENNReal.ofReal (abs (lesser Ω P.L)) -- remove
-- post exact.Broader redundant $L^4$ etc.
def brick (Ω:ℝ):ℝ≥0∞:= ((Fintype.card (Co P.L (PAC G 1)):ℝ≥0∞)+Fintype.card (PAC G 1))* ENNReal.ofReal (lesser Ω P.L)
def tide (Ω v:ℝ):=rootCost P K G v*brick P G Ω
lemma blue_d (Ω v:ℝ):tide P K G Ω v≠⊤:= ENNReal.mul_ne_top (moneyU P K (G:=G) v).choose_spec.1 (by unfold brick;finiteness)
variable (Hp:R.strip σ (lesser Ω P.L))(hh:0≤Ω)(ht:0<σ)
include Hp hh
lemma saves : chestE Kp Tc σ (ruling P G R) (brick P G Ω) ∧ chestE Tc Kp σ (Function.swap (ruling P G R)) (brick P G Ω):=by
 let V:= adult P R G
 have hD:V.strip σ (lesser Ω P.L):=adult_price G P R Hp (div_nonneg hh (by positivity : 0 ≤ (P.L.val:ℝ)))
 refine ⟨(roots Kp Tc hD).toll (by unfold brick;exact mul_le_mul_left le_add_self _),?_⟩; rw [ruling,← lading_rev]; exact (roots Tc Kp (Work.F08.strip_trans hD)).toll (mul_le_mul_left le_self_add _)
include ht
lemma buoys : chestE Gd Tc σ (phiQ P K R G) (tide P K G Ω σ) ∧ chestE Tc Gd σ (Function.swap (phiQ P K R G)) (tide P K G Ω σ):=by
 obtain ⟨hx,hz⟩:=saves P G R Hp hh
 obtain ⟨hp,h⟩:= (moneyU P K (G:=G) σ).choose_spec.2; refine ⟨hp.lapB hx ht.le,?_⟩; rw [phiQ,lap_flip]; apply (hz.lapB h ht.le).toll; unfold tide; rw [mul_comm];exact le_rfl

def shellC (Ω σ:ℝ):ℝ≥0∞:= brick P G Ω + downCost P G σ * tide P K G Ω σ
omit Hp hh ht in
lemma shellC_f : shellC P K G Ω σ≠⊤:=by unfold shellC;exact ENNReal.add_ne_top.mpr ⟨by unfold brick;finiteness, ENNReal.mul_ne_top (funded P G σ).choose_spec.1 (blue_d _ _ _ _ _)⟩
lemma coins : chestE Kp Tc σ (projectionQ P K R G) (shellC P K G Ω σ) ∧ chestE Tc Kp σ (Function.swap (projectionQ P K R G)) (shellC P K G Ω σ):=by
 obtain ⟨hx,hz⟩:=saves P G R Hp hh; obtain ⟨h,hp⟩:= buoys P K G R Hp hh ht
 have hg : chestE Kp Gd σ (finer (career G)) (downCost P G σ):= (funded P G σ).choose_spec.2.1
 have hy: chestE Gd Kp σ (Function.swap (finer (career G))) (downCost P G σ):=(funded P G σ).choose_spec.2.2
 rw [projectionQ,gained];constructor
 · unfold shellC; exact hx.add (hg.lapB h ht.le)
 rw [show ∀ {M U:Layer (Long G.ColorIndex) (Long G.ColorIndex)},Function.swap (M+U)=Function.swap M+Function.swap U from (fun {M U}=>rfl), lap_flip]
 rw [shellC,mul_comm (downCost P G σ)] -- fix
 exact hz.add (hp.lapB hy ht.le)
variable (hv:0<l)(he:s=l*P.L.val)(hx:0<s)
include hv he
-- physical counts $(s,s)$ and $(l,s)$.
def tariffJ (Ω σ:ℝ)(k:ℕ) := tide P K G Ω σ * ENNReal.ofReal (scar σ k)
omit Hp ht hh hv he in
lemma tariffJ_f q: tariffJ P K G Ω σ q≠⊤:= ENNReal.mul_ne_top (blue_d _ _ _ _ _) ENNReal.ofReal_ne_top
lemma turns_row : Layer.row (conveyer P K G R) (Tariff.native s hx q) (Gain.pointS l) (fm G s) (tariffJ P K G Ω σ q):=by
 let Y:=Tariff.native s hx q;let f:=phiQ P K R G
 have hp:Layer.row f Y (Gain.pointS l) (fm G s) _:= payUp hx _ (scars σ q ht).2 (costsC P hv he) (costsG hx) (buoys P K G R Hp hh ht).1
 have hh:= row_smult (N:=f+surge G f) (row_plus hp (coil_P G P f hv he hx _ hp)) (1/2:ℝ)
 rw [half_enn] at hh;exact hh

def post_C (Ω σ:ℝ)(q:ℕ):= shellC P K G Ω σ*ENNReal.ofReal (scar σ q)
lemma tilts : Layer.row (projectionQ P K R G) (Tariff.native s hx q) (fm G l) (fm G s) (post_C P K G Ω σ q)∧Layer.row (Function.swap (projectionQ P K R G)) (Tariff.native s hx q) (fm G s) (fm G l) (post_C P K G Ω σ q):=by
 let c:=scar σ q; have hc:= (scars σ q ht).2;obtain ⟨hv',hv''⟩:= coins P K G R Hp hh ht; exact ⟨payUp hx c hc (costsB hv he) (costsG hx) hv', payUp hx c hc (costsG hx) (costsB hv he) hv''⟩
omit Hp ht hh hv he in
lemma post_f q: post_C P K G Ω σ q ≠⊤:= ENNReal.mul_ne_top (shellC_f P K G) ENNReal.ofReal_ne_top
variable {S:Clip}(Z: Hall B σ Ω α S)(H:P.Branches K G)
include Z H --replace
omit Hp hh ht

def heatPost (Ω σ α:ℝ)(q:ℕ):= markup P K G σ Ω α * ENNReal.ofReal (scar (Oracle.widthK P K G σ Ω α) q)
omit hv he Z H in
lemma heat_fin q: heatPost P K G Ω σ α q≠⊤:= ENNReal.mul_ne_top (billingC _ _ _ _ _ _) ENNReal.ofReal_ne_top
lemma reels : Layer.row (hearth P K G B Z H) (Tariff.native s hx q) (fm G l) (fm G l) (heatPost P K G Ω σ α q):= payUp hx _ (scars _ q (width_pos P K G B Z)).2 (costsB hv he) (costsB hv he) (powersV P K G B Z H)
end YM.RegulatorIR.Oracle
