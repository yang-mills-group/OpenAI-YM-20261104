import YM.RegulatorIR.Oracle.Position

/-! Prepurchase numerical dependencies of slots. Lag radius B registered.
Independent of number of periods. Use adjusted analytic σ exactly. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge} {X Y A B : Type} {N M:Layer X Y} {α σ σ' Ω Ω' δ δ' r l s:ℝ} {q:ℕ} {n t: Side}
lemma row_plus {u p:ℝ≥0∞}{x:X→B}{y:Y→B}{F:Tariff B}(h:Layer.row N F x y u)(he:Layer.row M F x y p): Layer.row (N+M) F x y (u+p):=fun i=> (quota_add (N i) (M i) _).trans (add_le_add (h i) (he i))
lemma row_smult {u:ℝ≥0∞}{x:X→ B}{y:Y→B}{F:Tariff B}(h:Layer.row N F x y u)(c:ℝ): Layer.row (c • N) F x y (‖c‖ₑ*u):=fun i=>(quota_times (N i) _ c).trans_le (mul_le_mul_right (h i) _)
lemma row_rep {u:ℝ≥0∞}{x:X→B}{y:Y→B}{F:Tariff B}(h:Layer.row N F x y u)(Q: Equiv.Perm X)(S: Equiv.Perm Y)(he:∀ a b,F.road (x a) (y b)=F.road (x (Q a)) (y (S b))) :Layer.row (fun i j=>N (Q i) (S j)) F x y u:=by
 intro i; simp_rw [he i]; exact (quota_perm S (N (Q i)) _).trans_le (h _)
variable (P:Patch)(K:KernelChoices) (R: Cross P.L (TypeFace 1) (TypeFace 1))
variable (σ Ω:ℝ)(r:ℕ)

def lesser (n:Side) :ℝ:= Ω/(n.val:ℝ)
variable {σ r Ω} (G)

def scar (θ:ℝ)(u:ℕ) :ℝ:= if h:0<θ then (stipend h u).choose else 1
lemma scars (θ:ℝ)(u:ℕ)(h:0<θ):0<scar θ u ∧ ∀ i:ℕ,(1+(i:ℝ)+4)^u≤ scar θ u*Real.exp (θ*i):=by unfold scar;rw [dif_pos h]; exact (stipend h u).choose_spec

def pack_c (r:ℕ)(v w:ℝ):ℝ≥0∞:= (Fintype.card (PAC G 1):ℝ≥0∞)* ENNReal.ofReal w * ENNReal.ofReal (scar v r)
lemma pack_c_f q c d:pack_c G q c d≠⊤:=by unfold pack_c; finiteness
def fm (G:Gauge)(l:ℝ)(x: Long G.ColorIndex):Room:=seat l x.1
lemma cow_p {l b:ℝ}{r:ℕ}(u:0<l)(h:b=l*P.L.val)(U:0<b)(hp:0<σ) (he:R.strip σ (lesser Ω P.L))(hm:0≤Ω): Layer.row (ruling P G R) (Tariff.native b U r) (fm G l) (fm G b) (pack_c G r σ Ω * ENNReal.ofReal ((P.L.val:ℝ)⁻¹)):=by
 let c:= scar σ r; let f:=lesser Ω P.L
 have ht:chestE (blockQ G P.L) (linksQ G) σ (ruling P G R) _:= roots _ _ (adult_price G P R he (div_nonneg hm (by positivity:0≤ (P.L.val:ℝ))))
 have hx:= payUp (V:=fm G l) (U:=fm G b) U _ (scars σ r hp).2 (costsB u h) (costsG U) ht
 convert hx using 1; unfold pack_c lesser;rw [div_eq_mul_inv, ENNReal.ofReal_mul hm];ac_rfl
lemma half_enn (u :ℝ≥0∞): ‖(1/2:ℝ)‖ₑ*(u+u)=u:=by
 rw [← two_mul,← mul_assoc, ← ofReal_norm,Real.norm_of_nonneg (by norm_num),← show ENNReal.ofReal 2=2 from by simp,← ENNReal.ofReal_mul (by norm_num)];norm_num
lemma coil_P {l b:ℝ}{r:ℕ}(V: RegulatorIR.Gain.Bride G)(_u:0<l)(_h:b=l*P.L.val)(U:0<b)(p:ℝ≥0∞)(HP: Layer.row V (Tariff.native b U r) (Gain.pointS l) (fm G b) p): Layer.row (surge G V) (Tariff.native b U r) (Gain.pointS l) (fm G b) p :=by
 let F:=Tariff.native b U r; let E: Equiv.Perm (Gain.Point G):= Equiv.prodCongr (Equiv.neg Cover) (Equiv.refl _)
 have he:= row_rep HP E (snow G) (fun (p:RegulatorIR.Gain.Point G) v=>?_)
 · intro i; rw [show surge G V i= -(fun j=>V (E i) (snow G j)) from rfl,quota_neg];exact he i
 change Tariff.amount b r _=Tariff.amount b r (dist (Motion.slide l (-p.1)) (seat b (reco _)))
 rw [_root_.map_neg, seat_reco,dist_neg_neg];rfl
lemma pre_slot {l b:ℝ}{r:ℕ}(u:0<l)(h:b=l*P.L.val)(U:0<b)(hp:0<σ)(he:R.strip σ (lesser Ω P.L))(hm:0≤Ω): Layer.row (starrier P G R) (Tariff.native b U r) (fm G l) (fm G b) (pack_c G r σ Ω * ENNReal.ofReal ((P.L.val:ℝ)⁻¹)):=by
 have ht:= cow_p G P R (r:=r) u h U hp he hm
 let F:=starrier P G R; have hh:= row_rep ht (snow G) (snow G) (fun x y=> ?_)
 · simpa only [starrier,half_enn] using! row_smult (N:=ruling P G R + Flurry (ruling P G R)) (row_plus ht hh) (1/2)
 change Tariff.amount b r _=Tariff.amount b r (dist (seat l (reco _)) (seat b (reco _)))
 rw [seat_reco,seat_reco,dist_neg_neg];rfl
end YM.RegulatorIR.Oracle
