import YM.RegulatorIR.Address.Rooted
import YM.RegulatorIR.Cluster.Access

/-! Engineering factor for fine-side fidelity. Includes derivatives in
measuring-root convention; prices also pay Test seminorms as needed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Address.Calendar
open MeasureTheory Lattice Budget Budget.Packet Budget.Layer Budget.Tariff Budget.Tuple Motion Cluster Cluster.Collapsed Uniform Ledger Ledger.Sky Diagram ENNReal
open scoped ENNReal NNReal Topology BigOperators Classical
variable {X Z:Type} [MeasurableSpace Z] {l d:ℝ} {r u e:ℕ}{c:ℝ≥0∞}
variable (A:Calendar l X)(Q:TagList X Z r)(B:Script Z)(S:Set Room)(x:Room)

-- kme suffices not just for costs with totalized tsum and integral, but for
-- actual Integrability and representation by sums.
lemma counts (hl:0<l)(hc:c≠⊤)(hd:0≤d)(hh:Bills B S x d c)(hw: A.kme Q u≠ ⊤)(v): Summable (fun i=> spoke A Q B i v):=by
 apply quota_summable (w:=1) (fun _=>le_rfl)
 apply ne_top_of_le_ne_top (ne_top_of_le_ne_top (ne_top_of_le_ne_top (by finiteness) (cost_centers A Q B S x hh u hl hd)) (lines A Q B S u hl)); unfold quota; apply ENNReal.tsum_le_tsum
 intro i; let P:=(realm hl u S).uses A.home; exact le_trans (mul_le_mul_right (P.width_unit v) _) (term_le ..)
lemma valid (hl:0<l)(hc:c≠⊤)(hd:0≤d)(hh:Bills B S x d c)(hw:A.kme Q u ≠ ⊤)(p v) : Integrable (weighed (l:=l) Q B p v) (Q.rolls v):=by
 refine ⟨(root_see Q B l v p).aestronglyMeasurable,?_⟩
 have hp:= cost_centers A Q B S x hh u hl hd
 let P:=(realm hl u S).uses A.home
 let f p v:=∫⁻ z, ‖weighed (l:=l) Q B p v z‖ₑ*P.width (A.sends p v) ∂(Q.rolls v)
 apply lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top (ne_top_of_le_ne_top (by finiteness) hp) (show f p v≤gridTax A Q u B S hl from (ENNReal.le_tsum (f:=f p) v).trans (ENNReal.le_tsum (f:=fun i=>∑' v,f i v) p))))
 exact lintegral_mono fun _=> (mul_one _).ge.trans (mul_le_mul_right (P.width_unit _) _)

def material (H:ℕ) : Packet X r := (l^4/(l^H)) • calyx A Q B
lemma money_real (hl:0<l)(h:l≤1)(hd:0≤d) (n:ℕ): ENNReal.ofReal (l^4/(l^n))*ENNReal.ofReal ((1+2*d/l)^4) ≤ (1+2* ENNReal.ofReal d)^4*((ENNReal.ofReal l)^n)⁻¹:= by
 rw [← ENNReal.ofReal_mul (by positivity)]
 calc
 _ ≤ ENNReal.ofReal ((1+2*d)^4*(l^n)⁻¹):= by
    apply ENNReal.ofReal_le_ofReal
    calc
     _ =(l+2*d)^4*(l^n)⁻¹:=by field_simp
     _ ≤ _:= by gcongr
 _ = _:= by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul (by norm_num)]; simp
lemma material_price (hl:0<l) (h:l≤1) (hd:0≤d)(H:Bills B S x d c)(m:ℕ) : markQ ((realm hl u S).uses A.home) (material A Q B m) ≤ ((1+2* ENNReal.ofReal d)^4*c)*((ENNReal.ofReal l)^m)⁻¹* A.kme Q u:=by
 unfold markQ material
 apply le_trans (quota_times ..).le
 apply (mul_le_mul_right (wall A Q B S x H u hl hd) _).trans
 rw [← ofReal_norm, Real.norm_of_nonneg (by positivity : 0≤ l^4/l^m),← mul_assoc]
 exact le_trans (mul_le_mul_left (money_real hl h hd m) _) (le_of_eq (by ac_rfl))
end YM.RegulatorIR.Address.Calendar

namespace YM.RegulatorIR.Address.Calendar
open MeasureTheory Lattice Budget Budget.Packet Budget.Layer Budget.Tariff Budget.Tuple Motion Cluster Cluster.Collapsed Uniform Ledger Ledger.Sky Diagram ENNReal
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W:Type}{M:W→ℕ} {X Y Z:Page M→Type} [∀ i,MeasurableSpace (Z i)]
    (S:Sky X Y) {p u e h:ℕ}{L:Meter W} {x:W→Room} {c:Page M→ℝ≥0∞}{D:W→ Set Room}{d:W→ℝ}
    {A:(w:Page M)→ Calendar (S.l w) (X w)} {a:ℝ}
    {Q:∀ i:Page M,(e r:ℕ)→TagList (X i) (Z i) r}

lemma restoration (B:(i:Page M)→ Script (Z i))(hl:∀ i,S.l i≤1)(hq:∀ i, (A i).home=Stations S i)
  (H:∀ i : Page M, Bills (B i) (D i.bindW) (x i.bindW) (d i.bindW) (c i)) (hc: Poly (coverL M L) c)(hp:Poly L (ENNReal.ofReal ∘ d)) (hd:∀ i,0≤d i)
  (hU:∀ e≤p,∀ r:ℕ,Carry (coverL M L) (fun i=> ENNReal.ofReal ((S.ε i.bindW / S.l i)^a)) fun i=> (A i).kme (Q i e r) u) :
    Folds p (coverL M L) (estate S.hl (Stations S) (D ∘ Page.bindW) u) (topGrowth S a h) fun w e r=> material (A w) (Q w e r) (B w) h:=by
 intro e he r; let v:= topGrowth S a h
 have hv : Carry (coverL M L) v fun i:Page M=> (heightP S.l h i)⁻¹*(A i).kme (Q i e r) u:= by
    have hx:= Carry.scale (w:=fun i=>(heightP S.l h i)⁻¹) (hU e he r)
    apply Carry.mono (Carry.charge hx (Carry.mono (Carry.unit (coverL M L) v) (fun i=> (le_of_eq (mul_comm ..)))))
    intro i; exact le_of_eq (mul_comm ..)
 have hG: Poly (coverL M L) (fun i=> (1+2*ENNReal.ofReal (d i.bindW))^4*c i):= Poly.mul (Poly.powQ ((Poly.oneQ (coverL M L)).add ((Poly.standard _ (by finiteness : (2:ℝ≥0∞)≠⊤)).mul (Poly.us hp Page.bindW))) 4) hc
 apply Carry.mono (Carry.mul_left hG hv); intro i
 let P:=material (A i) (Q i e r) (B i) h
 change markQ ((realm (S.hl i) u _).uses (Stations S i)) P ≤ _; rw [← hq i]
 exact le_trans (material_price (A i) (Q i e r) (B i) _ (x i.bindW) (S.hl i) (hl i) (hd _) (H i) _) (le_of_eq (mul_assoc ..))
end YM.RegulatorIR.Address.Calendar
