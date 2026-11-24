import YM.RegulatorIR.Geometry.Rain
import YM.RegulatorIR.Step.Batch
import YM.RegulatorIR.Address.Script

/-! Common exact scale and kernel budget constructor on link labels. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Finset Function Lattice PertExtension Orb Gauge Budget Budget.Tuple Budget.Packet Motion Tariff Spatial Uniform ENNReal
open scoped ENNReal NNReal BigOperators Classical Topology
variable {W X:Type}{l P R:ℝ}{n:Side}
private def e₁ (v:Cover): Equiv.Perm (Edge Cover):=⟨dis v,dis (-v),fun a=>by simp [dis],fun a=>by simp [dis]⟩
def latticeWalk (X:Type) (l:ℝ): Address.Calendar l (Long X) where
 home w:= seat l w.1
 lamp v:= Equiv.prodCongr (e₁ v) (Equiv.refl X)
 lit i x:= dis_seat l i x.1

-- Joint counts. Keep n different for fine and coarse.
def plusBill (R l:ℝ):ℝ≥0∞:= (polygon.card:ℝ≥0∞)*(4* ENNReal.ofReal ((1+2*R/l)^4))*(∑' k,kilo k)
lemma colors (X:Type)[Fintype X](H:Even n.val)(hl:0<l)(hp:l*n.val=P)(hR:0<R): let A:=Cart l P X H hp; (∑' i: Hatch n X,(amount R 6 (singular P (A.atO i)))⁻¹) ≤ plusBill R l * Fintype.card X:= by
 intro A; rw [ENNReal.tsum_prod']; apply le_trans _ (mul_le_mul_left (rootTax hl hR hp) _)
 rw [← ENNReal.tsum_mul_right];apply ENNReal.tsum_le_tsum; intro a;change (∑' _:X,(amount R 6 (altitude P l a))⁻¹)≤ _; rw [tsum_fintype]; simp [nsmul_eq_mul,mul_comm]
lemma root_poly {l R:W→ℝ}(hl:∀ w,0<l w)(hr:∀ w,0<R w){L:Meter W}(h: Poly L (fun w=> ENNReal.ofReal (R w/l w))): Poly L (fun w=>plusBill (R w) (l w)):=by
 have hx : Poly L (fun w=> ENNReal.ofReal ((1+2*R w/l w)^4)):=by
    convert ((Poly.oneQ L).add ((Poly.standard _ (by finiteness : (2:ℝ≥0∞)≠⊤)).mul h)).powQ 4 using 1; ext1 w; have hi:=hl w; have hh:=hr w
    rw [mul_div_assoc, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)];simp
 exact Poly.mul ((Poly.standard _ (by finiteness : (polygon.card:ℝ≥0∞) ≠ ⊤)).mul ((Poly.standard _ (by finiteness : (4:ℝ≥0∞)≠⊤)).mul hx)) (Poly.standard _ totalK)

variable {P l m R:W→ℝ} {n k:W→Side} (X:Type) [Fintype X]
lemma sum_weight (hp:∀ w,0<P w)(hl:∀ w,0<l w)(hm:∀ w,0<m w)(hr:∀ w,0<R w)
 (he:∀ w,l w*(n w).val=P w)(ht:∀ w,m w*(k w).val=P w)(hx:∀ w,Even (n w).val)(hy:∀ w,Even (k w).val)
 {L:Meter W} (h:Poly L fun w=> ENNReal.ofReal (R w/l w))(hh:Poly L fun w=> ENNReal.ofReal (R w/m w)) : let A : Post (fun _:W=> Long X⊕Long X) (fun w=> Hatch (n w) X⊕Hatch (k w) X):= ⟨P,hp,R,hr,fun w=> Step.combine (Cart (l w) (P w) X (hx w) (he w)) (Cart (m w) (P w) X (hy w) (ht w))⟩; Poly L (A.weight 6):=by
 intro A; have hz:= Poly.standard L (by finiteness : (Fintype.card X:ℝ≥0∞)≠⊤)
 apply Poly.mono (((root_poly hl hr h).mul hz).add ((root_poly hm hr hh).mul hz)); intro w
 unfold Post.weight
 let f (i:Hatch (n w) X⊕Hatch (k w) X):= (amount (R w) 6 (singular (P w) ((A.deck w).atO i)))⁻¹
 change (∑' i,f i)≤_; rw [tsum_fintype,Fintype.sum_sum_type];
 have h₁:=colors X (hx w) (hl w) (he w) (hr w); have h₂:=colors X (hy w) (hm w) (ht w) (hr w); dsimp only at h₁ h₂; rw [tsum_fintype] at h₁ h₂; exact add_le_add h₁ h₂
end YM.RegulatorIR.Geometry
