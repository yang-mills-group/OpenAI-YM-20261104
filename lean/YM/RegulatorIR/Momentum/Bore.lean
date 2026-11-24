import YM.RegulatorIR.Momentum.Sustain

/-! Generative gain for vacuum carried-in. Before projection resets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Sources Oracle Oracle.Quarry RG Bloch Precision Tree PertExtension Geometry.Field Exterior
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {G:Gauge}{P:Patch}{X Y:Type} {r u m:ℕ}{C F A B:ℝ≥0∞}
lemma self_r (G:Gauge){P:Patch}(R:Cross P.L (TypeFace 1) (TypeFace 1)):SelfT (ruling P G R) P.L.val:=by
 intro i j x; have he:= albedoX P R G i j x; rw [strut,site_roll] at he; exact he
-- constants pre-L

def fore_c (X:Type)[Fintype X](r u m:ℕ)(F:ℝ≥0∞):=(Fintype.card (Regalia X):ℝ≥0∞)*F*((1+r:ℝ≥0∞)^u*F^r*2^u*ledger_c X r u m)
def fore_b (X:Type)[Fintype X](r u m:ℕ)(F:ℝ≥0∞):=(Fintype.card (Regalia X):ℝ≥0∞)*F*((1+r:ℝ≥0∞)^u*F^r*2^u*ledger_d X r m)
lemma fore_c_f [Fintype X](hv:F≠⊤) : fore_c X r u m F≠⊤:=by
 unfold fore_c ledger_c
 have he := limited_f (J:=Fin r×Axis) u m; finiteness
lemma fore_b_f [Fintype X](hv:F≠⊤) : fore_b X r u m F≠⊤:=by
 unfold fore_b ledger_d
 have he := display_f (J:=Fin r×Axis) m; finiteness
lemma woo {L:Side} (r m e:ℕ)(he:e+4≤(r+1)+m): (L.val:ℝ≥0∞)^4 * award L.val ^((r+1)+m) ≤ award L.val^e:=by
 let q:ℝ≥0∞:= L.val; let c:= award L.val
 have hp: q*c=1:=ENNReal.mul_inv_cancel (by unfold q; positivity) (by unfold q;finiteness)
 have hx:c≤1 := by simpa only [q,c,award,inv_one] using ENNReal.inv_le_inv.mpr (show 1 ≤ q from by unfold q;exact_mod_cast L.property)
 change q^_*c^_ ≤ _; calc
   _ ≤ q^4*c^(e+4):= mul_le_mul_right (pow_le_pow_of_le_one bot_le hx he) _
   _ = c^e:= by rw [Nat.add_comm,pow_add, ← mul_assoc, ← mul_pow,hp,one_pow,one_mul]
lemma obtains_h [Fintype X]{L: Side}{K:Fin (r+1)→Layer (Long X) (Long Y)}{T:Packet (Long X) (r+1)}(S:∀ i, PriceW (K i) L.val u m F)(H:Held T u A)(h: m≤u)(M: MomentsP T m B)(V:SelfT (K 0) L.val)(e:ℕ)(he:e+4≤(r+1)+m)(hf:F≠⊤)(ha:A≠⊤) :
 Held (unfoldQ K T) u (fore_c X r u m F * award L.val ^ e * A + fore_b X r u m F * (L.val:ℝ≥0∞)^4 * B) := by
 let c:ℝ≥0∞:=L.val; let Z:= award L.val; have hz : Z≤1:= by simpa only [Z,c,award,inv_one] using ENNReal.inv_le_inv.mpr (show 1 ≤ c from by unfold c;exact_mod_cast L.property)
 intro i; let p:= fore_c X r u m F; let q:= fore_b X r u m F
 have hx : c≠⊤:= by unfold c; finiteness
 have hu : Z≠⊤:= ne_top_of_le_ne_top (by finiteness : (1:ℝ≥0∞)≠⊤) hz
 have he₀ : c^4 * Fintype.card (Regalia X) * (F*Z)≠⊤:=by finiteness
 refine (band K T he₀ ha hf S (repays_roots V (S _)) H L.property M h i).trans ?_
 change c^4*_* (F*Z) * ((1+(r:ℝ≥0∞))^u*((F*Z)^r*2^u)*(ledger_c X r u m*Z^m*A+ ledger_d X r m*B))≤_
 calc
    _ = p*(c^4*Z^(r+1+m))*A+q*c^4*Z^(r+1)*B:=by unfold p q fore_c fore_b; rw [pow_add,pow_succ,mul_pow];ring
    _ ≤ _:= add_le_add (mul_le_mul_left (mul_le_mul_right (woo (L:=L) r m e he) _) A) (mul_le_mul_left (show _ ≤ q*c^4 from (mul_le_mul_right (pow_le_one₀ (zero_le : 0≤Z) hz (n:=r+1)) (q*c^4)).trans_eq (mul_one _)) _)
end YM.RegulatorIR.Momentum
