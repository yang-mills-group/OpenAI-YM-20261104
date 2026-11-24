import YM.RegulatorIR.Pupil.Lintel

/-!
# Paying W1 at selected marks. local moment representative; bounds
independent of horizon lengths until applying previous-order Keeps.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Laurent WOne
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{I:Type}{p k u m e n r:ℕ}
variable {H C d b:ℝ≥0∞}{U:Orders (Foot G)} {x:Foot G}
-- positive grant using all i (s=0 permitted)
def LowerQ (U:Orders (Foot G))(k u:ℕ)(C:ℝ≥0∞):Prop:=∀ i<k,∀ r ≤ i+2, Keeps (U i r) u C
def tradeP (G:Gauge)(H:ℝ≥0∞)(e:ℕ) := ∑ j∈ antidiagonal e,∑ i∈ Finset.range (j.1+2+1), (i:ℝ≥0∞)*(Fintype.card G.ColorIndex:ℝ≥0∞)*(2*billow G H j.2 i)
lemma tradeP_end (G:Gauge)(hc:H≠⊤)(e:ℕ): tradeP G H e ≠⊤:=by
 unfold tradeP; refine ENNReal.sum_ne_top.mpr fun i _=> ENNReal.sum_ne_top.mpr (fun j _=> ?_); apply ENNReal.mul_ne_top; finiteness
 exact ENNReal.mul_ne_top (by finiteness) (costs_b hc _ _)
lemma sweep_fee (x:Foot G) {A B:BEdge G}{σ:Cover→G.Color}(h:TightF (area x) H A)(hk:TightF (area x) H B)(ht:TightS (area x) H σ)(ha:GivesT A)(hb:GivesT B)(hv:(Function.support σ).Finite) (hl:∀ z,z≠x.1→A z=B z){U:Orders (Foot G)}(hc:LowerQ U e u C)(hp:r≤u):
 ‖sweep U e r A σ-sweep U e r B σ‖ₑ≤ tradeP G H e*C:=by
 unfold WOne.sweep; simp_rw [← Finset.sum_sub_distrib]
 let S:= (antidiagonal e); let Q:= S.erase (e,0); let f(i:ℕ)(j:ℕ×ℕ):= (i:ℝ≥0∞)*(Fintype.card G.ColorIndex:ℝ≥0∞)*(2*billow G H j.2 i)
 let g(j:ℕ×ℕ):= ∑ i∈ Finset.range (j.1+2+1),f i j
 apply (enorm_sum_le ..).trans; apply le_trans (b:=∑ j∈Q,g j*C)
 · apply sum_le_sum; intro j hj; apply (enorm_sum_le ..).trans; unfold g; rw [sum_mul]; apply sum_le_sum; intro i hi
   split_ifs with Hv; swap; simp only [sub_self,enorm_zero]; exact bot_le
   obtain ⟨hn,hq⟩:= mem_erase.mp hj; have he:= mem_antidiagonal.mp hq; have hu:j.2≠0:= fun hh=>hn (Prod.ext (by change j.1=e;omega) hh)
   exact link_fee x h hk ht ha hb hv hl (hc j.1 (by omega) i (by rw [Finset.mem_range] at hi;omega)) (le_trans Hv.le hp)
 rw [← sum_mul]; apply mul_le_mul_left; exact Finset.sum_le_sum_of_subset (erase_subset (e,0) S)

-- triangle pin/value of gradient hook. full arity only.
variable (V:W1 U p) (L:LowerQ U e u C) (he:e≤p)(hp:r≤ u)(hk:r ≤e+2)(hx:IsSym (U e r))
variable {σ:Cover→G.Color}(A:Fin r→ BEdge G)(hs:TightS (area x) d σ)(ht: ∀ i,TightF (area x) H (A i))
variable (hσ:(Function.support σ).Finite) (hf:∀ i,GivesT (A i))
variable (q j: Fin r)(hb:A q=pointA x)(hj:j≠q)(hq:A j=regalia σ)
def cork (G:Gauge)(H d:ℝ≥0∞)(e r:ℕ):ℝ≥0∞:= Fintype.card (Finset (Fin r))*tradeP G (d+r*H) e
lemma cork_f (h:H ≠⊤)(hd:d≠⊤): cork G H d e r ≠⊤:= ENNReal.mul_ne_top (by finiteness) (tradeP_end _ (by finiteness) _)
include V L he hp hk hx hf hs ht hσ hb hj hq
lemma oracle : ‖matchT (U e r) A‖ₑ≤ cork G H d e r*C:=by
 let p:= area x;let v:= pointA x;let s (i:Finset (Fin r)):= -sweep U e r (∑ z∈ i,A z) σ
 let P:= Finset.univ.erase j; let g(i: Finset (Fin r)):=s (insert q i)-s i;let B:ℝ≥0∞:= d+r*H;let b:=tradeP G B e*C
 have hh(i:Finset (Fin r)): TightF p B (∑ a∈i,A a):=fun x=> (tight_setsum i A ht x).trans (mul_le_mul_left (show (r:ℝ≥0∞)*H≤B from le_add_self) _)
 have hS:TightS p B σ:=fun x=> (hs x).trans (mul_le_mul_left (show d≤B from le_self_add) _)
 let S:= P.erase q
 have hv(i)(hi:i∈S.powerset) : ‖g i‖ₑ≤ b:=by
    let a:=∑ z∈ i,A z; let a':= ∑ z∈ insert q i,A z
    change ‖-_ - -_ ‖ₑ ≤ _; rw [← neg_sub',enorm_neg] -- neg_sub'?
    refine sweep_fee x (hh (insert q i)) (hh i) hS (sum_gives _ A hf) (sum_gives _ A hf) hσ ?_ L hp
    intro z hz;rw [sum_insert (fun hu=> notMem_erase q P ((mem_powerset.mp hi) hu)),Pi.add_apply,hb,show pointA x z=0 from if_neg hz, zero_add]
 have hr : ‖adjure g S‖ₑ≤ cork G H d e r*C :=by
    unfold adjure; apply (enorm_sum_le ..).trans; apply le_trans (b:=∑ _∈S.powerset,b)
    · apply sum_le_sum;intro i hi;apply le_trans ?_ (hv i hi)
      rw [enorm_mul,← ofReal_norm,_root_.norm_pow,norm_neg,norm_one,one_pow,ENNReal.ofReal_one,one_mul]
    unfold cork; rw [sum_const,nsmul_eq_mul, mul_assoc];apply mul_le_mul_left;exact_mod_cast (Finset.card_le_univ S.powerset)
 rw [← show adjure s P=adjure g S from remove s P q (Finset.mem_erase.mpr ⟨Ne.symm hj,mem_univ _⟩)] at hr
 apply le_trans _ hr; rw [show adjure _ _ = _ from (WOne.gradient V he hx A hf hk j σ hσ hq).symm, enorm_mul]; refine le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_left (show (1:ℝ≥0∞)≤ ‖(r.factorial:ℝ)‖ₑ from ?_) _)
 rw [← ofReal_norm,Real.norm_natCast]; exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal (by exact_mod_cast r.factorial_pos)
end YM.RegulatorIR.Pupil
