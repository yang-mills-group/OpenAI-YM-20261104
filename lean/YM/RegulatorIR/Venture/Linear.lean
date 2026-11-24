import YM.RegulatorIR.Venture.Comfort

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Epoch
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
variable {X: Type}{r s:ℕ}
section Static
-- split differences assuming both bills finite at all *used ranks*; R scale from Ω later
variable {T V:Layer X X}{K K':Packet X r}
lemma swivel_e (i:Fin r)(H:Limits K)(h:Billed T)(q:Tuple X r): Summable (Packet.swivel i K T q):=by
 obtain ⟨c,hc,H⟩:=H
 apply quota_summable (w:=1) (fun _=>le_rfl);apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (h.rows (q i)) hc); rw [quota_base,quota_base, ← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum;intro t; unfold Packet.swivel;rw [enorm_mul]; exact mul_le_mul_right (H _) _
lemma ray_minus (i:Fin r)(H:Billed T)(h:Billed V)(ht:Limits K)(hp:Limits K') : Packet.ray i K T-Packet.ray i K' V= Packet.ray i K (T-V)+Packet.ray i (K-K') V:=by
 have hL : Packet.ray i (K-K') V=Packet.ray i K V- Packet.ray i K' V:=by
    ext1 x;rw [Pi.sub_apply]; unfold Packet.ray;rw [← (swivel_e i ht h x).tsum_sub (swivel_e i hp h x)]; exact tsum_congr fun y=> mul_sub ..
 have hR:Packet.ray i K (T-V)=Packet.ray i K T-Packet.ray i K V:=by
    ext1 x;rw [Pi.sub_apply];unfold Packet.ray;rw [← (swivel_e i ht H x).tsum_sub (swivel_e i ht h x)]; exact tsum_congr fun y=> sub_mul ..
 rw [hL,hR]; abel
lemma splice_e {K:Packet X (r+1)}{P:Packet X (s+1)}(h:0<r+s) {A:Tariff X} {c d:ℝ≥0∞}(H:localQ A K c)(hp:localQ A P d)(hc:c≠⊤)(hd:d≠⊤) (x: Tuple X r) (y:Tuple X s): Summable (lace K P x y):=by
 have hv {r s:ℕ}(K:Packet X (r+1))(P:Packet X (s+1)){u v:ℝ≥0∞}{x:Tuple X r}{y:Tuple X s}(h:0<r)(H:localQ A K u)(hp:localQ A P v)(hu:u≠⊤)(hv:v≠⊤): Summable (lace K P x y) :=by
    let i:Fin r:=⟨0,h⟩;let p: Hold i (x i):=⟨x,rfl⟩;let f(t:Hold i (x i) × X × Tuple X s):=lace K P t.1.val t.2.2 t.2.1
    have hS: Summable f:= quota_summable (w:=_) (fun u:Hold i (x i) × X × Tuple X s=> A.diameter_unit (Fin.append u.1.val u.2.2)) (ne_top_of_le_ne_top (ENNReal.mul_ne_top hu hv) (Packet.splice_first _ _ H hp _ _))
    exact hS.comp_injective (i:=fun x=>(p,x,y)) (fun i j h=>congr_arg (fun x: Hold _ _ × X × Tuple X s=>x.2.1) h)
 by_cases he:0<r
 · exact hv _ _ he H hp hc hd
 exact (hv P K (x:=y) (y:=x) (by omega) hp H hd hc).congr fun i=> mul_comm ..
variable {A:Tariff X}{P P':Packet X (r+1)}{R R':Packet X (s+1)}
lemma splice_re (h:0<r+s)(H:Knows A P)(hp:Knows A P')(he:Knows A R)(hx:Knows A R'): Packet.splice P R-Packet.splice P' R'=Packet.splice (P-P') R+Packet.splice P' (R-R'):=by
 obtain ⟨c,hc,H⟩:=H; obtain ⟨d,hd,hp⟩:=hp; obtain ⟨k,hk,he⟩:=he; obtain ⟨Z,hZ,hx⟩:=hx
 ext1 x; rw [Pi.sub_apply,Pi.add_apply]; unfold Packet.splice
 have h1:= splice_e h H he hc hk (Tuple.cutLeft x) (Tuple.cutRight x)
 have h2 := splice_e h hp he hd hk (Tuple.cutLeft x) (Tuple.cutRight x)
 have h3:= splice_e h hp hx hd hZ (Tuple.cutLeft x) (Tuple.cutRight x)
 unfold lace at h1 h2 h3; simp only [lace,Pi.sub_apply,mul_sub,sub_mul]; rw [h1.tsum_sub h2,h2.tsum_sub h3]; abel
variable {K K':Packet X (r+2)} -- shadows
lemma loop_e {T:Layer X X}(H:Knows A K)(h: Billed T)(hx:0<r)(x: Tuple X r): Summable (Packet.curve K T x):=by
 obtain ⟨c,hc,hT⟩:=billing_point h; obtain ⟨d,hd,H⟩:=H;let i:Fin r:=⟨0,hx⟩;let q:Hold i (x i):= ⟨x,rfl⟩
 apply quota_summable (w:=fun _=> A.diameter x) (fun _=> A.diameter_unit x)
 apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hc hd);apply le_trans _ (Packet.loop_cost H hT i (x i)); exact ENNReal.le_tsum q
lemma loop_re (hx:0<r)(H:Knows A K)(hp: Knows A K')(he:Billed T)(h': Billed V): Packet.loop K T- Packet.loop K' V=Packet.loop K (T-V)+Packet.loop (K-K') V:=by
 ext1 u; rw [Pi.sub_apply,Pi.add_apply];unfold Packet.loop
 have h2:=loop_e H h' hx u; have h1:=loop_e H he hx u; have h3:=loop_e hp h' hx u;unfold Packet.curve at h1 h2 h3; simp only [Packet.curve,Pi.sub_apply,mul_sub,sub_mul];rw [h1.tsum_sub h2,h2.tsum_sub h3];abel
end Static
end YM.RegulatorIR.Epoch
