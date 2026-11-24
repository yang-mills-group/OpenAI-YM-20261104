import YM.RegulatorIR.Tape.Resound
import YM.RegulatorIR.Binding.Fair

/-!
# Point channel before profile aggregation

Any profiles at given cutoff if authenticated B outputs (Stencil etc.).
Not dying rates until size constraints imposed. Positivity of Ω inverse money
fully internal. No statements about field basis convergence. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Taping
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W:Type} {u b p j k a s m e:ℕ}{M: W→ℕ}{n:Page M→Side} {L:Meter W}{J D:Choice M}
variable {S:Heir n G} (R: Reel S) {Γ: Flap M → Layer (Foot G) (Foot G)} {V: Flap M → Bride G}
  {c: Flap M→ℝ≥0∞}
variable {T:S.Accounts}

-- assemble schedules from consumers. choose extra moment power positivity b.
-- strengthen Lead exponent r≥1 for clearer precondition.
def quantum (b u:ℕ):ℕ:=u+b+6+(u+b+6)

structure Cylinder (R: Reel S)(T:S.Accounts)(Γ:Flap M→ Layer (Foot G) (Foot G))(V:Flap M→Bride G)(L:Meter W)(c: Flap M→ ℝ≥0∞)(p b u:ℕ) : Prop where
  positive : 0<b
  port : R.Follows T
  price : Halo.Aug.Amenities S L p (quantum b u)
  inspiration : Inspires Γ V S
  rates : Azur R Γ V (quantum b u) L c
  bulk : S.Supplies T L p (quantum b u)

-- Need typed Radius and gamma ratios independently of capacity padding. Here one alpha.
structure Lantern (S:Heir n G) (D:Choice M)(L:Meter W)(c:Flap M→ℝ≥0∞)(γ:ℝ) : Prop where
 ref_mesh : ∀ w,S.l (D.choose w)=1
 gleams : 0<γ
 small : γ ≤ 1
 scale : Poly (flapL M L) (fun w=>ENNReal.ofReal (S.shift w))
 cold : ∀ w,c w ≤ ENNReal.ofReal ((S.shift w ^ γ)⁻¹)
 side : ∀ w,1 ≤ S.P w

variable {R} {x:W→Room} {γ c₀:ℝ}
namespace Cylinder
variable (A:Cylinder R T Γ V L c p b u)
include A
lemma leads (B:Lantern S D L c γ): S.Radiants L γ (u+b+b) 1 c D:=by exact {
   ref_mesh:= B.ref_mesh, gleams:=B.gleams, small:=B.small, scale:=B.scale,cold:=fun w=> by rw [pow_one]; exact B.cold w,side:=B.side, lead:=A.rates.diagonal A.inspiration (by unfold quantum; omega) }
lemma creators : S.Primitive L p (quantum b u):=A.rates.era A.inspiration p A.price
-- For cosmos, λ rounding handled by assigning any bounded log range.
omit A in
lemma fare (R:Reel S)(B:Lantern S D L c γ) : Poly (flapL M L) (S.ceilingRoom.weight 6):=by
 unfold Uniform.Post.weight; let n' (p:Flap M):=n p.prev;let m' (p:Flap M):=n p.next
 have hx:= Geometry.sum_weight G.ColorIndex (P:=fun i:Flap M=>S.P i.volW) (l:=fun i=>S.l i.prev) (m:=fun i=>S.l i.next) (R:=fun i=>S.l i.next) (k:=fun i=>m' i) (n:=n') (L:=flapL M L) (fun v=> S.hp v.volW) (fun v=>S.hl _) (fun v=> S.hl _) (fun v=> S.hl _) (fun v=> R.phase v.prev) (fun v=> R.phase v.next) (fun v=>R.even v.prev) (fun v=>R.even v.next) B.scale (show Poly _ _ from ?h)
 dsimp only at hx
 convert hx using 1;ext1 w; change (∑'z:Book G _ ⊕ Book G _, (Tariff.amount (S.l w.next) 6 (singular (S.P _) ((Step.combine (S.maps w.prev) (S.maps w.next)).atO z)))⁻¹)= _; rw [R.realms w.prev,R.realms w.next];rfl
 case h =>
   suffices hv : ∀ i:Flap M,S.l i.next/S.l i.next=1 by simp_rw [hv]; simpa using! Poly.oneQ (flapL M L)
   exact fun _=> div_self (S.hl _).ne'

variable (Z:T.Report m) (U : W→ Portrait G)
variable (hs:∀ w,Halo.BasisT m s (U w) (Z.main (Page.opening M w)))
include hs
lemma splines (B:Lantern S D L c γ): S.Cosmos T (u+b) 6 p L:=by
 refine { prim:=A.creators, space:=A.bulk,tops:=fun x h k hv hw=>?_, ward:= A.rates.ordWard A.inspiration T Z U A.bulk A.price (by have h:=A.positive; unfold quantum;omega) A.port hs, counted:= fare R B }
 obtain ⟨z,hc,h',hh⟩:=A.port x; unfold Sky.Accounts.change;rw [hh]; exact sub_self _
lemma proper (B:Lantern S D L c γ)(h:S.Preserved T Z 1 a p D x (u+b+b) L)(hp:0<c₀)(hc:S.cushion c₀ x): S.Registry T Z L u b 6 p 1 a c₀ γ x D c:=by
 have hk:14≤quantum b u:=by have ht:=A.positive;unfold quantum; omega
 refine ⟨A.splines Z U hs B,A.leads B,h,A.rates.preWard A.inspiration T Z U A.bulk A.price hk A.port hs,fun i _ _ _ hh he=>?_, A.rates.explicitO A.inspiration T Z U A.bulk A.price hk A.port hs,A.positive,hc,hp⟩
 omega
lemma transmission (B:Lantern S D L c γ)(h:S.Preserved T Z 1 a p D x (u+b+b) L)(hp:0<c₀)(hc:S.cushion c₀ x)(he:e ≤ p)(ht:D.age≤J.age)(N:R.Endings L):
 Carry L (fun w=> ENNReal.ofReal (S.modifyErr a b γ J w)) (fun w=> ‖plotPT (R.clock (Page.opening M w)) (vital (TopF n w) (U w)) s e-Ledger.Sky.note (Z.main (J.choose w) e 0)‖ₑ):= Coverage.amplitudes T Z _ _ _ (Halo.hinted R T Z A.port U hs) R.learned (proper A Z U hs B h hp hc) (R.year L N u p) he ht
end Cylinder
end YM.RegulatorIR.Taping
