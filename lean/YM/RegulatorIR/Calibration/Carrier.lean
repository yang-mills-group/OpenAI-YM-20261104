import YM.RegulatorIR.Calibration.Open

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {R:Type} {M:R→ℕ}{n:Page M→Side} (S:Circuit M n){K:KernelChoices}(Y:Program K) (G:Gauge)(Z:∀ P:Patch,P.Branches K G) (s:Page M→ Scale)
local notation "Q"=> S.payroll Y G Z
local notation "Tr"=> S.lane Y G Z
local notation "H₁"=> S.scroll_j Y G
local notation "T₁"=> S.devices Y G Z
variable {e:ℕ}
local notation "i₀" => Page.opening M
section readiness
lemma joint_limit (i:Flap M) (e r): Knows ((S.dialect Y G Z s).ceilingRoom.cone 0 i) ((T₁ s i).jVac ((Q s).bulk i.prev) e r):=by
 obtain ⟨c,hc,H⟩:= kernel_b S Y G Z s 0 i.prev e r; let C:= (S.dialect Y G Z s); let T:= C.ceilingRoom.cone 0 i;let X:= (Q s).bulk i.prev e r
 let f:= firstChannel (C.maps i.prev) (C.maps i.next); let F:=f.native
 have ht:localQ T (offer F X) c:= local_offer _ (A:= Tariff.native _ (S.l_p i.next) 0) (enters _ _ _ _ _ _ H)
 let k:= valor (s i.prev) e* Oracle.archive (S.pactP i) K G (Z _) e r 0
 exact ⟨c+k, ENNReal.add_ne_top.mpr ⟨hc, ENNReal.mul_ne_top (valor_f _ _) (archived _ _ _ _ _ _ _)⟩, local_add ht (startupK _ _ _ _ _ _ _ _ _)⟩
lemma cease_k (i:Flap M) (e r) : Limits (ceaseHeat (T₁ s i).line ((T₁ s i).jVac ((Q s).bulk i.prev)) false e r):=by
 let V:=((T₁ s i).jVac ((Q s).bulk i.prev));let L:= (T₁ s i).line; let A:= (S.dialect Y G Z s).ceilingRoom.cone 0 i
 have hp: Workday Stage.l₀ (fun _=>A) fun _=> ceaseHeat L V false e r :=by
    apply Workday.sum _ (Finset.range (3*e+1)); intro b _; apply Workday.hot (K:=fun _=>L) (V:=fun _=>V) _ _ false b e r le_rfl
    · intro p hp v; obtain ⟨c,hc,H⟩:= joint_limit S Y G Z s i p v; exact ⟨_, Poly.standard _ hc,fun _=>H⟩
    exact ⟨_,Poly.standard _ (arc_p S Y G i 0), fun _=> Stage.physical _ _ _ _ _ _ _⟩
 obtain ⟨c,h,H⟩:=hp; exact bounds_from (H ()) (h.cost _)
lemma stamps (w:R) (e:ℕ)(h:0<e) (i:G.ColorIndex): Rules.token ((Q s).bulk (i₀ w) e 2) i=biases (s (i₀ w)) e:=by
 rw [warmedUp _ _ _ _ _ _ _ h]; unfold Rules.token;rw [Rules.smul_shine]; change _*Rules.token (coil (H₁ _)) _= _; rw [show Rules.token (coil (H₁ _)) i=1 from Rules.kinetic (S.honored Y (i₀ w)).card i,mul_one]
include Y
lemma paints (q: Flap M) : mainR K (S.pactP q) G (Z _) 2=Warm.peak (coil (warmP K.penalty (finer (fringe (X:=G.ColorIndex) (S.rail K q))))):=by
 let t: Page M→Scale:=fun _=>Clocks.flat
 have hf:= ((Tr t).moduli q).rows; exact carriersK _ _ _ _ (T:=S.rail K q) rfl rfl hf.2.1 hf.2.2.1
lemma portrays (w:Flap M): let W:= offer (firstChannel (S.opened G w.prev) (S.opened G w.next)).native (coil (H₁ w.prev))+ mainR K (S.pactP w) G (Z _) 2 2
                          Limits W ∧ ((T₁ s w).pullI W)=coil (H₁ w.next):=by
 simp_rw [paints S Y G Z w, peak_at];have ht:= (Tr s).moduli w; obtain ⟨h,hp⟩:= flits S Y G Z s w; let F:= warmP K.penalty (finer (fringe (S.rail K w) (X:=G.ColorIndex)))
 obtain ⟨hf,hJ⟩:= shanks ht.rows.2.1 ht.rows.2.2.1; have hF : Billed F:= (hJ.lap hf).smul _
 exact ⟨add_l (offerL (coil_bound ht.rows.1) _) (coil_bound hF), Warm.carries ht hp _ rfl h (Stage.con _ _ _ _ _ _|>.2.1)⟩
end readiness
section move
-- compares at e+1 whenever called per step
variable {v : ℝ}{t:Page M→ Scale}
lemma top_h (w:R)(h: biases (s (i₀ w)) (e+1)=biases (t (i₀ w)) (e+1)+v)(ht: Squares e (tale (s (i₀ w)).beta) (tale (t (i₀ w)).beta)): (Q s).bulk (i₀ w) (e+1)= (Q t).bulk (i₀ w) (e+1)+ Warm.peak (v • coil (H₁ (i₀ w))):=by
 ext1 i;rw [Pi.add_apply]; by_cases hv:i=2
 · subst i;rw [peak_at,warmedUp _ _ _ _ _ _ _ (by omega),warmedUp _ _ _ _ _ _ _ (by omega),h,add_smul]
 rw [peak_dark _ hv,add_zero]; let A(P:Page M→Scale):=Circuit.mural G P w; change many (A s) _ _=many (A t) _ _;by_cases hh:i<2
 · rw [primary_low _ (Circuit.serene G s w) (by omega) hh,primary_low _ (Circuit.serene G t w) (by omega) hh]
 by_cases hp:i≤e+1+2
 · rw [primary_high _ (Circuit.serene G s w) (by omega) (by omega) hp,primary_high _ (Circuit.serene G t w) (by omega) (by omega) hp,show biases (s (i₀ w)) (e+1+2-i)=biases _ _ from ht _ (by omega)]
 have he(P:Page M→ Scale): many (A P) (e+1) i=0:= Classical.not_not.mp (fun h=> hp ((Q P).top_v w (e+1) i h).2)
 rw [he,he]
lemma add_h (i:Flap M)(h: biases (s i.prev) (e+1)=biases (t i.prev) (e+1)+v)(ht: Squares e (tale (s i.prev).beta) (tale (t i.prev).beta)): (T₁ s i).addon (e+1)=(T₁ t i).addon (e+1)+v • (mainR K (S.pactP i) G (Z _) 2):=by
 let A:= mainR K (S.pactP i) G (Z _); let P:=mainL K (S.pactP i) G (Z _) (e+1);
 rw [add_k _ _ _ _ _ _ _ (by omega),add_k _ _ _ _ _ _ _ (by omega),add_assoc];apply congr_arg
 let d:=(e+1,(0:ℕ));let N:=Finset.antidiagonal (e+1); have hx:d∈N:= Finset.mem_antidiagonal.mpr (Nat.add_zero _)
 rw [← sum_erase_add _ _ hx,← sum_erase_add N (fun q=> biases (t i.prev) q.1 • A (q.2+2)) hx];rw [show d=_ from rfl, add_assoc];apply congr_arg₂ (·+·)
 · apply sum_congr rfl; intro j hj; obtain ⟨hv,h⟩:= mem_erase.mp hj; have hf:= mem_antidiagonal.mp h
   by_cases hy:j.2=0
   · simp_rw [hy,add_zero] at hf; exact (hv (Prod.ext hf hy)).elim
   rw [show biases _ j.1= _ from ht _ (by omega)];rfl
 change biases (s _) (e+1) • _= biases (t _) _ • A 2+ v • _;rw [h,add_smul]
lemma chests (i:Flap M)(h: biases (s i.prev) (e+1)=biases (t i.prev) (e+1)+v)(ht: Squares e (tale (s i.prev).beta) (tale (t i.prev).beta))(H: Matches e ((Q s).bulk i.prev) ((Q t).bulk i.prev))(hp: (Q s).bulk i.prev (e+1)= (Q t).bulk i.prev (e+1)+Warm.peak (v • coil (H₁ i.prev))):
 (Q s).bulk i.next (e+1)= (Q t).bulk i.next (e+1)+Warm.peak (v • coil (H₁ i.next)):=by
 let A:= coil (H₁ i.prev); let W:=(Q s); let V:= (Q t);let P:= T₁ s i;let D:=T₁ t i;let B:= P.jVac (W.bulk i.prev);let U:=D.jVac (V.bulk i.prev); let l:= P.line;let k:=e+1
 let E:= (firstChannel (S.opened G i.prev) (S.opened G i.next)).native; let X:=mainR K (S.pactP i) G (Z _) 2
 let C:= offer E A+ X 2
 have he:X=Warm.peak (X 2):=by unfold X; rw [paints S Y G Z i, peak_at]
 have hx : B (e+1)= U (e+1)+Warm.peak (v • C):=by
    ext1 r;change offer E ((Q s).bulk i.prev (e+1) r)+(T₁ s i).addon (e+1) r= _; rw [hp,add_h _ _ _ _ _ i h ht]; by_cases hz:r=2
    · subst r; rw [Pi.add_apply (f:= _ ), peak_at,Diagram.offer_sum', Sources.scaleO]; change _=U _ _+(Warm.peak _ 2); rw [peak_at, show v • C= v • offer E A + v • X 2 from smul_add ..];change (_+ _)+(D.addon k 2+ v • X 2)= (_+D.addon k 2)+ _; abel
    simp_rw [Pi.add_apply,Pi.smul_apply,peak_dark _ hz, show mainR K (S.pactP i) G (Z _) 2=X from rfl]; nth_rw 1 [he]; simp_rw [peak_dark _ hz,smul_zero, add_zero]; rfl
 have hf: ceaseHeat l B false (e+1)=ceaseHeat l U false (e+1)+ Warm.peak (v • C):= finale l (joint_h _ _ _ _ _ _) (joint_h _ _ _ _ _ _) ((slims S Y G Z s i ht).joint_m H) hx
 ext1 r; rw [← (Q s).step_v, ← (Q t).step_v, Pi.add_apply]; change P.pure _ _ r= D.pure _ _ r+Warm.peak _ r; unfold GridStep.pure
 split
 next H=> rw [peak_dark _ (by omega),add_zero]
 next H=>
    change P.pullI (ceaseHeat l B _ _ _)=P.pullI (ceaseHeat l U _ _ _)+ _
    rw [hf, Pi.add_apply]; by_cases hr:r=2
    · subst r;obtain ⟨hh,hv⟩:= portrays S Y G Z s i; rw [peak_at,peak_at,pull_a P (flits S Y G Z s _|>.1) (show Limits (ceaseHeat l U false (e+1) 2) from cease_k S Y G Z t i (e+1) 2) (tilt_l hh _), pull_m,show P.pullI C=_ from hv]
    rw [peak_dark _ hr, peak_dark _ hr,add_zero,add_zero]
lemma increases (x:G.ColorIndex)(i:Page M)(h:(Q s).bulk i (e+1)= (Q t).bulk i (e+1)+Warm.peak (v • coil (H₁ i))) : Rules.token ((Q s).bulk i (e+1) 2) x= Rules.token ((Q t).bulk i (e+1) 2) x + v :=by
 let A:= (Q s).bulk i (e+1); let X:= (Q t).bulk i (e+1); let C:= (H₁ i)
 have ht : A 2-X 2=v • coil C:=by unfold A X C; rw [h,Pi.add_apply,peak_at, add_sub_cancel_left]
 rw [← sub_eq_iff_eq_add']; unfold Rules.token; rw [← Rules.minus_shine (cost_token _ _ _ _ _ i _) (cost_token _ _ _ _ _ i _) 2 (by omega)];change Pupil.shine (A 2-X 2) _ _ _ _ = v; rw [ht,Rules.smul_shine,show Pupil.shine (coil C) _ _ _ _ = _ from Rules.kinetic (S.honored Y i).card x,mul_one]
end move
end YM.RegulatorIR.Calibration
