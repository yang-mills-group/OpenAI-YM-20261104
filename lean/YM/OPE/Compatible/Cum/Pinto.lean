import YM.OPE.Compatible.Cum.Nut
/-!
# tangling Backs. paid at both envelopes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J E:Type}{N:Side} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] {μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E} [Fintype I]
local notation "Q!"=> deck I N
local notation "K!"=> Flume.Script.Tab I N
variable {Z:E→L[ℝ] deck I N} {Ω:Row I I}{C:ℕ→ℝ}{p e k d t n u:ℕ}{b c s a w:ℝ}
omit [MeasurableSpace E] [BorelSpace E] in
lemma mortPay (x:Q!)(i:Site N)(j:Fin (d+1))(P:Script I (e+(d+1)+1))(ha:0≤a)(hs:0<s)(hp:Ω.strip s a)(hv:Cold i i (Oriel L Z-Ω.acts N) c k)(hz:0≤c)(hP:soot k P b):
   let _A:=Shell.Cycle e d P j
   let W:= ∑ k: K!, φx (d:=d+1) x x Z ((orchestra P i).curryLeft (deltaH k)) (L.inverse (Ferry Z k)) j
   let h:= SX x x Z (orchestra (knots e d P j Ω) i) (d:=d) (e:=e)
   BeamS (grain N k • (W-h)) (((8:ℝ)^k*widthCost s k*a+ (3:ℝ)^k*c)*b) (clockY x Z) (e+d):=by
       intro A X f; let Y:= knots e d P j Ω; have he:soot k Y (b*a):=styleR P hp hs.le ha hP j; have hA:soot k A b:=slice_fee _ _ hP; have hb:Bond X:= Sumbond _ _ fun j _=> φBond ..; have hc:Bond f:=cueBond x x Z (orchestra Y i); refine ⟨Bond.scale _ (hb.sub hc),fun z=>?_⟩
       let v:= cue (x+Z z) x e d; let H:= (clockY x Z z)^(e+d); have hz' : 0 ≤ clockY x Z z := zero_le_one.trans (tallY Z x z); have hq:(∏ i,‖v i‖) ≤ H:= (prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> cuePad x Z z i)).trans_eq (by rw [prod_const,card_univ,Fintype.card_fin]); let p:= Ω.acts N; let K:= Oriel L Z; let E':= routeTap p A v i; let L':=grain N k; let U:=b*a
       rw [Pi.smul_apply, Pi.sub_apply,norm_smul,Real.norm_of_nonneg (zero_le_one.trans (grain_b _)),show X z= routeTap K A v i from ?_, show f z=scribe i (pad Ω A) v from scriptV i Y v (sootS he)]
       swap; · unfold X; rw [Finset.sum_apply]; exact tangles i L Z P x x z j (sootS hP)
       let V':=(8:ℝ)^k*widthCost s k*a; change L'* ‖routeTap K A v i-scribe i _ v‖ ≤ (V'+_)*b*H; apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ E' _) (show 0 ≤ L' from zero_le_one.trans (grain_b _))) -- lemma
       have hB:=Sack.coins hP; let A':=(3:ℝ)^k*c; have hy1: routeTap K A v i-E'=routeTap (K-p) A v i:=by unfold routeTap E'; unfold routeTap; simp_rw [Matrix.sub_apply,sub_mul,sum_sub_distrib]
       rw [mul_add,hy1]; apply (add_le_add (riseC _ _ _ _ hA hv hz) (pad_layers Ω hp hs ha A b hA _ _ i)).trans; apply le_of_eq ?_ |>.trans (mul_le_mul_of_nonneg_left hq (show 0 ≤ (V'+A')*b from ?_))
       · unfold V';ring
       unfold V' A'; have hx:= zero_le_one.trans (widthCost_ge hs k); positivity
omit [MeasurableSpace E] [BorelSpace E] in
lemma extPay (P:Script I (e+d+1))(T:Script I (u+(n+1)))(i j:Site N)(x:Q!)(v:Fin (n+1))(h: Cold i j (Oriel L Z) c k)(hc:0≤c)(hp:soot k P b)(he:soot k T w):
    let hT:=orchestra T j
    let Q:= ∑ a:K!,FTl e d (orchestra P i) x x (deltaH a) Z * φx x x Z hT (L.inverse (Ferry Z a)) v
    BeamS (grain N k • Q) ((3:ℝ)^k*c*b*w) (clockY x Z) (e+d+(u+n)):=by
       intro U Q; refine ⟨Bond.scale _ (Sumbond _ _ fun i _=>(show Bond _ from FTc ..).mul (φBond ..)),fun z=>?_⟩; let C:= (3:ℝ)^k *c*b*w; let A:= cue (x+Z z) x e d; let B:= cue (x+Z z) x u n; let P':=orientY u n T v; let H:= clockY x Z z; have hH:0 ≤ H:= le_trans zero_le_one (tallY Z x z); let X:=Oriel L Z; have hh: soot k P' w:=slice_fee _ _ he
       have ha : Q z = drawP X P P' A B i j:=by
          unfold Q drawP; rw [Finset.sum_apply]; refine sum_congr rfl fun a _=>?_ ; let y:=deltaH a; rw [Pi.mul_apply,frontier,Finset.mul_sum]; refine sum_congr rfl fun t _=>?_ ; let W:= cue (x+Z z) x u (n+1); let y':=deltaH t; have hW:U (Function.update W (pinT v) y')=scribe j P' (Fin.cons y' B):=by rw [scriptV j T _ (sootS he)]; unfold P' orientY;rw [slice_pay, show Function.update W _ _= _ from cull (e:=u) (x+Z z) x y' v] -- W left
          rw [show FTl _ _ _ _ _ _ _ _= _ from scriptV i P (Fin.cons y A) (sootS hp), hW]; ring
       rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (zero_le_one.trans (grain_b _)), ha]; refine (herdC _ _ _ _ _ _ _ h hc hp hh).trans ?_; have hp' {k m:ℕ}: (∏ i:Fin (k+m), ‖cue (x+Z z) x k m i‖) ≤ H^(k+m):=(prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> cuePad x Z z i)).trans_eq (by rw [prod_const,card_univ,Fintype.card_fin]); have hT :0 ≤ C:=by unfold C; have ht:= Sack.coins hp;have hU:= Sack.coins he;positivity
       change C*(∏ i, ‖A i‖)*(∏ i, ‖B i‖) ≤ C*H^(e+d+(u+n)); rw [pow_add,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul hp' hp' (prod_nonneg (fun _ _=> norm_nonneg _)) (pow_nonneg hH _)) hT
end YM.OPE.Libra.Shell
