import YM.OPE.Compatible.Cum.Hors
/-!
# period heurks. Definition uses powers up to fixed k. costs bounds.
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
local notation "W"=> E→ℝ
variable {u v:J→ℕ}{Q:∀ i:J,Script I (v i+u i)}{X:J→Option (Site N)} {a b:Site N}{c:ℝ}{Z:E→L[ℝ] deck I N} {Ω:Row I I}{C:ℕ→ℝ} [DecidableEq J]
def StepN (i j a b:Site N)(m:ℕ):ℝ:= (1+(separation i a:ℝ)+ (separation j b:ℝ))^m
def Cold (i j:Site N)(M:Matrix K! K! ℝ)(C:ℝ)(m:ℕ):Prop:= ∀ p q: Flume.Script.Tab I N, (N.val:ℝ)^m*‖M p q‖ ≤ StepN p.1 q.1 i j m *C
structure Fund (m:ℕ) (j:Site N) (Ω:Row I I)(L:Law E)(C:ℕ→ℝ)(Z:E→L[ℝ] deck I N):Prop where
   alive : Sustains L Z (C 0)
   pulse i (h:i≤m) : Cold j j (Oriel L Z-Ω.acts N) (C i) i
variable {s:Finset J}
def LightX (K:Option (Site N)):Bool:= !K.isSome
def Globe (p:ℕ)(s: Option (Site N))(x: deck I N)(f:Script I p)(Ω:Row I I)(L:Law E)(C:ℕ→ℝ)(Z:E→L[ℝ] deck I N)(d:Site N)(c:ℝ)(k:ℕ): Prop:= match s with | none=> Rookie L Z Ω x f c | some j=> ∀ i ≤ k, Cold d j (Oriel L Z) (C i) i
variable {p e k d t:ℕ}
def Vx (q:Option (Site N))(T:Script I p)(c:ℝ): Tensor.T Q! ℝ p:=match q with | none=> c • listV T N | some Q=> orchestra T Q
def Fig (u v:J→ℕ)(Q:∀ i:J,Script I (v i+u i))(X:J→Option (Site N))(c:ℝ)(x:deck I N)(Z:E→L[ℝ] deck I N):=story u v (fun i=>Vx (X i) (Q i) c) x x Z
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] [DecidableEq J] in
lemma pay_face (x: Fin d→ deck I N)(b:ℝ)(S:Script I d)(y:ℝ)(hb:0 ≤ b)(hx: soot k S y)(hp:∀ i,‖x i‖≤b)(j:Site N): ‖scribe j S x‖ ≤ y*b^d :=by
     unfold scribe; apply (norm_tsum_le_tsum_norm (instruments S (sootS hx) j x).summable.norm).trans; apply (((instruments S (sootS hx) j x).summable.norm).tsum_le_tsum ?_ (hx.2.1.mul_right (b^d))).trans
     · rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hx.2.2 (pow_nonneg hb _)
     intro i; rw [norm_mul]; apply mul_le_mul _ _ (norm_nonneg _) (mul_nonneg (zero_le_one.trans (payer k i)) (norm_nonneg _)); exact le_mul_of_one_le_left (norm_nonneg _) (payer k i); unfold render; rw [norm_prod]; apply (prod_le_prod (s:=univ) _ (show ∀ j∈univ, _ from fun j hj=>(norm_le_pi_norm (x j) _).trans (hp j))).trans_eq; · simp
     exact fun _ _=> norm_nonneg _
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma cuePad (x: Q!) (Z:E→L[ℝ] deck I N)(i:E)(j:Fin (e+d)): ‖cue (x+ Z i) x e d j‖≤ clockY x Z i:=by
    unfold cue clockY; split; · apply (norm_add_le ..).trans; linarith
    linarith [norm_nonneg (Z i)]
omit [DecidableEq J][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma Xspot (P:Script I (e+d))(x: Q!)(z:Site N)(h: soot k P c): BeamS (SX (e:=e) (d:=d) x x Z (orchestra P z)) c (clockY x Z) (e+d):=by
      refine ⟨cueBond x x Z _,fun i=>?_⟩; unfold SX;rw [scriptV z P _ (sootS h)]; exact pay_face _ _ P _ (zero_le_one.trans (tallY Z x i)) h (cuePad x _ i) z
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E][DecidableEq J] in
lemma faded (x:Q!)(p:Script I (e+d))(z: Option (Site N))(c' D:ℝ)(h:‖c'‖≤1)(hp:soot k p D):BeamS (SX (e:=e) (d:=d) x x Z (Vx z p c')) (grain N 4 * D) (clockY x Z) (e+d):=by
       have hd:0≤D:= Sack.coins hp; rcases z with _|z
       · refine ⟨cueBond ..,fun i=>?_⟩; unfold SX; change ‖c'*listV p N _‖≤ _; rw [norm_mul,muses p (sootS hp)]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) h); unfold library; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun j _=> pay_face _ _ p _ (zero_le_one.trans (tallY Z x i)) hp (cuePad x Z i) j)).trans_eq; rw [sum_const,card_univ,site_card,nsmul_eq_mul]; unfold grain;push_cast;ring
       have hx := Xspot p x z hp (Z:=Z) (e:=e) (d:=d); exact ⟨hx.1,fun i=>(hx.2 i).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hd (grain_b 4)) (pow_nonneg (zero_le_one.trans (tallY Z x i)) _))⟩
omit [DecidableEq J][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma plotme (x:Q!)(s:Finset J)(w:J→ℝ)(ha:‖c‖≤1)(h: coversB u v Q k w s): Prone (Fig u v Q X c x Z) (v+u) w (clockY x Z) (grain N 4) s:= fun i hi=> ⟨Sack.coins (h i hi),faded x _ _ _ _ ha (h i hi)⟩
end YM.OPE.Libra.Shell
