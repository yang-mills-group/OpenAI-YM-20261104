import YM.OPE.Compatible.Broma.Bopo
/-!
# Polynomial-geometric wealth
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose
variable {n c f:Side}{I J M E F Z:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
section
variable [NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup Z]
variable {T W:M→ℝ}
def Wealth (p:M→ E)(T W:M→ℝ):Prop:=∃ C:ℝ,0≤C ∧∃ k:ℕ,∀ i, ‖p i‖ ≤ C*T i^k*W i
lemma fortSum {p q:M→E}(h: Wealth p T W)(hp:Wealth q T W)(ht:1≤ T)(hw:0≤W):Wealth (p+q) T W:=by
      obtain ⟨c,hc,k,H⟩:=h; obtain ⟨b,hb,d,h⟩:=hp
      refine ⟨c+b,by positivity,k+d,fun i=>?_⟩;rw [add_mul,add_mul]; apply (norm_add_le ..).trans; refine add_le_add ((H i).trans (mul_le_mul_of_nonneg_right ?_ (hw i))) ((h i).trans (mul_le_mul_of_nonneg_right ?_ (hw i))); exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ht i) (by omega)) hc; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ht i) (by omega)) hb
lemma fortNeg {p:M→E}(h:Wealth p T W):Wealth (-p) T W:=by simpa only [Wealth,Pi.neg_apply,norm_neg] using h
lemma LoanFrom {p:M→stave m i I}(h: Loan m (fun i':M=>seed m i I (p i')) W T) : Wealth p T W:=by obtain ⟨c,h,k,H⟩:=h; exact ⟨c,h,k,fun i'=>by rw [← (sprig m i (p i')).tsum_eq]; exact (H i').2.2⟩
lemma points_we [Fintype I]{E:I→Type} [∀ i,NormedAddCommGroup (E i)] (p:M→((i:I)→E i))(h:∀ i, Wealth (fun j=>p j i) T W)(ht:1≤ T)(hw:0≤ W): Wealth p T W:=by
     choose C hc k H using h; let B:=∑ i,C i; have hb:0≤B:=sum_nonneg fun _ _=>hc _; let s:=∑ i,k i; refine ⟨B,hb,s,fun i=>?_⟩; have hs : 0 ≤ T i:=zero_le_one.trans (ht i); apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hb (pow_nonneg hs _)) (hw i))).mpr; intro j; exact (H j i).trans (mul_le_mul_of_nonneg_right (mul_le_mul (single_le_sum (fun i _=>hc i) (mem_univ _)) (pow_le_pow_right₀ (ht i) (single_le_sum (fun i _=>Nat.zero_le (k i)) (mem_univ _))) (pow_nonneg hs _) hb) (hw i))
lemma wealthZ (T W:M→ℝ):Wealth (0:M→E) T W:= ⟨0,le_rfl,0,by simp⟩
lemma wealthset (s : Finset J)(p:M→J→ E)(hx:∀ j∈s, Wealth (fun i=> p i j) T W)(ht:1≤ T)(hw:0≤ W): Wealth (fun i=> ∑ j∈s,p i j) T W:=by induction s using Finset.induction_on with | empty=>simp_rw [Finset.sum_empty]; exact wealthZ ..| insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact fortSum (hx _ (Finset.mem_insert_self ..)) (ih fun j hj=> hx j (mem_insert_of_mem hj)) ht hw
lemma wealth_mul {p:M→E}{q:M→F}{g:M→Z}{x y z:M→ℝ}(h: Wealth p x y)(hp:Wealth q x z)(ht:∀ i,‖g i‖≤‖p i‖*‖q i‖): Wealth g x (y*z):=by obtain ⟨c,hc,k,H⟩:=h; obtain ⟨d,hd,n,hD⟩:= hp; refine ⟨c*d,mul_nonneg hc hd,k+n,fun i=>?_⟩; exact (ht i).trans ((mul_le_mul (H i) (hD i) (norm_nonneg _) ((norm_nonneg _).trans (H i))).trans_eq (by rw [Pi.mul_apply,pow_add]; ring))
structure Brim (X Y:M→E)(T W:M→ℝ):Prop where
     A: Wealth X T 1
     B: Wealth Y T 1
     D: Wealth (X-Y) T W
lemma brimL {p q:M→ Seat d m I}(h:∀ j:ℕ, Auger m (fun i=>lilies m d I (p i) j) (fun i=>lilies m d I (q i) j) W T)(ht:1≤ T)(hw:0≤W): Brim p q T W:=by
      have he(f:Seat d m I)(i:Fin (d+1)): lilies m d I f i.val=seed m i.val I (f i):=by rw [soup,moduleAt,dif_pos (Nat.le_of_lt_succ i.isLt)];rfl
      refine ⟨points_we p (fun i=>LoanFrom (m:=m) ?_) ht zero_le_one, points_we q (fun i=>LoanFrom (m:=m) ?_) ht zero_le_one,points_we _ (fun i=> LoanFrom (m:=m) ?_) ht hw⟩
      · simp_rw [← he]; exact (h i.val).A -- maybe univ
      · simp_rw [← he]; exact (h i.val).B
      rw [show (fun j=>seed m i.val I ((p-q) j i))=(fun j=>lilies _ d I (p j) i.val)-(fun j=>lilies _ d I (q j) i.val) from funext fun j=>by rw [← he, Pi.sub_apply,map_sub];rfl]; exact (h i.val).D
variable [NormedSpace ℝ E][NormedSpace ℝ F]
lemma grantV (p:M→E→L[ℝ] F)(h: Wealth (fun i: M× (Metric.closedBall (0:E) 1)=> p i.1 i.2.val) (T ∘ Prod.fst) (W∘ Prod.fst))(ht:1≤ T)(hw:0≤ W): Wealth p T W:=by
      obtain ⟨c,hc,k,H⟩:=h; refine ⟨c,hc,k,fun i=>?_⟩; let d:=c*T i^k* W i; have he :0 ≤ d:=mul_nonneg (mul_nonneg hc (pow_nonneg (zero_le_one.trans (ht i)) _)) (hw i); apply (p i).opNorm_le_bound he; intro x; by_cases hp:x=0
      · subst x;simp
      let s:= ‖x‖; have hs:0<s:= norm_pos_iff.mpr hp; have hz:s⁻¹ • x ∈ Metric.closedBall (0:E) 1:=by rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), inv_mul_cancel₀ hs.ne']
      have hu:‖p i (s⁻¹ • x)‖≤ d:= H (i, ⟨_,hz⟩); rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),←div_eq_inv_mul] at hu; exact (div_le_iff₀ hs).mp hu
end
end YM.OPE.Drift
