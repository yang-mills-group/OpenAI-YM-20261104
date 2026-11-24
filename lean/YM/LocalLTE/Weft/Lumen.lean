import YM.LocalLTE.Weft.Gem
/-! On the auxiliary torus weights. Subtract constants before scaling coupling.
Scalar here the chart constant only for comparing stencil. Overall scalar in Peg exact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Uniform
variable {G : Gauge} {L c f : Side} {K : KernelChoices} {σ σ' τ τ' ℒ α ν d M : ℝ} {g' : ℝ→ℝ} {q : Teller G}
variable {E :Type} [NormedAddCommGroup E][NormedSpace ℝ E]{i j n m:ℕ}
open Weft Tensor
lemma centerArp {f:ℝ→E→ℝ}(h: Arp j n d f): Arp j n (d+d) (fun s=>off (f s)):=by
    let g s (i:E):=(fun q : ℝ=> f q i) s
    refine ⟨Hex.invert (fun i=> ((h.hex.use i).add ((h.hex.use 0).oneZ (-1))).change ?_), ?_⟩
    · intro s hs; unfold off; simp [sub_eq_add_neg]
    intro s hs; let u:= f s 0; have hz:‖u‖≤d:=by have he:= h.brush s hs; simpa only [smul_zero] using! he.bound
    exact (h.brush s hs).separating ((Brush.certified zero_le_one u).climb hz le_rfl)
lemma centerStem (x:E→ℝ)(i:ℕ)(h:ContDiffAt ℝ (↑i) x 0): Shellac.off (stem i x)= stem i (Shellac.off x):=by
   unfold off stem; funext y; rw [Pi.sub_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,← Finset.sum_sub_distrib]; apply sum_congr rfl; intro j hj; cases j with
   | zero=> simp [Tensor.diagonal,coeff_apply_zero]
   | succ j=>
      rw [show Tensor.diagonal (coeff x (j+1) 0) 0=0 from (coeff x (j+1) 0).map_coord_zero (0:Fin (j+1)) rfl,sub_zero]; unfold Tensor.coeff; rw [iteratedFDeriv_sub_apply (h.of_le (by exact_mod_cast (Finset.mem_range.mp hj).le)) contDiffAt_const, iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]
lemma centerPrice {x:E→ℝ} (h:0 ≤ d)(hp:ContDiffAt ℝ n x 0)(hD:∀ i≤n,0 < i→ normJ i x 0≤d) : Brush n d 1 (Shellac.off x) 0:=by
    apply Brush.offer.mpr; refine ⟨hp.sub contDiffAt_const,?_⟩; intro i hi; unfold off normJ; cases i with
    | zero=>rw [norm_iteratedFDeriv_zero]; simp [h]
    | succ i=> rw [iteratedFDeriv_sub_apply (hp.of_le (by exact_mod_cast hi)) contDiffAt_const, iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]; exact hD _ hi (by omega)
def pollenT (j n:ℕ)(f:ℝ):= (n:ℝ)*(f*2^n*(1+(n:ℝ))^j)
lemma centerCed (f:E→ℝ) (n m:ℕ)(hp:i+1≤n) (hC0: 0≤d)(hF:ContDiffAt ℝ n f 0) (hC: fderiv ℝ f 0=0)(hd: ∀ p≤n,0 < p → normJ p f 0≤d) : Arp (2+(i+1)) m (pollenT m (i+1) d) (fun s=> (s^2)⁻¹ • Shellac.off (stem (i+1) f)) :=by
    let g:= Shellac.off f
    have hg:Null 2 n g:=by
       intro i hi hv; apply norm_le_zero_iff.mp; rcases (show i=0∨ i=1 from by omega) with H|H <;> subst i
       · rw [norm_iteratedFDeriv_zero]; simp [g,Shellac.off]
       rw [norm_iteratedFDeriv_one]; unfold g off; rw [fderiv_sub (hF.differentiableAt (by exact_mod_cast (show n≠0 by omega))) (differentiableAt_const (f 0)),hC]; simp
    have h:=Arp.reduced (h:=centerPrice hC0 hF hd) hg; let t:= ContinuousLinearMap.id ℝ E
    refine (Arp.streamH (0:E) (by simp) (show ‖t‖≤1 from ContinuousLinearMap.norm_id_le) m h hp).adjust (fun s hs=>?_); rw [centerStem _ _ (hF.of_le (by exact_mod_cast hp))]; funext x; simp only [smul_zero,zero_add,Pi.smul_apply]; unfold stem; rw [Finset.sum_apply,Finset.sum_apply,Finset.smul_sum]
    refine sum_congr rfl fun i hi=>?_ ; rw [Tensor.coeff_smul _ ((centerPrice hC0 hF hd).smooth.of_le (by exact_mod_cast (Finset.mem_range.mp hi).le.trans hp))]; rfl
variable {S : StepData c f} (F:Forest S.ratio) (T:Tube G S) (Q:ChartRatio G) (ρ: Bid.Dir G c→AxisChart G F) (d:ℝ)(γ:ℝ)(k:S.Choices) {V W U r:ℝ}
open Frame
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Φ" => song F T Q ρ d γ k
def pollens (n j:ℕ)(U V W:ℝ) := (pollenT j (n+1) U+pollenT j (n+1) U + pollenT j (n+3) V)+ pollenT j (n+1) W
lemma rays {n n':ℕ} (j:ℕ)(h:n+3 ≤ n') (_hp: 0≤U)(hz:0≤V)(hv:0≤W)(hJ:Brush n' U 1 (joint F T Q ρ d k) 0)
    (hc:ContDiffAt ℝ n' (cedar F T ρ k) 0)(hF:fderiv ℝ (cedar F T ρ k) 0=0)(hs:∀ i ≤ n',0 < i→ normJ i (cedar F T ρ k) 0 ≤ V)(hu:ContDiffAt ℝ n' (shed F T Q ρ γ k) 0)(hh:∀ i≤n',0 < i → normJ i (shed F T Q ρ γ k) 0≤ W): Arp (2+(n+3)) j (pollens n j U V W) (fun s:ℝ=> Shellac.off (song F T Q ρ d γ k n s)):= by
   let L:=ContinuousLinearMap.inr ℝ ℝ Xs; let t:= ContinuousLinearMap.id ℝ Xs
   have hz': ‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>by simp [L]; -- edit
   let u:=((1:ℝ),(0:Xs)) -- edit
   have he:= centerArp (Arp.streamH u (by unfold u; simp) hz' j (Arp.still hJ) (show n+1≤ n' by omega));
   have hf:= centerCed (cedar F T ρ k) n' j (show (n+2)+1≤ n' by omega) hz hc hF hs
   have H:= Arp.streamH (0:Xs) (by simp) (show ‖t‖≤1 from ContinuousLinearMap.norm_id_le) j (Arp.still (centerPrice hv hu hh)) (show n+1 ≤ n' from by omega)
   refine ((((he.sumAdd hf).sumAdd H).climb (by omega) le_rfl)).adjust (fun s hs=> ?_)
   rw [← centerStem _ _ (hu.of_le (by exact_mod_cast (show n+1≤n' by omega)))]
   funext x; unfold off song; simp only [Pi.smul_apply,smul_zero,zero_add,smul_eq_mul,Pi.add_apply,Pi.sub_apply]; dsimp only [u,L,t]; simp [inv_pow]; ring -- edit
end YM.LocalLTE.FrameBox.Hall
