import YM.LocalLTE.Units.Seam
/-! Local kernel polynomial generator stable through authenticated masks. Uses m+1 extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c L : Side} {i p:ℕ} {o:Site c} (X:Grove o) {m:ℕ} {κ a l : ℝ}
open Cabana Grove
local notation "η" => Chi.canonical
local notation "Z" => neighbors m o
local notation "ι" => Directions G c
section price
open Blaze.March
variable {v V : Config G c} {Q:BudgetPoint} {f:Config G c→ℝ} {J:ℝ}
lemma powered (h:Agrees (Z:Set (Four (Per c))) v V)(hv:LocalOn Z f)(hp:∀ l:List (Directions G c), l.length≤ Q.order→ (∀ i∈l, ‖i‖ ≤ Q.threshold)→ ‖leftDerivs f l V‖ ≤ J) :
    ∀ l:List (Directions G c),l.length ≤ Q.order → (∀ i∈l,Q.dirBound o i) → ‖leftDerivs f l v‖ ≤ (1+(m:ℝ))^(Q.power*Q.order)*J := by
  intro l hl hx
  let Y:ℝ:=1+(m:ℝ); let t:=Y^Q.power; have ht:1≤Y:=by unfold Y; simp
  have ht':1 ≤ t:=one_le_pow₀ ht; have hu:= zero_lt_one.trans_le ht'
  let g (u: Directions G c)(e:Bond c):= if e.1∈Z then u e else 0; let l':=l.map g; let z:=l'.map fun i=> t⁻¹ • i
  have hh:l'=z.map (fun i=>t • i):=by unfold z; simp only [List.map_map,Function.comp_def,smul_smul,mul_inv_cancel₀ hu.ne',one_smul]; exact congr_fun List.map_id_fun.symm l'
  rw [stays hv l g (fun _ _ i hi=> if_pos hi) v V h]
  have hZ i (hi:i∈z): ‖i‖≤Q.threshold:=by
    obtain ⟨s,hS,rfl⟩:=List.mem_map.mp hi; obtain ⟨u,h'k,rfl⟩:= List.mem_map.mp hS; rw [norm_smul,norm_inv,Real.norm_of_nonneg hu.le]; have he :‖g u‖≤ Q.threshold*t := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg Q.threshold_pos.le hu.le)).2; intro e; unfold g; split
      next hh=>
        refine (hx u h'k e).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) Q.threshold_pos.le); unfold Y; gcongr; rw [separation_comm]; exact (neighbors_mem ..).1 hh
      rw [norm_zero]; exact mul_nonneg Q.threshold_pos.le hu.le
    rw [mul_comm]; apply (mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hu.le)).trans_eq; field_simp
  have hz:z.length=l.length:= by simp [z,l']
  have ht:= hp z (hz.trans_le hl) hZ
  change ‖leftDerivs f l' V‖ ≤ _; rw [hh,Blaze.March.expands,norm_smul,Real.norm_of_nonneg (by positivity : 0≤ t^z.length),pow_mul]
  exact mul_le_mul (pow_le_pow_right₀ ht' (hz.trans_le hl)) ht (norm_nonneg _) (pow_nonneg hu.le _)
end price
section
variable (G L){f:ℝ→ℕ}{k v w:ℝ} (hf:Rate G L 0 fun t=>(f t:ℝ))(hp: Reliable G κ k)(hV:w<v)(hw:v<0)
local notation "X'" => (fun t=> cone v (betaF G t L))
local notation "Y" => (fun t=> cone w (betaF G t L))
variable (hW : -(1/2:ℝ)<w) (hK:w<vow)
include hW hK hf hp hV hw
lemma minted (j p:ℕ) : ∃ E:ℝ→ℝ, Rate G L 0 E ∧ ∀ᶠ t in atTop, ∀ m z:ℕ,z≤ f t→ m+1≤z →∀ P:BudgetPoint, P.power=p → P.order=j →P.threshold=Pressure.temp t → P.threshold≤2*Pressure.fiery G t L →∀ (c:Side)(o:Site c)(_ :2*z < c.val)(h₂:2*(2*m)≤c.val), ∀ (X: Grove o)(d:ℕ)(F:Pkt (Directions G c) d)(U:Config G c→ℝ)(C:ℝ), 0≤C→ P.Regular (neighbors m o) U→
    (∀ x: Directions G c,‖x‖ < X' t → Fold.pullV o m h₂ (soloV x)∈ sunny P → Brush j C (X' t)⁻¹ (fun v=> U (soloV v)-Cabana.actual F v) x)→
    P.supBounds o (neighbors z o) (U-realise X m κ (colorP F)) (E t*C) := by
  let K t:= (1+(f t:ℝ))^(p*j)
  -- Blaze ticket. inspect syntax
  let L' :ℝ:= ticket j j.factorial
  have he:Rate G L 0 (fun t=> K t*L'):= by simpa only [K,zero_mul] using (((Rate.const 1).add hf).pow (p*j)).mul_right L'
  refine ⟨_,he,?_⟩
  filter_upwards [FrameBox.ticketed G L hf hp hV hw j,FrameBox.poll G L hf hW j p,Boulevard.equalityG G L hW hK j,Delay.shift_pos G L] with t hV h hp' hΩ m z hz hw P hi hP ht hF c o hx h₂ X d F U C hc hU hA
  let g:=U-realise X m κ (colorP F); have ha : P.Regular (neighbors m o) g:= AnalyticBridge.CouplingShape.reg_sub hU (legal X m hp F P)
  have hT:= hV m (by omega)
  refine ⟨mul_nonneg (mul_nonneg (by unfold K; positivity) (by unfold L' Boulevard.ticket; positivity)) hc, fun V he l hl hL=>?_⟩
  obtain ⟨k,S,hX,hS,hΥ⟩:= h m z hz hw P hi hP hF c o hx h₂ V he
  let A:=(1+(m:ℝ))^(P.power*P.order)*(ticket j (j.factorial*C))
  have hB (l:List (Directions G c))(he:l.length≤P.order)(hc':∀ u∈l,P.dirBound o u): ‖leftDerivs g l (gauge k V)‖≤ A:=by
    refine powered hΥ ha.sites (?_) l he hc'; intro a ha' hL;
    refine hp' P ht hF hP c S hS hX _ _ (j.factorial*C) ha (fun y hy hc => ?_) a ha' hL
    apply revisit X (Q:=F) (w:=C) hp hT h₂ hU hA y (lt_of_le_of_lt (le_add_of_nonneg_right (by unfold furl; positivity)) hy) hc
  change ‖leftDerivs g l _‖≤ _; rw [← Slide.traced k ha.symmetry]; refine (hB _ (by simpa) ?_).trans ?_
  · intro i hi; obtain ⟨i,hℓ,rfl⟩:= List.mem_map.mp hi; intro e; unfold Slide.plume; rw [norm_adjoint]; exact hL i hℓ _
  unfold A; rw [hi,hP]; unfold L' Boulevard.ticket; apply le_trans (mul_le_mul_of_nonneg_right (show (1+(m:ℝ))^(p*j) ≤ K t from (by unfold K; gcongr; omega)) (by positivity)); apply le_of_eq; ring
end
end YM.LocalLTE.FrameBox
