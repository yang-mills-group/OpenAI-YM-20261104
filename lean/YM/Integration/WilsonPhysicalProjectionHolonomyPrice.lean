import YM.FormalBulk08.Pose.Alto

/-! Spatial width dependence of the genuine holonomy jets used in the signed detector. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalProjectionHolonomyPrice
open Function Filter Finset Lattice Laurent Gauge Wilson Exterior Stationary
open FormalBulk08 FormalBulk08.Lava FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Gorge FormalBulk08.Shore
open FormalBulk08.City FormalBulk08.Kemp FormalBulk08.Rift FormalBulk08.Pose FormalBulk08.Orb
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {r d n:ℕ}

/-- A single derivative tariff for the actual ordered radial product, before the varying mesh width. -/
theorem tier_price (p:Loc G 1) (r d n:ℕ):
    ∃ C:ℝ,0≤C ∧ ∀η:ℝ,0<η → ∀(x:Fin n→Snap G d) (v:chain (edgeL G) r),
      ‖Tensor.coeff (tier (d:=d) v) n 0 x‖ ≤ C*widthCost η (d*n)*
        Real.exp (η*herb (fame _) (0,p) v)*∏i,‖x i‖:=by
   let u t:= ‖iteratedFDeriv ℝ n (nacre (r:=r) (G:=G) (d:=d) t) 0‖
   let c:=∑ t,u t;have hc:0≤c:=by unfold c; exact Finset.sum_nonneg (fun i _=>norm_nonneg _)
   let a:ℝ:=(n.factorial:ℝ)⁻¹
   refine ⟨a*c,mul_nonneg (by unfold a; positivity) hc,?_⟩
   intro η hs Y v
   let b:=widthCost η (d*n)
   let w:Fin r→hue G:=fun i=>(v i).2.2
   let L : Snap G d →L[ℝ] (Fin r → EdgeRead G d) := tileCons v d
   have he : tier (d:=d) v=nacre w ∘ L:=rfl
   have hv : iteratedFDeriv ℝ n (tier (d:=d) v) 0=(iteratedFDeriv ℝ n (nacre (d:=d) w) 0).compContinuousLinearMap fun _=>L:= by
     rw [he]
     exact jets_linear (X:=Snap G d) (E:=Fin r→EdgeRead G d) (F:=ℝ) (f:=nacre (d:=d) w) (k:=n) L ((nacre_diff (d:=d) w).of_le le_top)
   let x:ℝ:=herb (fame _) (0,p) v; have hx:0≤x:=Nat.cast_nonneg _
   rw [Tensor.coeff,hv, _root_.smul_apply,norm_smul, Real.norm_of_nonneg (by positivity)]
   have he' : ‖(iteratedFDeriv ℝ n (nacre (d:=d) w) 0) (L ∘ Y)‖≤c*(Real.exp (η*x) * b * ∏ i,‖Y i‖):= by
      apply ((iteratedFDeriv ℝ n (nacre w) 0).le_opNorm _).trans
      apply mul_le_mul (show u w ≤ _ from Finset.single_le_sum (f:=u) (fun i _=>norm_nonneg _) (Finset.mem_univ _)) _ (by positivity) hc
      apply (Finset.prod_le_prod (g:=fun i : Fin n=> (1+x)^d* ‖Y i‖) (fun _ _=>norm_nonneg _) (fun i _=>sheet_cost p v (Y i))).trans;rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, ←pow_mul]; exact mul_le_mul_of_nonneg_right ((widthBill η hs _ _ hx).trans_eq (mul_comm b _)) (by positivity)
   apply (mul_le_mul_of_nonneg_left he' (show 0≤a by unfold a; positivity)).trans_eq;unfold a x b; ac_rfl

theorem slate_price (p:Loc G 1) (r d n:ℕ):
    ∃C:ℝ,0≤C ∧ ∀η:ℝ,0<η → ∀(T:Tile (edgeL G) r) (A:ℝ),
      Knoxville (fame _) η (0,p) T A → ∀x:Fin n→Snap G d,
        ‖slate T d n x‖≤C*widthCost η (d*n)*A*∏i,‖x i‖:=by
  obtain ⟨C,C0,H⟩:=tier_price p r d n
  refine ⟨C,C0,?_⟩
  intro η pos T A ht x
  let B:=C*widthCost η (d*n)
  have B0:0≤B:=mul_nonneg C0 (zero_le_one.trans (widthCost_ge pos _))
  let z:=∏i,‖x i‖
  have z0:0≤z:=by dsimp [z]; positivity
  obtain ⟨hp,he⟩:=penn_amount ht
  let f v:=T v*Tensor.coeff (tier (d:=d) v) n 0 x
  have bound v:‖f v‖≤B*z*(Real.exp (η*herb (fame _) (0,p) v)*‖T v‖):=by
    dsimp only [f];rw [_root_.norm_mul]
    exact (mul_le_mul_of_nonneg_left (H η pos x v) (norm_nonneg _)).trans_eq (by dsimp [B,z];ring)
  have total:Summable (fun v=>‖f v‖):=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) bound (hp.mul_left (B*z))
  rw [slate_read p T x pos ht]
  apply (norm_tsum_le_tsum_norm total).trans ((total.tsum_le_tsum bound (hp.mul_left _)).trans ?_)
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left he (mul_nonneg B0 z0)).trans_eq (mul_right_comm ..)

/-- The authentic readout uses its submitted color tensor and slot count on both sides. -/
theorem entered (F:Frame G d) (p:Loc G 1) (row:Letter F) (r:ℕ):
    ∃C:ℝ,0≤C ∧ ∀η:ℝ,0<η → ∀(T:Tile (edgeL G) r) (A:ℝ),
      Knoxville (fame _) η (0,p) T A →
      |pearlJ F T (mint F row)|≤C*widthCost η (d*slots F row)*A:=by
  obtain ⟨K,K0,H⟩:=pocket_cost F (label F row) (slots F row) (mint F row)
  obtain ⟨B,B0,L⟩:=slate_price p r d (slots F row)
  refine ⟨K*B,mul_nonneg K0 B0,?_⟩
  intro η pos T A ht
  have non:0≤B*widthCost η (d*slots F row)*A:=
    mul_nonneg (mul_nonneg B0 (zero_le_one.trans (widthCost_ge pos _))) ht.1
  exact (Complex.abs_re_le_norm _).trans ((H _ _ non (L η pos T A ht)).trans_eq (by ring))

end YM.Integration.WilsonPhysicalProjectionHolonomyPrice
