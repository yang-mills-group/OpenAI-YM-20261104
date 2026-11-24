import YM.FormalBulk08.Sable.Loaf

/-! Projection duality with full polynomial moment. Native-unit reads.
No assumption about support measures before the projection. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {I:Type} {o:Loc G 1}{u m n d r:ℕ} {η A B :ℝ}
def Footing (f:edgeL G→ℝ) (m:ℕ) := ∃ B:ℝ,0≤B ∧ ∀ i,‖f i‖≤ B*liftCost m i.1
lemma tread_m {f:edgeL G→ℝ}(h:Footing f m)(e:m≤n): Footing f n:= by
    obtain ⟨B,hb,H⟩:=h; exact ⟨B,hb,fun i=> (H i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) e) hb)⟩
lemma foot_stip {f:edgeL G→ℝ}(h:Footing f m):Stipend f:= by obtain ⟨B,h⟩:=h; exact ⟨B,m,h⟩
lemma turf_f {f: Place.Potential G}(h:f∈rangeLt (Axis→G.Color) n): Footing (assigns f) n:= by
    obtain ⟨B,hb,H⟩:= royalties _ f h; refine ⟨B,hb,fun i=>?_⟩; let v:= f (Place.seat i.1) (bearing i); unfold assigns
    apply le_trans _ (H i.1 (bearing i)); rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ _ _]; exact (norm_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one,one_mul];rfl)
lemma ground_f (f:E4→ G.Color)(h:f∈rangeLt G.Color n) : Footing (ground f) n := by
    obtain ⟨A,hA,H⟩:=band_growth h; refine ⟨_,hA,fun x=>?_⟩
    unfold Grail.ground; rw [←EuclideanSpace.basisFun_inner G.ColorIndex ℝ _ _]; apply le_trans (norm_inner_le_norm ..);rw [OrthonormalBasis.norm_eq_one,one_mul]; apply (H _).trans (mul_le_mul_of_nonneg_left _ hA); unfold liftCost; exact pow_le_pow_left₀ (by positivity) (by linarith [shade_seat x.1]) _
lemma shoe_patch (f:E4→G.Color)(h:f∈rangeLt G.Color n): Footing (patcher f) n:= by
    obtain ⟨B,hB,hF⟩:=ground_f f h
    refine ⟨_,hB,fun i=>?_⟩; unfold patcher;split;exact hF i
    rw [norm_zero]; exact mul_nonneg hB (liftCost_pos n i.1)
lemma jump_f (f:E4→G.Color)(h:f∈rangeLt G.Color (n+1)) : Footing (assigns (jump f)) n:= turf_f (jump_band h)

lemma room_goods (o:I)(f: chain (Biglot I) m→ℝ)(M:ℕ)(B:ℝ)(hb:0≤ B)
    (h:∀ v, ‖f v‖≤ B*(1+herb (fame I) (0,o) v)^M)(T:Tile (Biglot I) m)(H:Knoxville (grain (fame _) 1) M (0,o) T A):
    Summable (fun i=> ‖T i‖*‖f i‖) ∧ (∑' i,‖T i‖*‖f i‖)≤ B*A:= by
    obtain ⟨-,hS,he⟩:=particle H; simp only [_root_.YM.FormalBulk08.Sable.gauge,NNReal.coe_one,one_mul] at hS he
    have hh i:‖T i‖*‖f i‖≤ B*((1+(herb (fame I) (0,o) i:ℝ))^M*‖T i‖):= (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)).trans_eq (by ring)
    have hg:=Summable.of_nonneg_of_le (fun i=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) hh (hS.mul_left B)
    refine ⟨hg,(hg.tsum_le_tsum hh (hS.mul_left B)).trans ?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he hb
lemma weave (S:Fin r→edgeL G→ℝ)(o:Loc G 1)(h:∀ i,Footing (S i) m)(hb:r*m ≤ u) : ∃ B:ℝ,0≤B∧∀ T:Tile (edgeL G) r,∀ A:ℝ,Knoxville (grain (fame _) 1) u (0,o) T A → ‖tariffs S T‖ ≤ B*A:= by
   choose B hp hz using h; let C:= ∏ i,B i; let f (v:chain (edgeL G) r):=∏ i,S i (v i)
   have hc:0≤C:= Finset.prod_nonneg (fun i _=> hp i)
   have ht(v:chain (edgeL G) r): ‖f v‖≤ C*(1+(herb (fame _) (0,o) v:ℝ))^(r*m):= by
      unfold f; rw [norm_prod]
      let u:ℝ:=herb (fame _) (0,o) v
      calc
         _ ≤ ∏ i,(B i*(1+u)^m):= Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>?_)
         _ = _:= by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,mul_comm m r]
      apply (hz _ _).trans (mul_le_mul_of_nonneg_left _ (hp i)); unfold liftCost u;gcongr;exact seat_ink o v i
   refine ⟨C,hc,fun T A hT=>?_⟩
   obtain ⟨H,hH⟩:=room_goods o f (r*m) C hc ht T (penn_shrink hT (Nat.cast_le.mpr hb));let g i:=T i*f i; have hx:Summable (fun v=>‖g v‖):=by unfold g;simp_rw [_root_.norm_mul];exact H
   refine (norm_tsum_le_tsum_norm hx).trans ?_;unfold g;simp_rw [_root_.norm_mul];exact hH

/-! Legibility of axis stencil and readout pearls already in model. Price under polynomial budget. -/
lemma tier_price (p:Loc G 1)(r d n:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ (x : Fin n→Snap G d) (v:chain (edgeL G) r),
     ‖Tensor.coeff (tier (d:=d) v) n 0 x‖ ≤ C * gauge (d*n) 1 (herb (fame _) (0,p) v) *∏ i,‖x i‖ := by
   let u t:= ‖iteratedFDeriv ℝ n (nacre (r:=r) (G:=G) (d:=d) t) 0‖
   let c:=∑ t,u t;have hc:0≤c:=by unfold c; exact Finset.sum_nonneg (fun i _=>norm_nonneg _)
   let a:ℝ:=(n.factorial:ℝ)⁻¹
   refine ⟨a*c,mul_nonneg (by unfold a; positivity) hc,fun Y v=>?_⟩
   let w:=fun i=>(v i).2.2; let L := tileCons v d
   have he : tier (d:=d) v=nacre w ∘ L:=rfl
   have hv : iteratedFDeriv ℝ n (tier (d:=d) v) 0=(iteratedFDeriv ℝ n (nacre (d:=d) w) 0).compContinuousLinearMap fun _=>L:= by rw [he]; exact Next.Foundations.jets_linear L ((nacre_diff w).of_le le_top)
   let x:ℕ:=herb (fame _) (0,p) v
   rw [Tensor.coeff,hv, _root_.smul_apply,norm_smul, Real.norm_of_nonneg (by positivity)]
   have he' : ‖(iteratedFDeriv ℝ n (nacre (d:=d) w) 0) (L ∘ Y)‖≤c*(gauge (d*n) 1 x * ∏ i,‖Y i‖):= by
      apply ((iteratedFDeriv ℝ n (nacre w) 0).le_opNorm _).trans
      apply mul_le_mul (show u w ≤ _ from Finset.single_le_sum (f:=u) (fun i _=>norm_nonneg _) (Finset.mem_univ _)) _ (by positivity) hc
      apply (Finset.prod_le_prod (g:=fun i : Fin n=> (1+(x:ℝ))^d* ‖Y i‖) (fun _ _=>norm_nonneg _) (fun i _=>sheet_cost p v (Y i))).trans_eq; simp only [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, ←pow_mul, _root_.YM.FormalBulk08.Sable.gauge, NNReal.coe_one,one_mul]
   apply (mul_le_mul_of_nonneg_left he' (show 0≤a by unfold a; positivity)).trans_eq;unfold a x;ac_rfl
lemma slate_back (a:Loc G 1)(r d n:ℕ)(hs:d*n ≤ u):∃ C:ℝ,0≤C ∧ ∀ T:Tile (edgeL G) r,∀ A:ℝ, Knoxville (grain (fame _) 1) u (0,a) T A→∀ x:Fin n→Snap G d,
    let f v:= T v*(Tensor.coeff (tier (d:=d) v) n 0 x); Summable (fun v=> ‖f v‖) ∧ ‖∑' v,f v‖ ≤ C*A*∏ i,‖x i‖:= by
   obtain ⟨C,hC,H⟩:=tier_price a r d n; refine ⟨C,hC,fun T A h x=>?_⟩; intro f; let z:= ∏ i,‖x i‖; have hz:0≤z:=by unfold z; positivity
   obtain ⟨-,hp,he⟩:=particle (penn_shrink h (Nat.cast_le.mpr hs))
   have ht v:‖f v‖≤C*z*(gauge (d*n) 1 (herb (fame _) (0,a) v)*‖T v‖):= by unfold f; rw [_root_.norm_mul];refine (mul_le_mul_of_nonneg_left (H x v) (norm_nonneg _)).trans_eq ?_; unfold z;ring
   have hh:=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) ht (hp.mul_left (C*z))
   refine ⟨hh,(norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum ht (hp.mul_left _)).trans ?_)⟩
   rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left he (mul_nonneg hC hz)).trans_eq (mul_right_comm ..)
lemma slate_k (d n u:ℕ)(p:Loc G 1)(hs:d*n ≤ u)(T:Tile (edgeL G) r)(h:Knoxville (grain (fame _) 1) u (0,p) T B): ∀ x:Fin n→ Snap G d, slate T d n x = ∑' v,T v*Tensor.coeff (tier v) n 0 x:= by
    obtain ⟨C,hC,H⟩:= slate_back p r d n hs; have e : ∃ P:Slate G d n,∀ x,P x=∑' v,T v*(Tensor.coeff (tier (d:=d) v) n 0 x):= seal_sum n _ _ (C*B) (fun v=> (H T _ h v).1.of_norm) fun v=>(H T _ h v).2
    rw [slate,dif_pos e]; exact Classical.choose_spec e
lemma rent_book (F:Frame G d)(i:Letter F)(p:Loc G 1)(r:ℕ)(hs:d*d ≤ u):∃ C:ℝ,0≤C ∧∀ T:Tile (edgeL G) r,∀ A:ℝ,Knoxville (grain (fame _) 1) u (0,p) T A→ ‖pearlJ F T (mint F i)‖≤C*A:= by
    obtain ⟨C,hC,h⟩:=pocket_cost F (Pose.label F i) (Pose.slots F i) (mint F i)
    have he:d*Pose.slots F i ≤ u:= le_trans (Nat.mul_le_mul_left d (slotsFits ..)) hs
    obtain ⟨K,hK,H⟩:=slate_back p r d (Pose.slots F i) he; refine ⟨C*K,mul_nonneg hC hK,fun T A ht=>?_⟩; unfold pearlJ; apply (Complex.abs_re_le_norm _).trans; rw [mul_assoc]; exact h _ _ (mul_nonneg hK ht.1) (fun x=>by rw [slate_k _ _ _ _ he T ht]; exact (H T _ ht x).2)
end YM.FormalBulk08.Sable
