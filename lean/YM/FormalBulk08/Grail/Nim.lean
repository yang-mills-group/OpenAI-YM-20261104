import YM.FormalBulk08.Grail.Led

/-! Pencil calculus in source slots. Revenue from gauge or Lens.
No quotient on fields. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{I X: Type*}[NormedAddCommGroup X]{m d n l r:ℕ}{A B σ:ℝ}{a:Loc G 1}

lemma exponent_goods (o:I)(f: chain (Biglot I) m→ X)(M:ℕ)(B:ℝ)(hb:0≤B)
    (h:∀ v, ‖f v‖≤ B*(1+herb (fame I) (0,o) v)^M)(p : 0 < σ)(T:Tile (Biglot I) m)(H:Knoxville (fame _) σ (0,o) T A):
    Summable (fun i=> ‖T i‖*‖f i‖) ∧ (∑' i, ‖T i‖*‖f i‖) ≤ B*widthCost σ M*A := by
    have hp:= zero_le_one.trans (widthCost_ge p M); obtain ⟨hS,he⟩:=penn_amount H
    let F i:= Real.exp (σ * herb (fame I) (0,o) i)*‖T i‖; let C:=B*widthCost σ M; have hc:0≤C:=mul_nonneg hb hp
    have hh i:‖T i‖*‖f i‖ ≤ C*F i:= by
       refine (mul_le_mul_of_nonneg_left ((h i).trans (mul_le_mul_of_nonneg_left (widthBill σ p M _ (Nat.cast_nonneg _)) hb)) (norm_nonneg _)).trans_eq ?_; unfold C F; ring
    have hg:=Summable.of_nonneg_of_le (fun i=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) hh (hS.mul_left C)
    refine ⟨hg,(hg.tsum_le_tsum hh (hS.mul_left C)).trans ?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he hc

-- uniform DP price on rows. Global polynomial probes grade.
def assigns (f:Place.Potential G) (v:edgeL G):ℝ:= f (Place.seat v.1) (bearing v) v.2.2

def tariffs (S: Fin r→edgeL G→ℝ) (T:Tile (edgeL G) r) := ∑' v:chain (edgeL G) r,T v* ∏ i,S i (v i)

def Stipend (f:edgeL G→ℝ) := ∃ B:ℝ,∃ n:ℕ,0≤ B ∧ ∀ i, ‖f i‖ ≤ B*liftCost n i.1
lemma shoulder {f: Place.Potential G}(h:f∈rangeLt (Axis→G.Color) n): Stipend (assigns f):= by
    obtain ⟨B,hb,H⟩:= royalties _ f h; refine ⟨B,n,hb,fun i=>?_⟩; let v:= f (Place.seat i.1) (bearing i); unfold assigns
    apply le_trans _ (H i.1 (bearing i)); rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ _ _]; exact (norm_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one,one_mul];rfl)

lemma pays_product (S: Fin r→edgeL G→ℝ)(o:Loc G 1)(hs:0<σ) (h:∀ i,Stipend (S i)):∃ B:ℝ,0≤B∧∀ T:Tile (edgeL G) r,∀ A:ℝ, Knoxville (fame _) σ (0,o) T A→
     Summable (fun v:chain (edgeL G) r=> T v* ∏ i,S i (v i)) ∧ ‖tariffs S T‖ ≤ B*A:= by
   choose B k hp hz using h; let C:= ∏ i,B i; let m:=∑ i,k i; let f (v:chain (edgeL G) r):=∏ i,S i (v i)
   have hc:0≤C:= Finset.prod_nonneg (fun i _=> hp i)
   have ht(v:chain (edgeL G) r): ‖f v‖≤ C*(1+(herb (fame _) (0,o) v:ℝ))^m:= by
      unfold f; rw [norm_prod]
      let u:ℝ:=herb (fame _) (0,o) v
      calc
         _ ≤ ∏ i,(B i*(1+u)^k i):= Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>?_)
         _ = _:= by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
      -- scope rewrite (calc product parentheses)
      apply (hz _ _).trans (mul_le_mul_of_nonneg_left _ (hp i)); unfold liftCost u; gcongr; apply seat_ink
   refine ⟨C*widthCost σ m,mul_nonneg hc (zero_le_one.trans (widthCost_ge hs _)),fun T A hT=>?_⟩
   obtain ⟨H,hH⟩:=exponent_goods o f m C hc ht hs T hT; let g i:= T i*f i; have hx : Summable (fun v=>‖g v‖):=by unfold g;simp_rw [_root_.norm_mul]; exact H
   refine ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ?_⟩; unfold g;simp_rw [_root_.norm_mul];exact hH

lemma tariff_turn (S: Fin r→edgeL G→ℝ)(T:Tile (edgeL G) r)(h:Agate T)(s:Equiv.Perm (Fin r)):tariffs (S ∘ s) T=tariffs S T:=by
    unfold tariffs; let f := Equiv.arrowCongr s.symm (Equiv.refl (edgeL G)); rw [← Equiv.tsum_eq f (fun v=> T v * ∏ i,(S ∘ s) i (v i))]; apply tsum_congr; intro i; change T (i ∘ s) * (∏ j,S (s j) _)=_; rw [h i s]; congr 1; exact Fintype.prod_equiv s _ _ fun j=>rfl

end YM.FormalBulk08.Grail
