import YM.FormalBulk08.Grail.Wilk

/-! Full repeated estimate. λ assembly before L. M ≥n missing roots paid
only with lower caps. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J:Type}{G : Gauge}{m u d D j e :ℕ}{η σ θ B A C :ℝ}

lemma knight (x:Cover) (a: Loc G 1) (T:Tile (edgeL G) m)(h:Knoxville (fame _) η (0,a) T A): Knoxville (fame _) η (x,a) (Kemp.carries x T) A:= by convert mantle_pay x h using 1; exact Prod.ext (zero_add _).symm rfl

-- combine cash_part with horn. here North location coarse exactly at ancestor. Price all test powers q subtract at once.
lemma thorn_cost (b:Loc G 1)(m k:ℕ)(hs:0<σ)(hp:0≤η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ L:Side, Odd L.val → Threshold σ η m L → ∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C k → ∀ x:Site L,∀ T: Tile (edgeL G) m,∀ A B:ℝ, Knoxville (fame _) σ (0,b) T B → 0≤A → (∀ (i:chain (Loc G 1) m) t, t∈trimmed (Fin m×Axis) k → ‖tariffs (fun j:Fin m=> assigns (horn (aster t j) (i j))) T‖ ≤ A) →
     Knoxville (fame _) η (0,b) (upmost L x S T) (X*B*(L.val:ℝ)⁻¹^(m+k)+ A*Y) := by
   obtain ⟨E,hE,H⟩:= cash_part (I:=Loc G 1) (J:=Loc G 1) (m:=m) hs hp hc k; obtain ⟨R,hR,Hr⟩:=cash_cove (I:=Loc G 1) (J:=Loc G 1) (m:=m) hp hc k; let n:ℝ:= Fintype.card (chain (Loc G 1) m)
   let W := trimmed (Fin m×Axis) k
   refine ⟨n*E,n*W.card*R,by unfold n; positivity,by unfold n; positivity,fun L ho hu S hS x T A B hT ha hU=>?_⟩
   let V: edgeL G:=(lift x,b); let p:=robot V (carries (lift x) T); have hl:=bot_arm V _ (knight (lift x) b T hT)
   let a:edgeL G :=(0,b); have hz :piz L V b=a:=Prod.ext (by
       change rent L (lift x)=0; exact (rent_raw (0:Cover) (lift x) x (by simp)).2) rfl
   have hZ:=hS [] (Nat.zero_le k); rw [advanceC, show (1+ List.length ([]:List Axis))=1 from rfl,pow_one] at hZ
   unfold upmost; rw [tale_gate S (lift x) b hZ hp (mul_nonneg hc (by positivity)) _ hs.le hT]
   have hx i : Knoxville (fame _) η (0,b) (glassTail S V p i) (B*(E*(L.val:ℝ)⁻¹^(m+k)) + W.card*(A*R)):= by
       change Knoxville _ _ a _ _; rw [←hz]; apply pose_sharp hs hp hc k ha hE S hu ho hS V a i (H L hu ho S hS V i · a) hl _ _ hR
       · intro j hj; rw [horn_test (lift x) b T j i hT hs]; exact hU i j hj
       intro j hj; exact Hr L S hS ho V i j ((trim_def ..).mp hj|>.le) a
   apply (knox_sum Finset.univ (fun i _=> hx i)).mono; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change n*(_ + _) ≤ _; apply le_of_eq; ring

lemma blossoms (H:Hol G)(F:Frame G d)(o:Loc G 1)(m u D e q:ℕ)(hx:q≤d+1)(s: Seasons)(σ θ:ℝ)(hp:0<θ)(he:θ≤σ): ∃ C:ℝ,0≤C ∧
     ∀ Y:Anthem D G,Clef o Y u→∀ A:ℝ,Bonds F o θ q e m Y A → ∀ i: chain (Loc G 1) m,∀ t∈trimmed (Fin m×Axis) (q-m-upper s),∀ X, Knoxville (fame _) σ (0,o) (Y (cone D s) e m) X → ‖tariffs (fun j:Fin m=> assigns (horn (aster t j) (i j))) (Y (cone D s) e m)‖ ≤ C*A:= by
   let I:= chain (Loc G 1) m; let R:=trimmed (Fin m×Axis) (q-m-upper s)
   have hh(i:I)(t:↥R): ∃ C:ℝ,0≤C ∧ ∀ Y:Anthem D G,Clef o Y u→∀ B:ℝ,Bonds F o θ q e m Y B→∀ X, Knoxville (fame _) σ (0,o) (Y (cone D s) e m) X→‖tariffs (fun j=> assigns (horn (aster t.val j) (i j))) (Y (cone D s) e m)‖≤ C*B:= by
       have Hk : (∑ i:Fin m,(upper (aster t.val i)+1)) + upper s<q:= by
          rw [Finset.sum_add_distrib,←adder,Finset.sum_const, Finset.card_univ,Fintype.card_fin]; simp only [smul_eq_mul,mul_one]
          have hg:upper t.val<(q-m-upper s):=(trim_def ..).mp t.property; omega
       obtain ⟨C,hC,h⟩:= hypotheses o F e q m hx s D u (fun j=>horn (aster t.val j) (i j)) (fun j=>upper (aster t.val j)+1) (fun j=>by omega) Hk (fun j=>horns _ _) H hp
       exact ⟨C,hC,fun Y hy B hb X hz=> h Y hy B hb X (penn_shrink hz he)⟩
   choose! C hC H using hh
   let X(i:I):=∑ j,C i j; have hz i:0≤X i:=Finset.sum_nonneg (fun _ _=> hC i _); let Z:=∑ i,X i
   refine ⟨Z,Finset.sum_nonneg (fun i _=> hz i),fun Y h A he i j hj B hV=>?_⟩; apply (H i ⟨j,hj⟩ Y h A he B hV).trans;exact mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun j _=> hC i j) (Finset.mem_univ _)).trans (show X i≤Z from Finset.single_le_sum (fun i _=>hz i) (Finset.mem_univ i))) he.1

lemma north_bill (H:Hol G)(F:Frame G d)(o:Loc G 1)(m u D e q:ℕ)(hx:q≤d+1)(s: Seasons)(σ η θ C:ℝ)(hθ:0<θ)(hp:θ≤σ)(he:0≤η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y∧
   ∀ T:Anthem D G,Clef o T u→∀ L:Side,Threshold σ η m L→Odd L.val→∀ S:Cross L (Loc G 1) (Loc G 1),gauss S η C (q-m-upper s)→∀ A:ℝ, Bonds F o θ q e m T A→∀ B, Knoxville (fame _) σ (0,o) (T (cone D s) e m) B→∀ x:Site L,
     Knoxville (fame _) η (0,o) (upmost L x S (T (cone D s) e m)) (X*B * Dawn.scale L ^ (m+(q-m-upper s)) + Y*A) := by
   obtain ⟨X,E,hx',hE,HX⟩:= thorn_cost o m (q-m-upper s) (lt_of_lt_of_le hθ hp) he hc
   obtain ⟨V,hV,HV⟩:=blossoms H F o m u D e q hx s σ θ hθ hp
   refine ⟨X,E*V,hx',mul_nonneg hE hV,fun T h L ht ho S hG A hb B hR x=>?_⟩
   apply Knoxville.mono (HX L ho ht S hG x _ _ _ hR (mul_nonneg hV hb.1) (fun i t he=> HV T h _ hb i t he _ hR)); apply le_of_eq; change _=X*B* (L.val:ℝ)⁻¹^_+_; ring
end YM.FormalBulk08.Grail
