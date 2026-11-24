import YM.Integration.WilsonMaxwellThermometerFiledIncidenceRate
import YM.Integration.WilsonMaxwellThermometerInteracting
import YM.Integration.WilsonMaxwellThermometerFaces

/-! Linear-spacing control for the literal connected Maxwell coefficient on
the declared public inversion regulator. The bound is multilinear in the
actual declared doses, with the same three roots in every proper moment. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerConnectedIncidenceRate
open Filter Set Finset Function Metric Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement
open WilsonMaxwellThermometerBareIncidenceRate
open WilsonMaxwellThermometerInteracting (face)
open WilsonPositionThermometerConnected (value)
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)

private theorem placed (v:Point G 6 3)(p:Tags G 6 3)(i:Fin 3)(x:Sec G 6)(s:Badge):
    face v (update p i x) s=if i∈s then v.toLinearMap (missing p s) i x else face v p s:=by
  by_cases h:i∈s
  · rw [if_pos h];unfold face
    change v _=v (update (missing p s) i x)
    congr 1;funext k
    by_cases e:k=i
    · subst k;simp [missing,h]
    · by_cases h':k∈s <;> simp [missing,h',update_of_ne e]
  · rw [if_neg h];unfold face;congr 1;funext k
    by_cases e:k=i
    · subst k;simp [missing,h]
    · by_cases h':k∈s <;> simp [missing,h',update_of_ne e]

def row (v:Point G 6 3):Point G 6 3:=MultilinearMap.mk'
  (fun p=>value (face v p))
  (fun p i x y=>by fin_cases i <;> simp [value,placed,map_add] <;> ring)
  (fun p i a x=>by fin_cases i <;> simp [value,placed,map_smul,smul_eq_mul] <;> ring)

theorem ground (p:Tags G 6 3){K:Set (Points 3)}(compact:IsCompact K)(apart:K⊆conf 3):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀u:pack 3,∀c∈M.Box,M.rel u c∈K →
      ‖row (live W 6 ⟨M,u,c⟩ 0) p-row (scene (M.rel u c) 6) p‖≤C*M.spacing:=by
  choose C pos bill using fun s:Badge=>bare W 6 (missing p s) compact apart
  let A:=∑s:Badge,C s
  have non:0≤A:=sum_nonneg (fun s _=>pos s)
  have ca (s:Badge):C s≤A:=single_le_sum (f:=C) (fun j _=>pos j) (mem_univ s)
  let T (x:Points 3):Badge→ℂ:=face (scene x 6) p
  have cont:ContinuousOn T K:=by
    apply continuousOn_pi.mpr
    intro s x hx
    exact (Wick.moment_smooth _ (apart hx)).continuousAt.continuousWithinAt
  obtain ⟨B,bc⟩:=compact.exists_bound_of_continuousOn cont
  let h:=A+max 0 B
  let D:=closedBall (0:Badge→ℂ) h
  have differentiates:ContDiff ℝ 1 value:=by unfold value;fun_prop
  obtain ⟨L,hl⟩:=differentiates.contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_closedBall (0:Badge→ℂ) h) (isCompact_closedBall _ _)
  refine ⟨L*A,mul_nonneg L.coe_nonneg non,?_⟩
  filter_upwards [eventually_all.mpr bill,frontier.smaller] with M good size
  intro u c hc valid
  let S:=face (live W 6 ⟨M,u,c⟩ 0) p
  let t:=T (M.rel u c)
  have diff:‖S-t‖≤A*M.spacing:=by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg non M.positive.le)).mpr
    intro s
    exact (good s u c hc valid).trans (mul_le_mul_of_nonneg_right (ca s) M.positive.le)
  have small:A*M.spacing≤A:=mul_le_of_le_one_right non size
  have ht:‖t‖ ≤ max 0 B:=(bc _ valid).trans (le_max_right ..)
  have din:t∈D:=by simpa [D,dist_zero_right] using ht.trans (le_add_of_nonneg_left non)
  have sin:S∈D:=by
    have b:‖S‖≤‖S-t‖+‖t‖:=by convert norm_add_le (S-t) t using 1;rw [sub_add_cancel]
    simpa [D,dist_zero_right] using b.trans (add_le_add (diff.trans small) ht)
  calc
    _ ≤ L*‖S-t‖:=by
      change ‖value S-value t‖≤_
      simpa only [dist_eq_norm] using hl.dist_le_mul S sin t din
    _ ≤ _:=by simpa [mul_assoc] using mul_le_mul_of_nonneg_left diff L.coe_nonneg

/-- Actual moving fields may be chosen after both the stencil and the torus.
The scalar is evaluated on the original seven complete ordinary faces. -/
theorem moving {I:Fin 3→Type}[∀j,Fintype (I j)](f:∀j,I j→Sec G 6)
    {K:Set (Points 3)}(compact:IsCompact K)(apart:K⊆conf 3):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀u:pack 3,∀c∈M.Box,M.rel u c∈K →
    ∀v:∀j,I j→ℂ,‖row (live W 6 ⟨M,u,c⟩ 0) (assembled 6 f v)-
      WilsonMaxwellThermometerFaces.connected (M.rel u c) (assembled 6 f v)‖≤
      (C*M.spacing)*∏j,∑i,‖v j i‖:=by
  choose c pos good using fun b:∀j,I j=>ground W (fun j=>f j (b j)) compact apart
  let C:=∑b,c b
  have hC:0≤C:=sum_nonneg (fun b _=>pos b)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_all.mpr good] with M fee
  intro u o ho hk v
  have constant (F:Badge→ℂ):PowerSeries.constantCoeff (b3 (fun s=>PowerSeries.C (F s)))=value F:=by
    simp [b3,value,Algebra.smul_def]
  rw [WilsonMaxwellThermometerFaces.connected,constant]
  let A:=row (live W 6 ⟨M,u,o⟩ 0)-row (scene (M.rel u o) 6)
  change ‖A (fun j=>∑i,v j i •f j i)‖≤_
  rw [MultilinearMap.map_sum_finset]
  calc
    _≤∑b:∀j,I j,‖A (fun j=>v j (b j) • f j (b j))‖:=norm_sum_le ..
    _≤∑b:∀j,I j,(C*M.spacing)*∏j,‖v j (b j)‖:=by
      apply sum_le_sum
      intro b _
      rw [A.map_smul_univ,norm_smul,norm_prod,mul_comm]
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _=>norm_nonneg _)
      have cb:c b≤C:=single_le_sum (f:=c) (fun j _=>pos j) (mem_univ b)
      exact (fee b u o ho hk).trans (mul_le_mul_of_nonneg_right cb M.positive.le)
    _= _:=by rw [←mul_sum,Fintype.prod_sum]

end YM.Integration.WilsonMaxwellThermometerConnectedIncidenceRate
