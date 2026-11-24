import YM.OPE.Compatible.Rhus.Ripple
/-! Lap shell ideal rank on this weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp Source Drops WardBin Planned.PrimaryIntegral295.Parts
open scoped Topology BigOperators Classical
variable {r d m n j:ℕ}{c:ℝ}{W:Type*}{G:Gauge}
namespace Script
open Page
variable (e:ℕ)(h:n+r≤j)(ht:j≤e)
lemma wallsUni (p:Spired G r n j)(Q R: MixX G r n d)(hQ:Reading p Q)(hR: Reading p R):Q=R:= mixUni Q R fun x=> by
    rw [← trunks x, ← hQ,← hR]
include h
def wallLease :Spired G r n j≃ₗ[ℝ] MixX G r n e:= by
    let v: Spired G r n j→ₗ[ℝ] MixX G r n e:={
       toFun := readWall e ht
       map_add' := fun a b=> wallsUni (d:=e) _ _ _ (Read_reads _ _ _) (show Reading (a+b) (readWall e ht a+readWall e ht b) from fun x=>by rw [rollAdd,← Read_reads,← Read_reads]; exact map_add ..)
       map_smul' := fun t p=> wallsUni (d:=e) _ _ _ (Read_reads _ _ _) (show Reading (t • p) (t • readWall e ht p) from fun x=>by
           rw [rollScale,← Read_reads]; exact (Labels.read x).toLinearMap.restrictScalars ℝ|>.map_smul t p.val.val)
    }
    refine LinearEquiv.ofBijective v ⟨fun i j h=>Subtype.ext (Subtype.ext (eval_ext _ _ fun x=>?_)),fun y=>?_⟩
    · change readWall e ht i=readWall e ht j at h; rw [Read_reads e ht i x,h,Read_reads e ht j x]
    obtain ⟨p,hp⟩:=tiled h y; exact ⟨p,wallsUni (d:=e) _ _ _ (Read_reads e ht p) hp⟩
lemma lease_pay (p:Spired G r n j):Reading p (wallLease e h ht p):=Read_reads e ht p
omit h
def glare (G:Gauge)(d:ℕ): Alphabet G d→ₗ[ℝ] Alphabet G d:=LinearMap.pi (fun i:Fin d=>
    let p:= gaugeJet (G:=G) (j:=i.val);
    p ∘ₗ p.leftInverse∘ₗ LinearMap.proj (φ:=fun j:Fin d=> Taylor G j.val) i)
abbrev crownTower (T: TaylorTower G): Alphabet G (d-1):=trunk d fun i=>gaugeJet (T i)
lemma shines (G:Gauge) (i: Shell G j): (gaugeJet (G:=G) (j:=j)).leftInverse (gaugeJet i)=i:= LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr leg_injective) i -- d unused
lemma glare_same (T:TaylorTower G): glare G (d-1) (crownTower T)=crownTower T:=by ext1 i; change gaugeJet ((gaugeJet (G:=G) (j:=i.val)).leftInverse (gaugeJet (T i.val)))=_; rw [shines];rfl
lemma glare_lift (v: Snap G d): ∃ T:TaylorTower G,glare G (d-1) v=crownTower (d:=d) T:=by
    let T j:= (gaugeJet (G:=G) (j:=j)).leftInverse (expand d v j); exact ⟨T,funext fun i=> by change gaugeJet ((gaugeJet (G:=G) (j:=i.val)).leftInverse (v i))=gaugeJet _; congr! 2; exact (congr_fun (trunks v).symm i) -- maybe rw RHS too
    ⟩
-- Multilinear restriction now equals diagonal; use as free EOM projection
abbrev wiped (A: Chord G d r):=∀ x: Fin r→Alphabet G d,A (fun i=> glare G d (x i))=0
/-- Restriction of a symmetric form to the range of a linear map is determined
by the repeated-input evaluations on that range. -/
private lemma projected_form_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : MultilinearMap ℝ (fun _ : Fin r => E) ℝ)
    (sym : ∀ (x : Fin r → E) (σ : Equiv.Perm (Fin r)), A (x ∘ σ) = A x)
    (p : E →ₗ[ℝ] E) (diag : ∀ t : E, A (fun _ => p t) = 0) (x : Fin r → E) :
    A (fun i => p (x i)) = 0 := by
  obtain ⟨B, hB⟩ := wiredLift (E:=E) A
  let f : E →L[ℝ] E := LinearMap.toContinuousLinearMap p
  let Y : Tensor.T E ℝ r := B.compContinuousLinearMap (fun _ => f)
  have hd : Tensor.diagonal Y = Tensor.diagonal (0 : Tensor.T E ℝ r) := by
    funext t
    change B.toMultilinearMap (fun _ => f t) = 0
    rw [hB]
    exact diag t
  have hs : Tensor.Sym Y := by
    intro v σ
    change B.toMultilinearMap _ = B.toMultilinearMap _
    rw [hB]
    exact sym (fun j => p (v j)) σ
  have hz : Y = 0 := Tensor.ext_diag Y 0 hs (fun _ _ => rfl) hd
  rw [← hB]
  exact congrArg (fun Z : Tensor.T E ℝ r => Z x) hz

lemma towel (A: partX G r n (d-1)): wiped A.val ↔∀ T:TaylorTower G,A.val (fun _=> crownTower (d:=d) T)=0:=by
  constructor
  · intro h T
    rw [← glare_same T]
    exact h _
  intro h x
  apply projected_form_zero (E:=Snap G d) A.val
    (show Off G r n (d-1) A.val from A.property).Perms (glare G (d-1)) _ x
  intro t
  obtain ⟨T, ht⟩ := glare_lift t
  rw [ht]
  exact h T
lemma vacuumLoc (p:Spired G r n j) (Q: MixX G r n d)(hq:Reading p Q): p.val∈equationIdeal G j ↔ wiped (d:=d-1) Q.1.val ∧ wiped (d:=d-1) Q.2.val:=by
   rw [ideal_meaning,towel (d:=d) Q.1,towel (d:=d) Q.2]; simp_rw [hq]; constructor
   · intro h; constructor
     · intro T; have hx:=congr_arg Complex.re (h T); simp only [rollReading] at hx; change Complex.re (↑(Q.1.val (fun _=> crownTower (d:=d) T)) + Complex.I * ↑(Q.2.val fun _=> crownTower (d:=d) T))=_ at hx; simpa using hx
     intro T; have hx:=congr_arg Complex.im (h T); change Complex.im (↑(Q.1.val (fun _=> crownTower (d:=d) T))+ Complex.I*↑(Q.2.val fun _=> crownTower (d:=d) T))=_ at hx; simpa using hx
   rintro ⟨h,hP⟩ T; change ↑(Q.1.val (fun _=> crownTower (d:=d) T))+Complex.I*↑(Q.2.val (fun _=>crownTower (d:=d) T))=_; rw [h,hP]; simp
end Script
end YM.OPE.Flume
