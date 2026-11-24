import YM.Comparison.RG02.Step.Record
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
/-!
# Physical marker renaming and restrictions

 Names are independent of the geometry and predictor. May take any admissible restriction, no
 re-tuning supports or branching. Exact identities here are for full polynomials at smaller
 horizon -- NOT statements that new data may be separately chosen/exist or that disjoint reports
 agree in contact germs etc. Use `Growth` reservation tracking separately. Coordinate reweight
 via Multi.dilation; do not interpret as arbitrary matrix or basis change. This binding uses
 pointwise full Π, not representation identities. For actual mask representation using
 `Multi.many`, also proved compatibility with *keeping* pulse choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sources
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Marker YM.Multi YM.Comparison.RG02.Order Integral Actual
open YM.Extra.Trajectories (Names Names.look connected pass_connected connected_quiet)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {V V' X Y : Type} [DecidableEq V'] [DecidableEq V] [Fintype V] [Fintype V'] {C : Census V} {C' : Census V'}
  (u : Names C C') (h : Lit C' X)

def remap := u.restriction ∘ h

def restriction : Poly C' →ₐ[ℂ] Poly C:={ u.restriction with
  commutes' := fun z=>by
    ext i
    change (Poly.send C'.quiet z).part (u.share i)=(Poly.send C.quiet z).part i
    simp_rw [Poly.part_send,← u.quiet,u.inj.eq_iff] }
omit [Fintype V] [Fintype V'] in
lemma restriction_part (a : Poly C') (s : C.Mode) : (restriction u a).part s=a.part (u.share s) := rfl
omit [Fintype V] [Fintype V'] in
lemma lit_part (s : C.Mode) : atMark s (remap u h)=atMark (u.share s) h := rfl
omit [Fintype V] [Fintype V'] in
lemma restrict_lit (a : Hot C'→ℂ) : (restriction u) (lit C' a)=lit C (a ∘ u.look) := by
   ext i; rw [restriction_part]; by_cases hi:i.val.Nonempty
   · let k:Hot C := ⟨i,hi⟩
     exact (part_lit a (u.look k)).trans (part_lit (a ∘ u.look) k).symm
   have hu: i=C.quiet:= Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hi); rw [hu,u.quiet, part_lit_quiet, part_lit_quiet]

-- unitscale and masks
omit [Fintype V] [Fintype V'] in
lemma masked (A : Set X) : remap u (A.indicator h)=A.indicator (remap u h) := by
  funext i; unfold remap; by_cases H:i∈A <;> simp [*]
omit [Fintype V] [Fintype V'] in
lemma remap_sub (h' : Lit C' X) : remap u (h-h') = remap u h-remap u h':= by ext u; simp [remap]
omit [Fintype V] [Fintype V'] in
lemma remap_comp (f : Y→X): remap u (h∘f) = remap u h ∘ f:= rfl
omit [Fintype V] [Fintype V'] in
lemma unit (x : Poly C') : u.restriction (unitScale x)=unitScale (u.restriction x) := by
  unfold unitScale; rw [u.smul,part_restrict,u.quiet]
omit [Fintype V] [Fintype V'] in
lemma re_price (x : Poly C') (w : V'→ℝ) (H : ∀ i, 0<w i) : Poly.price (w∘u.e) (u.restriction x) ≤ Poly.price w x := by
  let U := map ⟨u.share,u.inj⟩ (Finset.univ : Finset C.Mode)
  have hp : U ⊆ Finset.univ := subset_univ _
  unfold Poly.price
  refine le_trans (Eq.le (b:=∑ i∈U,Poly.toll w i * ‖x.part i‖) ?_) (sum_le_sum_of_subset_of_nonneg hp (fun i _ _=> mul_nonneg ((Finset.prod_pos (fun j _=>H j): 0<Poly.toll w i).le) (norm_nonneg _)))
  rw [Finset.sum_map]; exact sum_congr rfl fun i _=> congrArg (· * _) (Eq.symm (Finset.prod_image (f:=w) (s:=i.val) u.e.injective.injOn))

section integration
variable [MeasurableSpace X] (μ : Measure X)
omit [Fintype V] [Fintype V'] in
lemma charge_remap : u.restriction (charge μ h)=charge μ (remap u h) := rfl
omit [Fintype V] [Fintype V'] in
lemma good (H : Good μ h) : Good μ (remap u h) := fun t=> H (u.share t)
omit [Fintype V] [Fintype V'] in
lemma born (H : Leaf.All h) : Leaf.All (remap u h) := fun t=> H (u.share t)
end integration

variable {c f : Side} (S : StepData c f) {G : Gauge} (K : Lit C' (Config G f))
  (b : ℝ) (J : Config G c)
omit [Fintype V] [Fintype V'] in
lemma keeps : remap u (Actual.Push S b K)= Actual.Push S b (remap u K) := by
  funext i; apply Marker.Poly.ext; intro s; rfl
omit [Fintype V] [Fintype V'] in
lemma retains (t : S.Choices) : remap u (Actual.stack t J b K) = Actual.stack t J b (remap u K) := rfl
omit [Fintype V] [Fintype V'] in
lemma floor (P : Rep G f) (H : Floor P K) : Floor P (remap u K) := by
   refine ⟨fun y=> ?_,born u K H.safe, fun t x=> congrArg u.restriction (H.gauges t x)⟩
   change (K y).part (u.share C.quiet)=_; rw [u.quiet,H.vacancy]
lemma many_part (P : Rep G f) (D : Hot C' → Pulse G f) : remap u (many P C' D)= many P C (D ∘ u.look) := by
   funext y; change restriction u (many P C' D y)=_; unfold many; rw [maps_at (restriction u) _ _ _ (part_lit_quiet _) (by rw [restrict_lit u (fun i:Hot C'=> (D i).1 y),part_lit_quiet])]; simp_rw [restrict_lit]; rfl

section Bind
open Bulk
variable {o : ℝ} {r r' : ℕ} (he : Fin r ↪ Fin r')
omit [Fintype V] [Fintype V'] in
lemma share_card (s : C.Mode) : (u.share s).val.card=s.val.card := Finset.card_image_of_injective _ u.e.injective

lemma value_restrict (p : Grade C' r) (hp : Order.Symmetric p) (a : ℂ) : u.restriction (value a p)=value a (truncate u (Function.Embedding.refl _) p) := by
  unfold value; rw [map_sum]; apply sum_congr rfl; intro k hk; rw [u.smul,trunc_observe u _ hp (by simpa using hk : k≤r)]
lemma trunc_logVac {p : Grade C' r'} (hp : UnitLeading p) : truncate u he (logVac p)= logVac (truncate u he p) := by rw [logVac,denominator,trunc_log u he ((bottom_quiet _).trans hp : UnitLeading (denominator p)),trunc_bottom]; rfl
lemma trunc_marked {p : Grade C' r'} (hp : UnitLeading p) : truncate u he (logMarked p) = logMarked (truncate u he p) := by rw [logMarked,trunc_log u he (ratio_quiet hp),trunc_ratio u he hp]; rfl

def pin (R : Colors C' G f) : Colors C G f:= {vac:=R.vac,mark:=R.mark ∘ u.look,power:=R.power ∘ u.look}
omit [Fintype V] [Fintype V'] in
lemma well (P : Colors C' G f) (h : Well P) : Well (pin u P) := ⟨h.suppose_vac,fun i=> h.suppose_mark (u.look i), h.natural,fun i=> h.gauges (u.look i), h.envelope, fun i=> h.prices (u.look i)⟩
omit [Fintype V] [Fintype V'] in
lemma standard_pin (P : Colors C' G f) (h : P.Standard) : (pin u P).Standard:= ⟨well u P h.1,h.2⟩
variable {S} {p : Clip} {P : PathData G} {O : ChartRatio G} (Q : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
   (W : Colors C' G f) (x : fieldDir G c 1)
local notation "W'"=> pin u W
lemma criterion : truncate u he (Fk Q F t W x r')= Fk Q F t W' x r :=
    Assembly.restriction (stage Q F x) _ (W').power _ _ _ _ (Q.positive F t) u he _ _ _ (fun _ _ _=>rfl) (fun _ _ _ _=>rfl)
end Bind
end YM.Comparison.RG02.Sources
