import YM.MatchingLedger.Review.Times
import YM.PertExtension.BareWords

/-!
# Columns are actual canonical stencils (and joint products)

Dimensionless test read. No claiming costs after extension/extraction. The label in this
estimate can realize *the corresponding bare field* exactly on the constructed trajectory
(`SameColumns.reprice`, horizon-dependent even at translations). Don't specify which
canonical fields are equal modulo e.g. EOM from this product rule/statements below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Review.Columns
open Function Filter Set MeasureTheory Lattice RG Wilson Tree Pressure
open Precision Action Top Home Cooling Gazette Periodical Kiosk Books Push.Uniform
open Source MvPolynomial
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

section forge
variable {n : ℕ}
lemma multiply {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{p q:E→ℂ}{k l:ℝ}{x:E}(hp:Allows n p x k)(hq:Allows n q x l) :
    Allows n (fun x=>p x*q x) x (2^n* k*l):=by simpa only [mul_one,ContinuousLinearMap.mul_apply'] using hp.bilinear (ContinuousLinearMap.mul ℝ ℂ) hq (ContinuousLinearMap.opNorm_mul_le ℝ ℂ)

-- Torus-independent (using cylinder rather than analytic patch prices).
variable (G)
private lemma wired (n : ℕ) : ∃ z:ℝ,0≤z ∧ ∀ {c f:Side}{S:StepData c f}(F : Forest S.ratio)(e : Bond f)(x : Chip (Needle F G)), ‖x‖ ≤ 1→ Allows n (fun y=> G.mat (F.drape (lights F y) e)) x z:= by
  obtain ⟨Z,H⟩:= paint_supply G n
  have hp:= outer_pos G n H.1
  let z:= outerCost G n Z; refine ⟨z+‖(1:G.Mat)‖,add_nonneg hp.le (norm_nonneg _),?_⟩
  intro c f S F e x hx; by_cases h:e∈F.trunks
  · simp_rw [show ∀ s:F.Slice G,G.mat (F.drape s e)=1 from fun s=>congr_arg G.mat (F.on_tree s ⟨e,h⟩)]
    exact allows_const x (le_add_of_nonneg_left hp.le)
  let i : F.Free:=⟨e,h⟩
  have hv (x:Chip (Needle F G)) : F.drape (lights F x) e=launch x i := F.off_tree _ i
  simp_rw [hv]; let L:= ContinuousLinearMap.id ℝ (Chip (Needle F G))
  exact ((paint_book (x:=x) L H (fun _=> le_rfl) hx i).mono (le_add_of_nonneg_right (norm_nonneg _)))


variable {G}
def Floats (p : Finset Cover)(φ : Source.Formula G p)(n : ℕ) := ∃ u : ℝ, 0≤u ∧
    ∀ {c f:Side} {S:StepData c f} (F : Forest S.ratio) (y:Site f) (x:Chip (Needle F G)), ‖x‖≤1 →
       Allows n (fun z=> aeval (Source.entry (expandAt y (F.drape (lights F z)))) φ) x u
private def normReceipt {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](L:E→L[ℝ]ℂ):ℝ := ‖L‖
private lemma nonnegL {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E](L:E→L[ℝ]ℂ): 0 ≤ normReceipt L:= norm_nonneg _
lemma floats (p : Finset Cover)(φ : Source.Formula G p)(n:ℕ) : Floats p φ n:= by
  obtain ⟨v,hv,H⟩:= wired G n
  induction φ using MvPolynomial.induction_on with
  | C a=>
    refine ⟨‖a‖, norm_nonneg _,fun {c f S} F y x _=>?_⟩; simp_rw [aeval_C,Algebra.algebraMap_self]; exact allows_const x (by rfl)
  | add f q hf hq=>
    obtain ⟨a,ha,hf⟩:=hf; obtain ⟨b,hb,hq⟩:=hq; refine ⟨a+b,add_nonneg ha hb,fun {c f_ S} F y x hx=>?_⟩
    simp_rw [_root_.map_add]; exact (hf F y x hx).add (hq F y x hx)
  | mul_X f i hf=>
    obtain ⟨a,ha,hf⟩:=hf
    let L:G.Mat →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ i.2.1 i.2.2.1).toContinuousLinearMap
    let L' : G.Mat →L[ℝ] ℂ := if i.2.2.2 then Complex.conjCLE.toContinuousLinearMap.comp L else L
    have he(U:CoverConfig G): Source.entry U i=L' (G.mat (U i.1.val)):=by unfold Source.entry L'; cases i.2.2.2 <;> rfl
    let u:= normReceipt (E:=G.Mat) L'
    have h : 0 ≤ u := nonnegL (E:=G.Mat) L'
    refine ⟨2^n*a*(u*v), by positivity,fun {c f_ S} F y x hx=>?_⟩
    simp_rw [_root_.map_mul,aeval_X,he]; exact multiply (hf F y x hx) (Allows.linear L' (H F _ x hx) le_rfl)
end forge

section sector
variable {C : Family G}{d : ℕ}
def deck (C : Family G) (d : ℕ)(y : Site f) := (C.localSection d).footprint y

def chairs (C : Family G)(F : Forest S.ratio)(d : ℕ)(y : Site f):= Finset.univ.filter (fun i : F.Free=> i.val.1∈ deck C d y)
lemma seats (C : Family G)(F : Forest S.ratio)(d : ℕ)(y : Site f): (chairs C F d y).card ≤ (C.localSection d).stencil.card*Fintype.card Axis:= by
  apply (Finset.card_le_card_of_injOn Subtype.val (t:= (deck C d y) ×ˢ (Finset.univ (α:=Axis))) (fun i hi=> Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hi).2,Finset.mem_univ _⟩) Subtype.val_injective.injOn).trans
  rw [Finset.card_product,Finset.card_univ]; exact Nat.mul_le_mul_right _ Finset.card_image_le

lemma pinned_column (C : Family G) (τ : C.label d) (F : Forest S.ratio)(y : Site f){U V:F.Slice G} (he:EqOn U V (chairs C F d y)) : (C.localSection d).places τ y (F.drape U)=(C.localSection d).places τ y (F.drape V) := by
  apply (C.localSection d).placed_local; intro i hi _
  by_cases h : i∈F.trunks; exact (F.on_tree _ ⟨_,h⟩).trans (F.on_tree _ ⟨_,h⟩).symm
  let j:F.Free:=⟨i,h⟩; have hh : j∈ chairs C F d y:= Finset.mem_filter.mpr ⟨Finset.mem_univ j,hi⟩; exact (F.off_tree U j).trans ((he hh).trans (F.off_tree V j).symm)
end sector

section palettes
variable {α : Type*} (w : Finset α)(d : α→ ℕ)(C : Family G)(τ : ∀ i, C.label (d i))
def documentary (y : α→ Site f)(U : Config G f) := ∏ i∈w,(C.localSection (d i)).places (τ i) (y i) U
lemma genuine : ∀ (N p:ℕ) (x:α→Site (C.side N p))(U:Config G (C.side N p)), documentary w d C τ x U= ∏ i∈w,C.O N p (YM.PertExtension.SameColumns.reprice C N p (τ i)) (x i) U:= by simp_rw [YM.PertExtension.SameColumns.reprice_eq]; intros; rfl
lemma document_wire (y : α→ Site f) : Continuous (documentary w d C τ y):= continuous_finsetProd _ fun _ _=> SectionData.continuous_places ..
lemma documentary_invar (h : C.Makes)(y:α→Site f): GaugeInvariant (documentary w d C τ y):= fun g U=>Finset.prod_congr rfl (fun i _=> SectionData.placed_invariant _ (h.sections (d i)) _ _ g U)

def cinema (F : Forest S.ratio)(w : Finset α)(d:α→ℕ)(C:Family G)(y : α → Site f):= w.biUnion fun i=> chairs C F (d i) (y i)
def barges := ∑ i∈w, (C.localSection (d i)).stencil.card * Fintype.card Axis
lemma room (F : Forest S.ratio)(y:α→Site f) : (cinema F w d C y).card ≤ barges w d C:= (Finset.card_biUnion_le ..).trans (Finset.sum_le_sum fun i _=> seats C F (d i) _)
lemma tone {F : Forest S.ratio} (y:α→Site f){U V:F.Slice G} (h:EqOn U V (cinema F w d C y)): documentary w d C τ y (F.drape U)= documentary w d C τ y (F.drape V):= Finset.prod_congr rfl fun i hi=> pinned_column C (τ i) F _ (h.mono (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem (fun i=>chairs C F (d i) (y i)) hi))) -- check namespace

lemma matinee (n : ℕ) : ∃ a : ℝ, 0≤ a ∧ ∀ {c f:Side} {S:StepData c f}(F : Forest S.ratio)(y : α→Site f),
    (∀ u:Config G f, ‖documentary w d C τ y u‖ ≤ a) ∧
    (∀ x:Chip (Needle F G), ‖x‖≤1 → Allows n (documentary w d C τ y ∘ F.drape ∘ lights F) x a) := by
  induction w using Finset.induction_on with
  | empty =>
    refine ⟨1,zero_le_one,fun {c f S} F y=> ⟨fun u=>?_ , fun x _=>?_⟩⟩
    · rw [documentary,Finset.prod_empty,norm_one]
    simp only [documentary,Finset.prod_empty,Function.comp_def]; exact allows_const x (by simp)
  | insert i w hi hw=>
    obtain ⟨a,ha,H⟩ := floats _ ((C.localSection (d i)).evalC (τ i)) n
    obtain ⟨e,he⟩:= ((C.localSection (d i)).continuous_evaluate (τ i)).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
    obtain ⟨b,hb,h⟩:= hw
    have he' := (norm_nonneg _).trans (he (1 : CoverConfig G))
    refine ⟨max (e*b) (2^n * a*b),le_trans (by positivity) (le_max_left ..),fun {c f S} F y=>?_⟩
    have hu (U:Config G f) : documentary (insert i w) d C τ y U=(C.localSection (d i)).places (τ i) (y i) U* documentary w d C τ y U:= Finset.prod_insert hi
    refine ⟨fun v=>?_,fun x hx=>?_⟩
    · rw [hu,norm_mul]; exact (mul_le_mul (he _) ((h F y).1 v) (norm_nonneg _) he').trans (le_max_left ..)
    simp_rw [Function.comp_def,hu]; exact (multiply (H F (y i) x hx) ((h F y).2 x hx)).mono (le_max_right ..)

-- α horizon for input can be any finite subset; orthogonal rotations of C preserve field Hpart, at stencil-dependent prices.
lemma cinemas (L:ℂ→L[ℝ]ℝ)(n:ℕ): ∃ a : ℝ, 0 ≤ a ∧ ∀ {c f:Side} {S:StepData c f}(F : Forest S.ratio)(y : α→Site f), Affords F (cinema F w d C y) ((L∘ documentary w d C τ y) ∘ F.drape) n a:= by
  obtain ⟨a,ha,h⟩:= matinee w d C τ (n+1); have he :0≤‖L‖*a:=by positivity
  refine ⟨‖L‖*a,he,fun {c f S} F y=>?_⟩
  let W:= documentary w d C τ y
  have hW : Continuous (W ∘ F.drape) := (document_wire w d C τ y).comp F.continuous_drape
  exact ⟨he,fun U=> (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((h F y).1 _) (norm_nonneg _)), (L.continuous.comp hW).measurable, fun x hx=> Allows.linear L ((h F y).2 x hx) le_rfl, fun {u v} he=>congr_arg L (tone _ _ _ _ y he)⟩

end palettes
end YM.MatchingLedger.Review.Columns
