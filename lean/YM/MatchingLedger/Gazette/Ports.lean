import YM.MatchingLedger.Draw
import YM.MatchingLedger.Books.Stencil
import YM.Push.STATIONARY_UNIFORM.Array

/-!
# Vertices in color-on-free-link coordinates and supports which really feed them.

For this SD prescription use logs of fine links themselves, not centered at replica of exterior.
Both operands are graphs on the chosen sides. `StepData`/`kernel` and all forest counts native.
- Cost to fit radius incl choices Branches is full `Action.belt S.patch`, never only low-ray support.
- SD is in unweighted real coordinates on *exact* group chart; here with sup-norm for variations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Gazette
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff
open scoped Finset
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio)

abbrev Kernel (G : Gauge)(ι : Type) := ι × G.ColorIndex
abbrev Needle (G : Gauge) := Kernel G F.Free
abbrev Page (G : Gauge)(c : Side) := Kernel G (Bond c)
abbrev Meter (G : Gauge) := Needle F G ⊕ Page G c

variable {ι α : Type} [Fintype ι] [Fintype α]
abbrev Chip := Books.Field

def binL : Chip (ι ⊕ α)→L[ℝ] Chip ι := ContinuousLinearMap.pi fun i : ι=> ContinuousLinearMap.proj (.inl i)
def binR : Chip (ι ⊕ α)→L[ℝ] Chip α := ContinuousLinearMap.pi fun i : α=> ContinuousLinearMap.proj (.inr i)
lemma binL_le (x : Chip (ι ⊕ α)): ‖binL x‖≤‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>norm_le_pi_norm x (.inl i)
lemma binR_le (x : Chip (ι ⊕ α)): ‖binR x‖≤‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>norm_le_pi_norm x (.inr i)
lemma joined (x : Chip ι)(y : Chip α){v : ℝ}(hx:‖x‖≤v)(hy:‖y‖≤v) : ‖Sum.elim x y‖≤v := (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hx)).mpr
  (fun i=> match i with | Sum.inl i=>(norm_le_pi_norm x i).trans hx | Sum.inr i => (norm_le_pi_norm y i).trans hy)

def launch (x : Chip (Kernel G ι)) (i : ι) := G.lieExp ((tint G ι x) i)
lemma tint_limit (x : Chip (Kernel G ι)) (i : ι) : ‖tint G ι x i‖ ≤ shade G*‖x‖ := (norm_le_pi_norm _ _).trans (tint_le x)
lemma tint_eq {x y : Chip (Kernel G ι)} {i : ι} (he : ∀ j:G.ColorIndex, x (i,j)=y (i,j)) : (tint G ι x) i=(tint G ι y) i := by ext j; exact he j
lemma send (x : Chip (Kernel G ι)) (i : ι) : launch x i=G.lieExp (WithLp.toLp 2 (fun j=> x (i,j))) := rfl
lemma launch_eq {x y : Chip (Kernel G ι)} {i : ι} (he : ∀ j:G.ColorIndex, x (i,j)=y (i,j)) : launch x i=launch y i := congr_arg _ (tint_eq he)
@[simp] lemma launch_zero : launch (ι:=ι) (G:=G) 0=1:= by unfold launch; simpa using! (by funext i; simp : (fun i=> G.lieExp ((tint G ι 0) i))=1) -- simplify
lemma launch_locus (i : ι) (x : Chip (Kernel G ι)) : ContinuousAt (fun z => launch (G:=G) z i) x := G.lieExp_cont.continuousAt.comp ((continuousAt_pi.mp ((tint G ι).continuous.continuousAt)) i)

def runway (y : Chip (Page G c)) : Config G c:= launch y
def venue (x : Chip (Meter F G)) := runway (binR x)
def lights (x : Chip (Needle F G)) : F.Slice G := launch x
def litter (x : Chip (Meter F G)) : Config G f := F.drape (lights F (binL x))
@[simp] lemma runway_zero : runway (G:=G) (c:=c) 0=1 := launch_zero
@[simp] lemma venue_zero : venue (G:=G) F 0=1 := by simp [venue]
@[simp] lemma litter_zero : litter (G:=G) F 0=1 := by
  unfold litter lights; rw [map_zero,launch_zero]; ext1 i; by_cases h:i∈F.trunks
  · exact F.on_tree _ ⟨_,h⟩
  exact F.off_tree _ ⟨_,h⟩

abbrev place {α : Type*} (q : ι → Site c) : ι × α → Site c := q ∘ Prod.fst
abbrev nest : Needle F G → Site c := place (area F)
abbrev berth : Page G c → Site c:= place Prod.fst
def atlas : Meter F G→ Site c:= Sum.elim (nest F) berth

abbrev ribbon (z : Site c) := halo (belt S.patch) {z}
def seats (z : Site c) := located (atlas (G:=G) F) (ribbon (S:=S) z)
lemma card_place (q : ι → Site c) (R : Support c) : (located (place (α:=α) q) R).card=(located q R).card * Fintype.card α:= by
  rw [← Finset.card_univ, ← Finset.card_product]
  congr 1; ext i; simp only [loc,Finset.mem_product, Finset.mem_univ, and_true]; rfl
lemma card_sum (q : ι → Site c)(g : α→ Site c)(R : Support c) : (located (Sum.elim q g) R).card=(located q R).card+(located g R).card:=by
  rw [← Finset.card_disjSum]
  congr 1; ext x; cases x <;> simp only [loc,Sum.elim_inl, Sum.elim_inr,Finset.inl_mem_disjSum,Finset.inr_mem_disjSum]

def nestCost (G : Gauge)(P : Patch) := linkRent P * G.lieDim
def cap (G : Gauge) (P : Patch) := nestCost G P + Fintype.card Axis * G.lieDim
lemma nest_size (R : Support c) : (located (nest (G:=G) F) R).card ≤ nestCost G S.patch * R.card:= by
  unfold nest; rw [card_place]; apply (Nat.mul_le_mul_right _ (free_size S R F)).trans_eq; unfold nestCost linkRent; rw [show Fintype.card G.ColorIndex=_ from @Fintype.card_fin G.lieDim]; ring
lemma atlas_size (R : Support c) : (located (atlas (G:=G) F) R).card ≤ cap G S.patch * R.card:= by
  unfold cap atlas; rw [card_sum, add_mul]; apply Nat.add_le_add (nest_size F R)
  apply le_of_eq; unfold berth; rw [card_place]
  have he : located Prod.fst R=R ×ˢ (Finset.univ (α:=Axis)):= by ext i; simp [located]
  rw [he,Finset.card_product,Finset.card_univ,show Fintype.card G.ColorIndex=_ from @Fintype.card_fin G.lieDim]; ring
lemma mag (s : Site c)(k : ℕ) : (halo k {s}).card ≤ (k+k+1)^4:= by simpa only [Finset.card_singleton,one_mul] using Lattice.Corona.halo_size {s} k

def bench (G : Gauge)(P : Patch) (k : ℕ) := cap G P*(k+k+1)^4
lemma bench_le (z : Site c) : (seats (G:=G) F z).card ≤ bench G S.patch (belt S.patch) := (atlas_size F _).trans (Nat.mul_le_mul_left _ (mag ..))

section agree
variable (S) {U W : Config G f}{V V' : Config G c}
/-- Enough fine sites on the whole forest. -/
def equalInside (S : StepData c f)(U W : Config G f)(R : Support c) := ∀ i : Bond f, region S i ∈ R → U i=W i
lemma equal_litter {x y : Chip (Meter F G)} {R : Support c}
    (h : Set.EqOn x y (located (atlas (G:=G) F) R)) : equalInside S (litter F x) (litter F y) R:= by
  intro i hi; by_cases he:i∈F.trunks; exact (F.on_tree _ ⟨_,he⟩).trans (F.on_tree _ ⟨_,he⟩).symm
  exact (F.off_tree _ ⟨_,he⟩).trans ((launch_eq (x:=binL x) (y:=binL y) (i:=⟨i,he⟩) (fun j=>h (loc.mpr (show atlas F (.inl (⟨i,he⟩,j)) ∈ R from hi)))).trans (F.off_tree _ ⟨_,he⟩).symm)
lemma equal_venue {x y : Chip (Meter F G)} {R : Support c}{z : Bond c}(hz : z.1∈R)
    (h : Set.EqOn x y (located (atlas (G:=G) F) R)) : venue F x z = venue F y z:=
  launch_eq fun j=> h ((loc (a:=atlas F) (i:=Sum.inr (z,j))).mpr hz)

variable (hB : S.patch.Branches S.kernel G) {z : Site c}(h : equalInside S U W (ribbon (S:=S) z))
include h
lemma equal_target (e : Site c) (hx : separation z e ≤ 1) : Agrees (Push.GridApprox.window (S.ratio.embed e) (Push.GridApprox.reach S.patch)) U W :=
  fun i hi _=> h i (near_root.mpr (le_trans (separation_triangle _ e _) (le_trans
      (Nat.add_le_add hx (window_pay S e i.1 hi)) (by unfold belt; omega))))
lemma equal_toll (i : Cell f) (he : region S i=z) : toll U i=toll W i := by
  unfold toll; apply congr_arg; apply travel_local; intro j hj _; apply h; rw [ribbon,near_root,← he]; exact (near_visit S i _ hj).trans (by unfold belt PatchArea.radius; omega)
include hB
lemma equal_wire (t : S.Choices) (he: ∀ i: Axis,V (z,i)=V' (z,i)) (i : Axis):
    wire (S.prediction U t) V (z,i)=wire (S.prediction W t) V' (z,i):=by
  unfold wire StepData.prediction; rw [he, Push.GridApprox.connector_dep S hB (z,i) _ _ rfl rfl (equal_target S h _ (by simp)) (equal_target S h _ (Work.E01.sep_step_le ..))]
lemma equal_price (t : S.Choices) (he: ∀ i: Axis,V (z,i)=V' (z,i)) :
    Action.bill S U V t z= Action.bill S W V' t z := by
  have hX : face S U z=face S W z:= Finset.sum_congr rfl fun i hi=>congr_arg (·^2) (equal_toll S h i (Finset.mem_singleton.mp (loc.mp hi)))
  unfold Action.bill; rw [hX]
  unfold thread; simp_rw [equal_wire S hB h t he]

omit h
def dues (G : Gauge) (t : S.Choices) (z : Site c) (x : Chip (Meter F G)) := Action.bill S (litter F x) (venue F x) t z
lemma equal_dues (t : S.Choices) {x y : Chip (Meter F G)} (hv : Set.EqOn x y (seats (G:=G) F z)) : dues S F G t z x= dues S F G t z y :=
  equal_price S hB (equal_litter (S:=S) F hv) t (fun i=> equal_venue (S:=S) F (z:=(z,i)) (halo_subset _ _ (Finset.mem_singleton_self _)) hv)
lemma dues_port (t : S.Choices) (z : Site c) : Books.Restricted (dues S F G t z) (seats F z):= by
  refine Filter.Eventually.of_forall (fun i=> equal_dues S F hB t ?_)
  intro j hj; rw [Books.crop_apply,if_pos]; exact hj
end agree
end YM.MatchingLedger.Gazette
