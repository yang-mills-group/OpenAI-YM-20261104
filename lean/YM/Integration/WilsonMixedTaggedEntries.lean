import YM.RG05Readout.Many.Consider

/-! An actual mixed activity is entered exactly once in the lifted catalogue.
The selected alternative depends only on its monomial. It is independent of
the field, support, activity and later date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedEntries
open Finset Function Set Marker RG05Readout.Many Lattice Wilson RG MergeProof Accent
open Push GridApprox.Nil Ac AbsoluteSums
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V] [Fintype V] {B : Census V}
local notation "Bₜ" => Lift B (Prod.fst : V × Bool → V)

def base (x : (Bₜ).Mode) : B.Mode :=
  (show Lit B Prod.fst x.val from (Finset.mem_filter.mp x.property).2).climb

def selected (s : Finset V) : Option V := if h : s.Nonempty then some h.choose else none

def place (x : B.Mode) (v : V) : V × Bool := (v,decide (some v = selected x.val))

omit [Fintype V] in
private theorem injective_place (x : B.Mode) : Injective (place x) :=
  fun _ _ h => congrArg Prod.fst h

omit [Fintype V] in
private theorem image_place (x : B.Mode) : (x.val.image (place x)).image Prod.fst = x.val := by
  simp [Finset.image_image,place,Function.comp_def]

def charged (x : B.Mode) : (Bₜ).Mode := by
  refine ⟨x.val.image (place x),(chamber B Prod.fst) _ ⟨?_,?_⟩⟩
  · rw [image_place]
    exact x.property
  · intro a ha b hb he
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hb
    exact congrArg (place x) he

@[simp] theorem base_charged (x : B.Mode) : base (charged x)=x :=
  Subtype.ext (image_place x)

theorem card_charged (x : B.Mode) : (charged x).val.card=x.val.card :=
  Finset.card_image_of_injOn (injective_place x).injOn

theorem toll_charged (w : V → ℝ) (x : B.Mode) :
    Poly.toll (w ∘ Prod.fst) (charged x) = Poly.toll w x := by
  change (∏ v ∈ x.val.image (place x),w v.1)=∏ v ∈ x.val,w v
  rw [Finset.prod_image (injective_place x).injOn]
  rfl

def pack (c : ℂ) (p : Poly B) : Poly Bₜ :=
  ∑ x:B.Mode, Poly.send (charged x) (c*p.part x)

theorem part_pack (c : ℂ) (p : Poly B) (y : (Bₜ).Mode) :
    (pack c p).part y = if y=charged (base y) then c*p.part (base y) else 0 := by
  rw [pack,Poly.part_sum,sum_eq_single (base y),Poly.part_send]
  · intro x _ hx
    simp only [Poly.part_send,if_neg (show y≠charged x from fun he=>hx (by rw [he,base_charged]))]
  simp

private theorem tagged_product (z : ℂ) (x : B.Mode) (h : x.val.Nonempty) :
    (∏ v ∈ (charged x).val, if v.2 then z else 1) = z := by
  change (∏ v ∈ x.val.image (place x),if v.2 then z else 1)=z
  rw [Finset.prod_image (injective_place x).injOn]
  simpa [place,selected,h] using
    (Finset.prod_ite_eq_of_mem' x.val h.choose (fun _=>z) h.choose_spec)

/-- Every charged mixed monomial has precisely one factor z under this
specialization, irrespective of its number of physical slots. -/
theorem unpack {p : Poly B} (hp : p.part B.quiet = 0) (c z : ℂ) :
    feed (fun v:V×Bool=>if v.2 then z else 1) (chamber B Prod.fst) (pack c p) =
      (z*c) • p := by
  conv_rhs => rw [← Poly.studs p,Finset.smul_sum]
  rw [pack,map_sum]
  apply sum_congr rfl
  intro x _
  rw [mouth,move,dif_pos (show Lit B Prod.fst (charged x).val from (mem_filter.mp (charged x).property).2)]
  change Poly.send (base (charged x)) (_*(c*p.part x)) = (z*c) • Poly.send x (p.part x)
  rw [base_charged,← YM.Multi.send_scale]
  by_cases h : x.val.Nonempty
  · rw [tagged_product z x h,mul_assoc]
  have he : x=B.quiet := Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp h)
  rw [he,hp]
  simp

variable {n : Side} {G : Gauge} {o : V → Site n} {t : ℝ}
variable {T : Support n} {F : Config G n → Poly B}

theorem borne (c : ℂ) (h : Borne o T F t) :
    Borne (o ∘ Prod.fst) T (fun U=>pack c (F U)) t := by
  refine ⟨fun U U' ha hb=>congrArg (pack c) (h.home U U' ha hb),
    fun g U=>congrArg (pack c) (h.turns g U),fun y=>?_,fun U y outside=>?_⟩
  · simp_rw [part_pack]
    split
    · exact (h.me _).const_mul c
    · exact measurable_const
  rw [part_pack]
  split
  · rw [h.scope U (base y) ?_,mul_zero]
    intro allowed
    apply outside
    intro v hv
    exact allowed (Finset.mem_image_of_mem Prod.fst hv)
  · rfl

private theorem unpacks_nonzero (c : ℂ) {p : Poly B} (nz : pack c p ≠ 0) : p ≠ 0 := by
  intro he
  apply nz
  simp [pack,he]

private theorem pack_rises (c : ℂ) {p : Poly B} (h : rises p) : rises (pack c p) := by
  intro x hx
  rw [part_pack] at hx
  split at hx
  next he =>
    calc 2 ≤ (base x).val.card := h (base x) (right_ne_zero_of_mul hx)
         _ = x.val.card := (show Lit B Prod.fst x.val from (mem_filter.mp x.property).2).keep_count
  next => contradiction

variable {H : Support n → Config G n → Poly B} {K : Box n → Config G n → Poly B}
theorem carton (c : ℂ) (h : Carton o H K t) :
    Carton (o ∘ Prod.fst) (fun i U=>pack c (H i U)) (fun i U=>pack c (K i U)) t := by
  constructor
  · intro i
    obtain ⟨b,m⟩ := h.exp i
    refine ⟨⟨borne c b.toBorne,fun U nz=>b.permits U (unpacks_nonzero c nz),?_⟩,
      fun U=>pack_rises c (m U)⟩
    intro U
    rw [part_pack]
    have he : base (Bₜ).quiet = B.quiet := Subtype.ext (by simp [base,Lit.climb,Census.quiet])
    rw [he,b.sil]
    simp
  · intro i
    obtain ⟨f,m⟩ := h.flag i
    exact ⟨⟨borne c f.toBorne,fun U nz=>f.permits U (unpacks_nonzero c nz)⟩,
      fun U=>pack_rises c (m U)⟩

end YM.Integration.WilsonMixedTaggedEntries
