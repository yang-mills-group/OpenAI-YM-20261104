import YM.UVExt.Consolidate
import YM.UVExt.ChainFee
import YM.UVExt.ShiftSlot

/-! Numerical tokens on the cover, irrespective of chronological history:
 rebase the SECOND path to the first terminal and wrap only after recording
 the full relative displacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Laurent Lattice Wilson RG Bid Precision
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {N : Side}

instance : Finite Step := Finite.of_surjective (fun p : Axis×Bool => Step.mk p.1 p.2) fun i=> ⟨⟨i.dir,i.neg⟩,rfl⟩
instance : Countable Slot := Countable.of_equiv _ (Equiv.ofBijective (fun p:Walk×PlaqAxes=>Slot.mk p.1 p.2) ⟨fun x y h=>Prod.ext (congrArg Slot.walk h) (congrArg Slot.plaq h), fun x => ⟨⟨x.walk,x.plaq⟩,rfl⟩⟩) -- want Countable Slot

/-- path assignment plus one color tensor component, independent of actual atom index; any
repetitions aggregated before comparing cutoffs. -/
abbrev Token (G : Gauge) (k : ℕ) := (Fin k → Slot) × (Fin k → G.ColorIndex)

def breath {k : ℕ} (p : Token G k) := ((∑ i, (p.1 i).length : ℕ) : ℝ)

lemma limited_walks (K : ℕ) : Set.Finite {l : Walk | l.length ≤ K} := by
  induction K with
  | zero => exact (Set.finite_singleton []).subset (fun x hx => by simpa using hx)
  | succ K h =>
    let s := {l : Walk | l.length ≤ K}
    refine ((Set.finite_singleton []).union ((Set.finite_univ (α:=Step) |>.prod h).image (fun p => p.1::p.2))).subset ?_
    rintro (_|⟨a,x⟩) he
    · left; rfl
    right; exact ⟨(a,x),⟨mem_univ _, by simpa using he⟩,rfl⟩

lemma breath_pos {k : ℕ} (p : Token G k) : 0 ≤ breath p := Nat.cast_nonneg _
lemma breath_top (k) : Tendsto (breath (G:=G) (k:=k)) cofinite atTop := by
  have hv i : Finite {p:Slot // p.walk.length ≤ i} := by
    letI : Finite PlaqAxes := Finite.of_injective Subtype.val Subtype.val_injective
    letI : Finite {l:Walk // l.length ≤ i} := (limited_walks i).to_subtype
    exact Finite.of_injective (fun p : {p:Slot // p.walk.length ≤ i} => ((⟨p.val.walk,p.property⟩ : {l:Walk // l.length ≤ i}),p.val.plaq))
      fun x y h=> Subtype.ext (by
         have h1 : x.val.walk = y.val.walk  := by
           exact (show _ from congr_arg (fun i => i.1.val) h)
         have h2 : x.val.plaq = y.val.plaq := by simpa using congrArg Prod.snd h
         rcases x with ⟨⟨a,b⟩,hsA⟩; rcases y with ⟨⟨c,d⟩,hsB⟩; exact congrArg₂ (α:=Walk) Slot.mk h1 h2)
  letI := fun i=> hv i
  apply tendsto_atTop.mpr; intro w
  obtain ⟨n,hn⟩ := exists_nat_ge w
  apply eventually_cofinite.mpr
  refine Set.finite_coe_iff.mp ?_
  let A := {p : Token G k | ¬ w ≤ breath p}
  have hh (p : A) (i : Fin k) : ((p:Token G k).1 i).walk.length ≤ n := by
    apply le_trans (b:=∑ i, ((p:Token G k).1 i).length) (le_trans (Nat.le_add_right ..) (Finset.single_le_sum (f:=fun i => ((p:Token G k).1 i).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)))
    apply Nat.cast_le (α:=ℝ) |>.mp
    exact (lt_of_not_ge p.property).le.trans hn
  let f (u : A) : (Fin k→{p:Slot // p.walk.length ≤ n}) × _ := (fun i=> ⟨u.val.1 i,hh u i⟩,u.val.2)
  exact Finite.of_injective f (fun i j h=> Subtype.ext (by dsimp [f] at h; cases i with | mk a ha => cases j with | mk u hb => exact Prod.ext (funext fun x => congr_arg (fun (t : (Fin k→{p:Slot // p.walk.length ≤ n}) × (Fin k→G.ColorIndex)) => (t.1 x).val) h) (by simpa using congr_arg (fun t : (Fin k→{p:Slot // p.walk.length ≤ n}) × (Fin k→G.ColorIndex) => t.2) h)))

variable {k : ℕ}

def stream (v : Dir G N) (x : Site N) (B : Token G k) := (∏ i : Fin k, sprout v x (B.1 i) (B.2 i))

/-- Atom kernel, before evaluating at an orientation or summing the site. -/
def necklace (V : ℕ → RG.Atom G k) : Token G k→ℝ := pool (fun i : ℕ × (Fin k→G.ColorIndex) => (V i.1).coeff i.2) fun i=> ⟨(V i.1).leg,i.2⟩
lemma necklaces_paid (V : ℕ→RG.Atom G k) (s C) (hh : SumBudget (fun i => (V i).budget s) C) (hs : 0<s) : Carries C s breath (necklace V) :=
    pool_money (s:=fun i => ⟨(V i.1).leg,i.2⟩) (product_money (R:=fun i=>(V i).coeff) (fun i=> (V i).length) (fun _=> Nat.cast_nonneg _) (fun i=>(V i).magnitude) (fun _=>rfl) hh) hs (fun _=>le_rfl) breath_pos

def relay (u a : Slot) : Slot := {a with walk := Lattice.reverse u.walk ++ a.walk}

def ground (a : Slot) : Slot := ⟨[],a.plaq⟩

def alignSecond (a b : Slot) := Stationary.walkSlot b.plaq (b.offset-a.offset)

def axisPair (v : Dir G N) (x:Site N) (B : Token G 2) :=
    sprout v x (ground (B.1 0)) (B.2 0) * sprout v x (alignSecond (B.1 0) (B.1 1)) (B.2 1)

def afterPair (v : Dir G N) (x:Site N) (B : Token G 2) :=
    sprout v x (ground (B.1 0)) (B.2 0) * sprout v x (relay (B.1 0) (B.1 1)) (B.2 1)

lemma advance(a : Cover)(w): stop a w=a+stop (0:Cover) w := by
  have h a b (w : Walk) : stop (a+b:Cover) w=a+stop b w := by induction w generalizing b with
     | nil => rfl
     | cons d w ih => rw [stop,stop,add_assoc,ih]
  simpa using h a (0:Cover) w
lemma relay_end (a b : Slot) : (relay a b).offset = (alignSecond a b).offset := by
  have hp := reverse_stop a.walk (0:Cover)
  rw [show stop 0 a.walk=a.offset from rfl, advance a.offset] at hp
  rw [Slot.offset,relay,alignSecond,stop_append, advance, Stationary.walkSlot_end,← Slot.offset, show stop (0:Cover) (Lattice.reverse a.walk) = -a.offset by exact eq_neg_of_add_eq_zero_right hp,sub_eq_neg_add]

lemma walk_size (w : Walk) (x : Cover) : size (stop x w) ≤ w.length + size x := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons d l ih =>
    rw [stop,List.length_cons]
    have hv : size (d.vec:Cover)≤1 := by cases d with | mk i d => cases d <;> simp [Step.vec,Laurent.size,step,Pi.single_apply] <;> simp only [apply_ite,Int.natAbs_zero,Int.natAbs_one,Finset.sum_ite_eq',Finset.mem_univ,if_true,le_refl]
    have hx := size_add x d.vec
    specialize ih (x+d.vec); omega
lemma length_offset (x : Slot) : size x.offset ≤ x.walk.length := by simpa [Slot.offset,Laurent.size] using walk_size x.walk 0
lemma align_status (a b : Slot) : max (relay a b).length (alignSecond a b).length ≤ a.length+b.length := by
  have hk := size_add b.offset (-a.offset)
  have hl : size (-a.offset) = size a.offset := by simp [Laurent.size, Pi.neg_apply]
  rw [alignSecond, Stationary.walkSlot_cost,sub_eq_add_neg]
  let p := relay a b
  have hp : p.walk.length = a.walk.length + b.walk.length := by simp only [p,relay,Lattice.reverse,List.length_append,List.length_map,List.length_reverse]
  change max p.length _ ≤ _
  simp only [Slot.length,max_le_iff, hp]; have ha:=length_offset a; have hb := length_offset b
  omega

private lemma ad_inner (u : G.El) (x y : G.Color) : inner ℝ (G.adjoint u x) (G.adjoint u y) = inner ℝ x y := by
  have h := norm_add_sq_real (G.adjoint u x) (G.adjoint u y)
  rw [←map_add] at h
  simp only [G.norm_adjoint, norm_add_sq_real x y] at h
  linarith

lemma sub_at (a b : Slot) (x) (U : Config G N) :
    inner ℝ (a.atSite U x) (b.atSite U x) = inner ℝ ((ground a).atSite U (stop x a.walk)) ((relay a b).atSite U (stop x a.walk)) := by
  simp_rw [Work.F03.atSite_path]
  have ha := attach_back x a.walk
  have hp := relay_end a b
  have h₁ : Work.F03.slotFace (ground a) (stop x a.walk) = Work.F03.slotFace a x := by rw [ha]; simp [Work.F03.slotFace,ground,Slot.offset,stop, add_comm]
  have h₂ : Work.F03.slotFace (relay a b) (stop x a.walk) = Work.F03.slotFace b x := by
    unfold Work.F03.slotFace; rw [hp, alignSecond,Stationary.walkSlot_end, map_sub, ha]; dsimp [relay,alignSecond,Stationary.walkSlot,Slot.offset]; rw [show ∀ a b : Site N, a-b+(x+b)=a+x by intros; abel]
  rw [h₁,h₂,show travel U _ (ground a).walk=1 by rfl, G.adjoint_one]
  simp only [relay,travel_append,travel_reverse,G.adjoint_mul]
  let g:= travel U x a.walk
  change inner ℝ (G.adjoint g _) _ = inner ℝ _ (G.adjoint g⁻¹ _); conv_rhs => rw [← ad_inner g, ←Gauge.adjoint_mul, mul_inv_cancel,G.adjoint_one]
  rw [reverse_stop]

end YM.UVExt.Paths
