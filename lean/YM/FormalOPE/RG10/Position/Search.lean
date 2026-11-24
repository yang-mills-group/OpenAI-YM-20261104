import YM.FormalOPE.RG10.Position.Match
/-!
# Position before coupling

Require real continuum free TestSystem diagnostics with full unit-preserving, filtration
preserving, H-equivariant tangent, nested as indicated. This is RG06/11 infrastructure, not here
proving rank beyond previously accepted all-leading. Conditioning not asserting that projection of
naively chosen high solves automatically commutes downwards on regulators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Physical.Profile PertExtension.Physical PertExtension.Position
  PowerSeries Triangle
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {F : Frames G} {d k : ℕ}
local notation "M" d => Mark (Deck F d) Physical.Profile.n
abbrev Stock (F : Frames G) := ∀ i, TestSystem (Deck F i) Profile Profile.n

open Deck

structure Oriented (F:Frames G) (i:ℕ)(A:FrameAt (Deck F i) ℝ) : Prop where
  filtration v w (h:price F i v<price F i w) : A v w=0
  signed (s:Signed) : (operator (L:=Maxwell.standard F) (deck F i) A).comp (ride F s.ortho i)= (ride F s.ortho i).comp (operator (L:=Maxwell.standard F) (deck F i) A)
structure Official (D:Stock F):Prop where
  normal i : (D i).baseline= Physical.diag _
  tangent i A: A ∈ (D i).Z ↔ Oriented F i A ∧ A (start F i)=0
  fresh i : (D i).Regular (Physical.free (L:= Maxwell.standard F) (deck F i))
  tests (i j : ℕ) (h:i ≤ j) : Bindings Profile.n (climb F h) (D i) (D j)

-- on the common H,S; pose chosen once
variable (S : ∀ i, Source.SectionData (F.level i)) (H : Source.Hol G)
variable (hS : ∀ i,(S i).Sound H)(hP : ∀ i, Bid.pop (S i))

-- aggregate to keep binder lengths under control, do not hide the connection to the actual common stencils
structure Plan (F:Frames G) where
  -- profile geometry & heights not here; using Profile for arbitrary finite tests
  source : ∀ i, Source.SectionData (F.level i)
  H : Source.Hol G
  sound i : (source i).Sound H
  chosen i : Bid.pop (source i)
  liftOff : Loft F
  certified : liftOff.Level F
  stock : Stock F

namespace Plan
variable (p:Plan F)

def begins (q:ℕ+)(m : ℕ)(d : ℕ)(v:M d) := prelude p.H p.source p.sound p.chosen p.liftOff (Deck.token F d ∘ v.2) q m (fun x=>Complex.re (v.1.test (YM.points x)))
def beginsAt (q:ℕ+)(m : ℕ)(d:ℕ) := (p.stock d).leadingAdjust (Physical.free (L:= Maxwell.standard F) (deck F d))
   (fun v=> constantCoeff (p.begins q m d v))
def poses (q:ℕ+)(m d : ℕ) := (p.beginsAt q m d).position (p.begins q m d)
def dressed (q:ℕ+)(m d : ℕ) := PertExtension.Position.insert (Deck F d) Profile.n (p.begins q m d) (p.poses q m d)

variable {p} {q:ℕ+} {m:ℕ} (hq : 1 < q.val)
include hq
lemma starts (p:Plan F) (v : Mark (Deck F d) Profile.n) :
    Tendsto (fun m=> constantCoeff (p.begins q m d v)) atTop (𝓝 (Physical.free (L:= Maxwell.standard F) (deck F d) v)) := by
  rcases v with ⟨⟨n,t⟩,w⟩; exact tending _ _ _ _ _ w _ t p.certified hq
variable (h : Official p.stock)
include h
lemma complete (d) : ∀ᶠ m in atTop, (p.beginsAt q m d).Regular (fun v=> constantCoeff (p.begins q m d v)) := by
   let u d (v:Mark (Deck F d) Profile.n) := Physical.free (L:= Maxwell.standard F) (deck F d) v
   let X d (v:Mark (Deck F d) Profile.n):= PowerSeries.C (u d v)
   let a m d (v:Mark (Deck F d) Profile.n):=PowerSeries.C (constantCoeff (p.begins q m d v))
   have hh : ∀ v : M d, AlignSeries atTop (fun m=> a m d v) (X d v) := fun v => AlignSeries.scalar_C _ _ (starts hq p v) -- inspect args order
   have he := (p.stock d).leading_achieved (X d) (fun i=> a i d) (by simpa only [X,u,constantCoeff_C] using h.fresh d) hh
   change ∀ᶠ m in atTop,((p.stock d).leadingAdjust (fun i=>constantCoeff (X d i)) (fun i=>constantCoeff (a m d i))).Regular (fun i=>constantCoeff (a m d i)) at he
   simpa only [beginsAt,X,u,a,constantCoeff_C] using he

-- strongest nested proof: equality across ALL larger heights separately through their periods
private abbrev climbTo (hd:d ≤ k) := ascend Profile.n (climb F hd)
omit h hq in
lemma begins_restrict (p:Plan F) (q:ℕ+)(m:ℕ)(hd:d ≤ k) : p.begins q m d = p.begins q m k ∘ climbTo (F:=F) hd := rfl
omit h hq in
lemma fresh_clips (hd:d ≤ k) : Physical.free (L:= Maxwell.standard F) (deck F d)= Physical.free (L:= Maxwell.standard F) (deck F k) ∘ climbTo (F:=F) hd := by
  funext v; obtain ⟨⟨n,t⟩,v⟩:=v
  change Physical.free _ _= Physical.free (L:= Maxwell.standard F) (deck F k) ⟨⟨n,t⟩,climb F hd ∘ v⟩
  -- avoid Test point inside
  rw [vision,vision]; simp_rw [Function.comp_apply,← cabin,writes_higher]

lemma binding (hd:d ≤ k) : ∀ᶠ m in atTop,
    Bindings Profile.n (climb F hd) (p.beginsAt q m d) (p.beginsAt q m k) := by
  let a (i)(v : M i):= Physical.free (L:= Maxwell.standard F) (deck F i) v
  let f (m) (d) (v:M d):=constantCoeff (p.begins q m d v)
  have he : Bindings Profile.n (climb F hd) (p.stock d) (p.stock k):= h.tests d k hd
  have hf (m) : f m d=f m k ∘ climbTo (F:=F) hd := by simp_rw [f, p.begins_restrict _ _ hd]; rfl
  unfold Plan.beginsAt; change ∀ᶠ m in atTop, Bindings Profile.n (climb F hd) ((p.stock d).leadingAdjust (a d) (f m d)) ((p.stock k).leadingAdjust (a k) (f m k))
  have hy : a d=a k ∘ climbTo (F:=F) hd:=fresh_clips ..
  simp_rw [hf,hy]; exact he.rebind _ _ (climb_inj F hd) (hy ▸ h.fresh d) (h.fresh k) (fun v=> starts hq p v)

theorem shipped (hd:d ≤ k) : ∀ᶠ m in atTop, p.poses q m d= clip (climb F hd) (p.poses q m k) ∧ p.dressed q m d = p.dressed q m k ∘ ascend Profile.n (climb F hd) := by
  filter_upwards [binding hq h hd, complete hq h d, complete hq h k] with m he hd' hk
  have hu:=p.begins_restrict q m hd
  have he' : p.poses q m d= clip (climb F hd) (p.poses q m k):=by
    unfold poses; rw [hu]; exact he.cast (climb_inj F hd) hd' hk
  refine ⟨he',?_ ⟩
  funext v; unfold dressed; erw [he',hu]; exact (promote _ _ _ _ _ (climb_inj F hd) (he.atCenter _)).symm

-- normalized prior to the coupling-solving and mass-independent grading adjustment
lemma proclaimed (d : ℕ) : ∀ᶠ m in atTop, ∀ r:ℕ,
    (p.stock d).select (fun v=>coeff r (p.dressed q m d (markIn _ v)))= if r=0 then (p.stock d).target else 0 := by
  filter_upwards [complete hq h d] with m hm r
  exact TestSystem.normalizes (p.beginsAt q m d) hm r

-- express B0 near identity and B_{>0} tangent: the formal frame precomposition preserves the unit and filtration/H here; not internal boundedness.
omit hq in
theorem state (q:ℕ+)(m d n:ℕ) : ∃ Z':FrameAt (Deck F d) ℝ, Oriented F d Z' ∧ Z' (start F d)=0 ∧
    (fun i j=>coeff n (p.poses q m d i j))= if n=0 then Physical.diag _ + Z' else Z' := by
  obtain hN|hN:=eq_or_ne n 0
  · subst n; let b:= (p.stock d).branch (Physical.free (L:=Maxwell.standard F) (deck F d)) ((fun i=> constantCoeff (p.begins q m d i)) ∘ markIn (p.stock d).tests)
    refine ⟨b.val, (h.tangent d _ |>.mp b.property).1,(h.tangent d _ |>.mp b.property).2,?_⟩
    simp only [poses, coeff_zero_eq_constantCoeff_apply,TestSystem.position_zero,Plan.beginsAt,TestSystem.leadingAdjust, ↓reduceIte]; rw [h.normal]
  have hz : (fun i j=>coeff n (p.poses q m d i j))∈ (p.stock d).Z := TestSystem.positive_variation (p.beginsAt q m d) _ n hN
  exact ⟨_, (h.tangent d _|>.mp hz).1,(h.tangent d _|>.mp hz).2, (if_neg hN).symm⟩

lemma poses_zero (i j : Deck F d): Tendsto (fun m=> constantCoeff (p.poses q m d i j)) atTop (𝓝 (Physical.diag _ i j)) := by
  let a:=Physical.free (L:=Maxwell.standard F) (deck F d)
  let b m:= fun v : Mark _ Profile.n=>constantCoeff (p.begins q m d v)
  let D:=p.stock d;
  have he : Tendsto (fun m=>b m ∘ markIn (arity:=Profile.n) (J:=Deck F d) D.tests) atTop (𝓝 (a∘ markIn D.tests)):= tendsto_pi_nhds.mpr fun _=> starts hq p _
  have hc : Tendsto (fun u:D.Z=> D.baseline i j+ u.val i j) (𝓝 (0:D.Z)) (𝓝 (D.baseline i j+ (0:D.Z).val i j)):=by apply Continuous.tendsto; exact continuous_const.add ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
  simp_rw [poses,TestSystem.position_zero];
  apply (hc.comp ((D.tends a (h.fresh d)).comp he |>.snd_nhds)).mono_right (le_of_eq ?_); congr 1; simp [D,h.normal]

end Plan
end YM.FormalOPE.RG10.Position
