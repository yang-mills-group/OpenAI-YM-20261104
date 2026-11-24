import YM.RG02.Native.Publish
import YM.Next.FOUNDATIONS.LinkBounds

/-!
# Projective jet assembly from local practices

`Respects -- germ inputs; `JetIs` can use only through-order publishers
when proof-minimal. Contractions between common palettes via slots on Torus.
No graph or loop here. Inversions / rotations can use a projector straight
from their Laurent readers if only jets align. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Native
open Function Filter Finset Lattice RG Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology ContDiff
variable {α β A Z: Type}

abbrev Ground (α:Type)(n:Side) := Leaf α n → ℝ
abbrev Stalk (α β Z:Type)(n:Side) := Leaf β n→ Ground α n → Z
abbrev Stencil (α β Z:Type):= (n:Side)→Stalk α β Z n
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype α]
variable {n m:Side}

-- coordinates are real; omitted root position in `Cover` read only
-- along basis i cost pulses. Use marker modalities separately.
def pulse (i:Leaf α n): Ground α n:= Pi.single i 1
lemma pullField (x:Ground α n) : x = ∑ i:Leaf α n, x i • pulse i:=by
    ext1 a; rw [Finset.sum_apply,Finset.sum_eq_single a]; simp [pulse]; intro k _ hk; simp [pulse, Pi.single_eq_of_ne hk.symm]; simp
variable [Fintype A]

def expand (K:OnTorus α β A Z n)(i:Leaf β n)(v:A→Ground α n) := ∑ j:A→Leaf α n,(∏ a:A,v a (j a)) • K i j
lemma pulls (L : ContinuousMultilinearMap ℝ (fun _ : A=> Ground α n) Z)(v:A→Ground α n):
    L v = ∑ j:A→Leaf α n,(∏ a:A,v a (j a)) • L (pulse ∘ j) :=by
    change L.toMultilinearMap _=_; conv_lhs=> rw [show v=(fun i:A=>∑ k:Leaf α n,v i k • pulse k) from funext fun i=> pullField (v i)]
    rw [MultilinearMap.map_sum]; exact sum_congr rfl fun j _=> MultilinearMap.map_smul_univ _ (fun i=> v i (j i)) _
lemma samples (K:OnTorus α β A Z n)(i:Leaf β n)(j:A→Leaf α n) : expand K i (pulse ∘ j)=K i j:=by
    have hh (j' : Leaf α n)(v : Leaf α n) : pulse j' v=if v=j' then 1 else 0:= by unfold pulse; rw [Pi.single_apply]
    unfold expand; rw [Finset.sum_eq_single j]; simp [hh]
    intro a _ ha; obtain ⟨l,hl⟩:=Function.ne_iff.mp ha; rw [Finset.prod_eq_zero (Finset.mem_univ l) (show (pulse ∘ j) l (a l)= (0:ℝ) by rw [comp_apply,hh,if_neg hl]),zero_smul]; simp

-- projective map always use `+` ; linear and phase blind

def weave (α:Type)[Fintype α](h:divides n m)(o:Site n) : Ground α n →L[ℝ] Ground α m:= ContinuousLinearMap.pi fun i:Leaf α m=> ContinuousLinearMap.proj (φ:=fun _=>ℝ) (collapse h o i)
@[simp] lemma looms (h:divides n m)(o:Site n)(x:Ground α n)(j:Leaf α m): weave α h o x j=x (collapse h o j):= rfl

-- PRACTICAL projective identity could instead be acquired from native publisher on vertices only.
def collates (t:ℕ)(U:PeriodicTable α β A Z) := ∀ n m (h:divides n m)(o:Site n)(i:Leaf β m)(v:A→Ground α n), t≤n.val→
    expand (U n) (collapse h o i) v=expand (U m) i (weave α h o ∘ v)
lemma receipt (t:ℕ)(U:PeriodicTable α β A Z): coherent t U ↔ collates t U:=by
    constructor
    · intro hp n m h o i v hn
      unfold expand; simp_rw [hp n m h o i _ hn, Finset.smul_sum]
      rw [Finset.sum_comm]; apply sum_congr rfl; intro x _
      rw [sum_eq_single (collapse h o ∘ x),if_pos rfl]; rfl
      intro b _ hh; rw [if_neg hh.symm,smul_zero]; simp
    intro hp n m h o i j hn
    rw [← samples (U n) (collapse h o i) j, hp n m h o i _ hn,expand]; apply sum_congr rfl; intro k _
    split; rename_i H
    · simp_rw [← H]; simp [pulse]
    rename_i H; obtain ⟨l,hl⟩:= Function.ne_iff.mp H
    rw [prod_eq_zero (mem_univ l) ?_,zero_smul]; simp only [pulse,comp_apply,looms]; apply Pi.single_eq_of_ne hl

section production
variable {U : Stencil α β Z}

def shape (k:ℕ)(U:Stalk α β Z n) : OnTorus α β (Fin k) Z n := fun i j=>iteratedFDeriv ℝ k (U i) 0 (pulse ∘ j)
abbrev shaped (U:Stencil α β Z)(k:ℕ) : PeriodicTable α β (Fin k) Z := fun n=>shape k (U n)

omit [Fintype A] in -- A doesn't occur
lemma shape_expanded (k:ℕ)(U:Stalk α β Z n)(i:Leaf β n)(v:Fin k→Ground α n) : iteratedFDeriv ℝ k (U i) 0 v = expand (shape k U) i v:= pulls _ v

variable {η:ℝ}
def fair (t r:ℕ)(U:Stencil α β Z) := ∀ n: Side,t≤n.val → ∀ i, ContDiffAt ℝ r (U n i) 0
-- Germ sufficient OR exact finite jet projectivity

def respects (t:ℕ)(U:Stencil α β Z) := ∀ n m (h:divides n m)(p:Site n)(i:Leaf β m),t≤n.val→
    U n (collapse h p i) =ᶠ[𝓝 0] U m i ∘ (weave α h p)
def through (t r:ℕ)(U:Stencil α β Z) := ∀ k≤r,coherent t (shaped U k)

lemma shares {U:Stencil α β Z}{t r}(he:respects t U)(hf:fair t r U) : through t r U:= by
    intro k hk; apply (receipt t _).mpr
    intro n m h o i j hn; simp_rw [shaped, ← shape_expanded]
    have hm : ContDiffAt ℝ k (U m i) 0:= (hf m (hn.trans (Nat.le_of_dvd m.pos h)) i).of_le (Nat.cast_le.mpr hk)
    rw [((he _ _ h o _ hn).iteratedFDeriv ℝ k).self_of_nhds,Next.Foundations.jets_linear (weave α h o) hm]; rfl

-- Supplied from germ & projection widths. -/
def funded (t r:ℕ)(u:ℝ)(U:Stencil α β Z)(a:ℕ→ℝ):= ∀ k≤r,charged t u (a k) (shaped U k)

theorem issued [ProperSpace Z] [Fintype β] {t r}{v:ℝ}{w:ℕ→ℝ} (h:through t r U)(he:funded t r v U w)(hv:0<v)(hc:∀ k≤r,0 ≤ w k) :
    ∀ k≤r,∃ F:CoverForm α β (Fin k) Z,narrow v (w k) F ∧
      ∀ n:Side,t≤ n.val → ∀ i j,iteratedFDeriv ℝ k (U n i) 0 j= expand (imprint F n) i j :=by
    intro k hk; obtain ⟨F,hp,hh⟩:=publish hv (hc k hk) (he k hk) (h k hk); exact ⟨F,hp,fun n hn i j=>by rw [← hh n hn]; apply shape_expanded⟩
end production
end YM.RG02.Native
