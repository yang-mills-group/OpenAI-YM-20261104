import YM.Comparison.RG02.Sky.Rig
import YM.Comparison.RG02.Cumulants.Cloud
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion

/-!
# Finite polynomial rows and the literal connected pairing program

Each row retains its own finite choices, ordered leg occurrences, complex
coefficient and original covariance indices. The only rearrangement below
is finite multilinearity. Every entry of Traces.circle/Rig.program remains
in the sum, including repeated entries and the empty path at a lone
constant vertex. Empty marker coefficients vanish because the logarithm
of the normalized constant coefficient is zero, not because vacuum
vertices or vacuum diagrams have been discarded.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteConnectedProgram

open Finset Function
open YM.Marker YM.Multi YM.Next.Rank
open YM.Comparison.RG02.Cumulants
open YM.Comparison.RG02.Sky
open YM.Extra.Trajectories (connected Names)
open scoped BigOperators Classical

/-- A finite, unsymmetrized polynomial presentation. -/
structure Rows (I : Type) where
  Choice : Type
  finiteChoice : Fintype Choice
  Leg : Choice → Type
  finiteLeg : ∀ a, Fintype (Leg a)
  coefficient : Choice → ℂ
  index : ∀ a, Leg a → I

attribute [instance] Rows.finiteChoice Rows.finiteLeg

namespace Rows

variable {I : Type}

def polynomial (D : Rows I) : Normal.poly I :=
  ∑ a, D.coefficient a • Normal.glyphs (D.index a) univ

end Rows

/-- Finite cumulant multilinearity from the native addition and scalar identities. -/
private def stockCumulant {I V : Type} [Fintype V] [AD : DecidableEq V]
    (Q : Normal.Symmetric I) :
    MultilinearMap ℂ (fun (_ : V) => Normal.poly I) ℂ where
  toFun u := (connected (moments (Stock.census V) (Normal.blend Q 0) u)).part
    (Stock.final V)
  map_update_add' {_d} a i x y := by
    have hh : _d = AD := Subsingleton.elim _ _
    subst _d
    exact cumulant_add (Normal.blend Q 0) (Normal.fresh Q 0) a
      (R := Stock.census V) (s := Stock.final V) i (mem_univ _) x y
  map_update_smul' {_d} a i c x := by
    have hh : _d = AD := Subsingleton.elim _ _
    subst _d
    exact cumulant_smul (Normal.blend Q 0) (Normal.fresh Q 0) a
      (R := Stock.census V) (s := Stock.final V) i (mem_univ _) x c

variable {I V : Type} [Fintype V] [DecidableEq V]

abbrev Assignment (D : V → Rows I) := ∀ v, (D v).Choice

abbrev Legs (D : V → Rows I) (a : Assignment D) (v : V) :=
  (D v).Leg (a v)

def fieldIndex (D : V → Rows I) (a : Assignment D) (p : Sigma (Legs D a)) : I :=
  (D p.1).index (a p.1) p.2

def coefficient (D : V → Rows I) (a : Assignment D) : ℂ :=
  ∏ v, (D v).coefficient (a v)

def pathValue (Q : Normal.Symmetric I) (D : V → Rows I)
    (a : Assignment D) (p : Rig.Record (Legs D a)) : ℂ :=
  ∏ j : Fin p.length,
    Q.cov (fieldIndex D a (p.get j).1) (fieldIndex D a (p.get j).2)

def stockValue (Q : Normal.Symmetric I) (D : V → Rows I) (root : V) : ℂ :=
  ∑ a : Assignment D, coefficient D a *
    ∑ j : Fin (Rig.program (Legs D a) root).length,
      pathValue Q D a ((Rig.program (Legs D a) root).get j)

private lemma local_word (D : V → Rows I) (a : Assignment D) (v : V) :
    Normal.glyphs ((D v).index (a v)) univ =
      Wick.word Sigma.fst (fieldIndex D a) univ v := by
  unfold Wick.word Normal.glyphs
  refine Finset.prod_bij (fun k _ => (⟨v, k⟩ : Sigma (Legs D a)))
    (fun k _ => mem_filter.mpr ⟨mem_univ _, mem_singleton_self _⟩)
    (fun k _ l _ he => Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq) ?_
    (fun _ _ => rfl)
  rintro ⟨u, k⟩ hk
  have hu : u = v := mem_singleton.mp (mem_filter.mp hk).2
  subst u
  exact ⟨k, mem_univ _, rfl⟩

/-- Complete finite multilinearity, followed by the native ordered program.
No quotient by pairings, graph isomorphism, or tensor symmetry is taken. -/
theorem stock_program (Q : Normal.Symmetric I) (D : V → Rows I) (root : V) :
    (connected (moments (Stock.census V) (Normal.blend Q 0)
      (fun v => (D v).polynomial))).part (Stock.final V) =
      stockValue Q D root := by
  let M := stockCumulant (V := V) Q
  change M (fun v => ∑ a, (D v).coefficient a •
    Normal.glyphs ((D v).index a) univ) = _
  rw [M.map_sum]
  unfold stockValue
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MultilinearMap.map_smul_univ]
  change coefficient D a *
    (connected (moments (Stock.census V) (Normal.blend Q 0)
      (fun v => Normal.glyphs ((D v).index (a v)) univ))).part
        (Stock.final V) = _
  apply congrArg (coefficient D a * ·)
  simp_rw [local_word D a]
  rw [Traces.count_charges Sigma.fst Q (fieldIndex D a) univ root
    (Fintype.card (Sigma (Legs D a))) (card_univ.le)]
  simp only [Traces.charge_prices, Rig.program, pathValue]
  rfl

variable {R : Census V}

private def selectedNames (t : R.Mode) : Names (Stock.census t.val) R where
  e := ⟨Subtype.val, Subtype.val_injective⟩
  visible s := by
    apply R.down t.property
    rintro v hv
    obtain ⟨u, _, rfl⟩ := mem_image.mp hv
    exact u.property

omit [Fintype V] in
private lemma selected_final (t : R.Mode) :
    (selectedNames t).share (Stock.final t.val) = t := by
  apply Subtype.ext
  change (univ : Finset t.val).image Subtype.val = t.val
  ext v
  constructor
  · intro hv
    obtain ⟨u, _, rfl⟩ := mem_image.mp hv
    exact u.property
  · intro hv
    exact mem_image.mpr ⟨⟨v, hv⟩, mem_univ _, rfl⟩

omit [Fintype V] in
private lemma selected_moments (Q : Normal.Symmetric I)
    (p : V → Normal.poly I) (t : R.Mode) :
    (selectedNames t).restriction (moments R (Normal.blend Q 0) p) =
      moments (Stock.census t.val) (Normal.blend Q 0) (fun v => p v.val) := by
  ext s
  change Normal.blend Q 0 (∏ v ∈ s.val.image Subtype.val, p v) =
    Normal.blend Q 0 (∏ v ∈ s.val, p v.val)
  rw [Finset.prod_image Subtype.val_injective.injOn]

private lemma selected_cumulant (Q : Normal.Symmetric I)
    (p : V → Normal.poly I) (t : R.Mode) :
    (connected (moments R (Normal.blend Q 0) p)).part t =
      (connected (moments (Stock.census t.val) (Normal.blend Q 0)
        (fun v => p v.val))).part (Stock.final t.val) := by
  have h := congrArg (fun z => z.part (Stock.final t.val))
    ((selectedNames t).connected_restrict
      ((moments_quiet (Normal.blend Q 0) p).trans (Normal.fresh Q 0)))
  rw [selected_moments] at h
  change (connected (moments R (Normal.blend Q 0) p)).part
    ((selectedNames t).share (Stock.final t.val)) = _ at h
  simpa only [selected_final] using h

/-- The empty coefficient is treated explicitly. A nonempty coefficient
uses all of its actual selected vertices, including pure vacuum vertices. -/
def modeValue (Q : Normal.Symmetric I) (D : V → Rows I) (t : R.Mode) : ℂ :=
  if h : t.val.Nonempty then
    stockValue Q (fun v : t.val => D v.val) ⟨h.choose, h.choose_spec⟩
  else 0

theorem cumulant_program (Q : Normal.Symmetric I) (D : V → Rows I)
    (t : R.Mode) :
    (connected (moments R (Normal.blend Q 0)
      (fun v => (D v).polynomial))).part t = modeValue Q D t := by
  by_cases h : t.val.Nonempty
  · rw [modeValue, dif_pos h, selected_cumulant]
    exact stock_program Q (fun v : t.val => D v.val) ⟨h.choose, h.choose_spec⟩
  · rw [modeValue, dif_neg h]
    have ht : t = R.quiet := Subtype.ext (not_nonempty_iff_eq_empty.mp h)
    rw [ht]
    exact YM.Extra.Trajectories.connected_quiet
      ((moments_quiet (Normal.blend Q 0) (fun v => (D v).polynomial)).trans
        (Normal.fresh Q 0))

/-- The original Cloud shard/composition sum, with every connected block
replaced by its exact finite ordered pairing program. -/
theorem cloud_program [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (D : Hot R → Rows I) (t : R.Mode) :
    (connected (Cloud.prescription Q hQ 0
      (fun v => (D v).polynomial))).part t =
      ∑ s ∈ shards R t, modeValue
        (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) D s := by
  rw [Cloud.prescribed_log]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact cumulant_program
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) D s

end YM.Integration.FiniteConnectedProgram
end
