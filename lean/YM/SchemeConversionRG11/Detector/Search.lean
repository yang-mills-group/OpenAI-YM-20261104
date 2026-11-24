import YM.SchemeConversionRG11.Detector.Coordinates

/-! The local normalization using a single implicit branch around the free point. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Detector.Poll
open Function Filter Maxwell Issue Series Pert.Position Affine Orbit
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {d n : ℕ} (Q : Poll F d)

abbrev fares (A : Issue F d) : Series (Buffer F d) := fun i ↦ Q.fareL (Q.getTest A i)

def target : Series (Buffer F d) := record (fun _ ↦ Q.scan (Q.blank,0))

/-- Separated symmetry-orbit normalization equations. -/
def Pinned (A : Issue F d) (X : Series (Buffer F d)) (n : ℕ) := Through n (Q.fares (imprint X A)) Q.target

lemma validates {A : Issue F d} {B : Series (Buffer F d)} {v : ℝ → Q.Inputs} {w : ℝ → Buffer F d}
    (hA : Represents n v (Q.getTest A)) (hw : Represents n w B) :
    Represents n (fun t ↦ Q.resolve (v t, w t)) (Q.getTest (imprint B A)) := by
  let u := fun t ↦ Q.resolve (v t, w t)
  have h : Represents n u (record u) := record_represents ((hA.pair hw).lift Q.resolving.contDiffAt).regular
  apply h.congr
  intro j hj; funext i
  let L := Q.tapeL i
  have hp := (h.linear (F:=Tape F d (Q.table i).r ℂ) L)
  have ht := hA.linear (F:=Tape F d (Q.table i).r ℂ) L
  exact hp.unique (Tape.tape_jet hw ht) j hj

lemma total_fares (A : Issue F d) (V : Series (Buffer F d)) :
    liftJet Q.location (both (Q.getTest A) V) = both (Q.getTest A) (Q.fares (imprint V A)) := by
  funext j
  have HA := trunc_represents (Q.getTest A) j
  have HV := trunc_represents V j
  have ht := Q.validates HA HV
  have hu := ht.linear (F:=Buffer F d) Q.fareL
  exact ((HA.pair HV).lift Q.chartRegular.contDiffAt).unique (HA.pair hu) j le_rfl

theorem discovers : ∃ φ, Reports Q.scan Q.blank 0 φ := Reports.of_square Q.scanner.contDiffAt Q.effective

def solution := Classical.choose Q.discovers

def press (A : Issue F d) := liftJet Q.solution (Q.getTest A)

theorem eventually_presses :
    ∀ᶠ v in 𝓝 Q.blank, Fits (Q.solution v) ∧
    ∀ A : Issue F d, Q.getTest A 0 = v → ∀ p, Q.Pinned A (Q.press A) p := by
  have h : Reports Q.scan Q.blank 0 Q.solution := Classical.choose_spec Q.discovers
  have ht : Tendsto Q.solution (𝓝 Q.blank) (𝓝 0) := h.fixes ▸ h.diff.continuousAt.tendsto
  filter_upwards [ht.eventually fits_zero.surround, h.diff.eventually (by simp),
    eventually_eventually_nhds.mpr h.curves] with v hv hv' hp
  refine ⟨hv, fun A ha p ↦ ?_⟩; subst v
  have H := trunc_represents (Q.getTest A) p
  have he : Represents p (Q.solution ∘ trunc (Q.getTest A) p) (Q.press A) := H.lift hv'
  have hz := Q.validates H he |>.linear (F:=Buffer F d) Q.fareL
  have hu : ∀ᶠ i in 𝓝 (0:ℝ), scan Q (trunc (Q.getTest A) p i, (solution Q ∘ trunc (Q.getTest A) p) i) = scan Q (Q.blank,0) :=
    H.regular.continuousAt.tendsto.eventually (by rw [H.value]; exact hp)
  exact hz.unique (Represents.germ (γ := fun _ ↦ Q.scan (Q.blank,0)) (record_represents contDiffAt_const) hu)

theorem starts_zero {A : Issue F d} (he : A.Twist) : Q.press A 0 = 0 := by
  have hw : Q.getTest A 0 = Q.blank := funext (fun i ↦ he (Q.table i).r _)
  rw [press, liftJet_zero,hw]; exact (Classical.choose_spec Q.discovers).fixes

theorem captures {A : Issue F d} (he : A.Twist) (p : ℕ) : Q.Pinned A (Q.press A) p :=
  (mem_of_mem_nhds Q.eventually_presses).2 A (funext fun i ↦ he (Q.table i).r _) p

/-- Local uniqueness for each finite jet (can be applied even along a regulator where
  only **zeroth** coefficients already approach this point). -/
theorem close_inj : ∀ᶠ (v : Q.Whole × Buffer F d) in 𝓝 ((Q.blank,(0:Buffer F d)),(0:Buffer F d)),
    ∀ A, ∀ u w : Series (Buffer F d), Q.getTest A 0 = v.1.1 → u 0 = v.1.2 → w 0 = v.2 →
      ∀ p, Through p (Q.fares (imprint u A)) (Q.fares (imprint w A)) → Through p u w := by
  let r : Q.Whole × Buffer F d → Q.Whole × Q.Whole := fun v ↦ (v.1,(v.1.1,v.2))
  have hr : Continuous r := continuous_fst.prodMk ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have H := eventually_chart_inj (E:=Q.Whole) (F:=Q.Whole) (f:=Q.location) (x:=(Q.blank,0)) Q.chartRegular.contDiffAt Q.coordinateRank
  have hyT : Tendsto r (𝓝 ((Q.blank,(0:Buffer F d)), (0:Buffer F d))) _ := hr.tendsto _
  filter_upwards [hyT.eventually H] with v hv
  intro A u w ha hx hy p he
  have heq : Through p (both (Q.getTest A) u) (both (Q.getTest A) w) := by
    apply hv
    · exact Prod.ext ha hx
    · exact Prod.ext ha hy
    rw [Q.total_fares, Q.total_fares]; exact Through.rfl.both he
  exact fun j hj ↦ congrArg Prod.snd (heq j hj)

theorem unique_frame {A : Issue F d} {X : Series (Buffer F d)} (hX : X 0 = 0) (hA : Twist A)
    (hv : Q.Pinned A X n) : Through n X (Q.press A) :=
  mem_of_mem_nhds Q.close_inj A _ _ (funext (fun i ↦ hA (Q.table i).r _)) hX
    (Q.starts_zero hA) n (hv.trans (Q.captures hA n).symm)

/-- Even composing formal series of a convergent (fixed-order) trajectory of arrays doesn't
  lose information in the press at this order. No convergence of the original bare arrays
  assumed here; typically apply on *changed* columns/parameters on the same regulator.* -/
theorem converges_test {I : Type*} {l : Filter I} {A : I → Issue F d}
    {X : Issue F d} (hx : Limits n l A X) :
    Converges n l (fun i ↦ Q.getTest (A i)) (Q.getTest X) :=
  fun p hp ↦ tendsto_pi_nhds.mpr (fun i ↦ hx (Q.table i).r _ p hp)

theorem convergence {I : Type*} {l : Filter I} {A : I → Issue F d}
    {X : Issue F d} (hX : Twist X) (hx : Limits n l A X) :
    Converges n l (fun i ↦ Q.press (A i)) (Q.press X) := by
  refine (Q.converges_test hx).lift ?_
  change ContDiffAt ℝ ω Q.solution _
  rw [show Q.getTest X 0 = Q.blank from funext (fun i ↦ hX (Q.table i).r _)]
  exact (Classical.choose_spec Q.discovers).diff

end YM.SchemeConversionRG11.Detector.Poll
