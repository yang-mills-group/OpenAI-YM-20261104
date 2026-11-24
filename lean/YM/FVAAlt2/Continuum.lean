import YM.FVAAlt2.Library

/-!
# Continuum comparison for the top regulator with a bare MS dictionary

Primary concrete supplier. NO assumed identity to LPT and unknown
error estimate between two diagram systems. This is the **orbit tree**
(and so FormalOPE.RG10 InversionTop) normalized coefficient with marks and slot powers,
compared to the independent MS prescription. The `Library` lets users
specify actual stencils in that `LitBook`; using `always_L` unconditionally
constructs one, but it still refers just to LitBook physical fields, not to
the physical construction. The conversion covers every horizon d on the labelled
placements p. A length-independent position scheme and the attachment of the
local chain require additional data.

The (arbitrary) local analytic chart for group Haar, list, family of real mark readers, etc.
are fixed. No constants uniform in library or vanishing analytic
remainders of unexpanded densities here. The real analytic expansions at the
trivial saddle and universes of `Library.ok` are as in `Fixed`; they use proper
ordinary-power expansions AFTER including incoming normalization. The remaining
field dress matrix applied here is `oil`, WITH its spacing-dependence: neither side
of any regulator estimate is subjected to unbounded linear change after taking a limit.
Position-frame identification of the incoming data by physical rank and θ solve
remains a separate required step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Billing
open MS MS.Koszul MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Vista MS.Vane MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog
open MS.Dial MS.Rake MS.Tide.PeakT MS.Tone
open Function Finset Filter Topology Precision Pert.Orb Lattice MeasureTheory
open scoped PowerSeries ContDiff
variable {I W : Type} [LinearOrder W] {l: Filter I} {T: Dial.Trial I W} {μ:ℝ}

omit [LinearOrder W] in
lemma SideFunding (h: Dial.Uses T l μ) : ∀ᶠ i in l,Admissible (dimT T.side i) := by
 filter_upwards [h.upright.eventually_ge_atTop 4,h.super (1:ℝ)] with i he ht
 rw [one_mul] at ht; have hb:= Real.log_le_sub_one_of_pos (Vista.δ_p T.side i)
 refine ⟨ ?_,?b ⟩; case b=> rw [dimT,cap_val]; simp
 suffices hw : (4:ℝ) ≤ Vista.tickA T.side i by exact_mod_cast hw
 linarith

variable {G:Gauge}{B:MS.Local.Physical.Deck G} (Z:LitBook B)(P:ChartRatio G)(R: LocalRatio P){F:MS.Land.Booked B}(S:MS.Land.MS_Data G F)
variable (p: W→Rake.Label B)(Λ:Library Z){X:Fleet.Terrify W I}(Q:MS.Land.Prescription B)
variable (h: coherent F S Z p T μ true Q l X)
set_option linter.unusedSectionVars false

def readTop (μ:ℝ)(T: Trial I W) : Terrify W I:= fun s n i=> PowerSeries.coeff n (ΓReg Z P p Λ Q s (fun w=> T.off w i) (T.head i) (μ-T.profile.θ i) (dimT T.side i))

include h R
lemma same_coefficient {i:I}(he: Admissible (dimT T.side i))(s:Finset W)(n:ℕ): ordZ X s n i = readTop Z P p Λ Q μ T s n i := congrFun (classicalμ (τ_nil ..) (h.cost i s) (spectrum Z P p Λ Q s (fun w=> T.off w i) (T.head i) _ he R)) n
local notation "U"=> readTop Z P p Λ Q μ T
local notation "g"=> Label.h ∘ p
lemma receipt (hc: Dial.Uses T l μ)(m:Finset W)(k:ℕ):
    twin l T.profile mildG (fare g T.profile U m k)
     (fun i=> tour S p μ (testP T i) m k) := by
  obtain ⟨ha,hv⟩:=h.bouquet m k; refine ⟨ha,PeakT.fromζ hv ?_ ⟩
  filter_upwards [SideFunding hc] with i hi; rw [Pi.sub_apply, Pi.sub_apply, fare,fare,Pi.mul_apply,Pi.mul_apply,same_coefficient Z P R S p Λ Q h hi]; -- H
lemma hits [Fintype W] {f:W→ Tone.QP}(hf:Function.Injective f)(hc:Dial.Uses T l μ)(he:Tendsto (testP T) l (𝓝 f))(m:Finset W)(k:ℕ): Tendsto (fare g T.profile U m k) l (𝓝 (tour S p μ f m k)):= by
 apply Dial.agrees _ (receipt Z P R S p Λ Q h hc m k) hc.upright; exact ((Dial.contin S p f hf m k μ).1).tendsto.comp he
omit h

def Valid (Q: MS.Land.Prescription B)(I W:Type)[LinearOrder W](T: Trial I W)(l: Filter I)(μ:ℝ)(p:W→Label B): Prop:=
 (∀ m k, twin l T.profile mildG (fare (Label.h ∘ p) T.profile (readTop Z P p Λ Q μ T) m k)
     (fun i=> tour S p μ (testP T i) m k)) ∧ (∀ [Fintype W] {f: W→ Tone.QP}, Injective f→ Tendsto (testP T) l (𝓝 f) → ∀ (m:Finset W)(k:ℕ), Tendsto (fare (Label.h∘p) T.profile (readTop Z P p Λ Q μ T) m k) l (𝓝 (tour S p μ f m k)))

theorem topMatch (hg:G.Simple): ∃ Q:MS.Land.Prescription B, MS.Land.TaylorOK S Z Q ∧
    ∀ (W I:Type)(_ :LinearOrder W)(T:Trial I W)(l:Filter I)(μ:ℝ)(p:W→Rake.Label B), Dial.Uses T l μ→ Valid Z P S Λ Q I W T l μ p:=by
 obtain ⟨Q,hQ,H⟩:=LPT_to_MS Z S hg; refine ⟨Q,hQ,?_⟩; intro W I _ T l μ p ht; obtain ⟨X,hX,H⟩:= H W I inferInstance T l μ p true ht; exact ⟨receipt Z P R S p Λ Q hX ht,fun {_ f} hf hc => hits Z P R S p Λ Q hX hf ht hc⟩

-- A version also with constructively available simultaneous limits at every separated geometry (not any diagonal).
theorem separated_tests (hg:G.Simple): ∃ Q:MS.Land.Prescription B, MS.Land.TaylorOK S Z Q ∧ ∀ (μ:ℝ) (W:Type)(_ :LinearOrder W)(_ :Fintype W)(f:W→ Tone.QP), Injective f→ ∃ T:Trial ℕ W,Dial.Uses T atTop μ ∧ Tendsto (testP T) atTop (𝓝 f)∧ ∀ p:W→Rake.Label B, Valid Z P S Λ Q ℕ W T atTop μ p:=by
 obtain ⟨Q,hQ,H⟩:= topMatch Z P R S Λ hg; refine ⟨Q,hQ,?_⟩; intro μ W _ _ f hf; obtain ⟨T,ht,he⟩:= Dial.crew f hf μ; exact ⟨T,ht,he,fun p=> H W ℕ _ T atTop μ p ht⟩
end YM.FVAAlt2.Billing

