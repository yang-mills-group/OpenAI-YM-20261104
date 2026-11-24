import YM.FormalBulk08.Primer.Kernel
import YM.FormalBulk08.First.Tail
import YM.FormalBulk08.Delphi.Obelisk
import YM.FormalBulk08.Sound.Kingdom

noncomputable section
set_option autoImplicit false
/-! ### Formal-coefficient integrator interface (part 1)

Here is one way to use the library on the proposed **common** physical
construction. Use any `F` you choose **on the same C** and apply
`EveryPhase.all_characters` if pursuing EveryPhase. Constructor compatibility
accepts arbitrary additional numerical requests (height and widths pre,
post-log book/rise delays, choose at construction time).

Purchases are not assumptions about fields, scaling limits, or R_k: inspect definitions
`Evergreens`, `Dahlia`, `Jolt/Dominoes`. They are certificates about ONE schedule.
Do not infer them automatically from the stock UV/Calibration: if your Step log uses
other heights make sure you carry them from launch using `canopies` (from the SAME
UV installer). Qualification requests in general can depend on the schedule; see
`Evergreens` for rooting ages & policy.

These FormalBulk08 endpoints are likewise NOT performing any claim about the
real reporting coefficients. All on the infinite Cover except torus calculations in
this calibration. See `Primer.Kernel` first.
-/
namespace YM.FormalBulk08.Primer
open Lattice Laurent Bloch RG Precision Wilson Filter Function Set
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical Matrix.Norms.Frobenius
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Gorge Lava Lotus Shore North Quire Elm Borough Spigot Delphi
open Stationary hiding seat Rays
open Aster
open PhysicalNext.Repeat.Legato Next.Foundations
variable {G : Gauge} (C:Family G) (h:G.Simple)

abbrev Noise:= C.path.levels.clock.kernel
abbrev Families:= ∀ i:ℕ,Lodge ((C.path.levels.clock.op i 0).patch)
lemma setup: Nonempty (Families C):= ⟨fun _=> routes _⟩
lemma shadeExists (G:Gauge)(h:G.Simple): Nonempty (hue G):= colorAvail G h
abbrev FamilyWindow:= windowBasis G (Noise C)

structure Announced (U:ℕ→ℕ):Prop where
    available:C.Makes
    provenance:Provenance G C (chart G)
    power: Evergreens (Noise C) herald C.labels.level C.params (chart G) (FamilyWindow C) C.path.levels
    frontloading: First.Dahlia C.path.levels (FamilyWindow C).width
    inputs (i : ℕ): Bid.pop (C.localSection i)
    soilP : Jolt (Noise C) U C.labels.level C.params (fun i=> (C.path.levels.clock.factor i).val)
    grainP: Dominoes C.path.levels U C.labels.level C.params (Noise C)
variable {C}
lemma provenance_lives (p:Provenance G C (chart G))(i : ℕ): Bid.pop (C.localSection i):= by
    obtain ⟨H,R,T,L⟩:= p
    rcases C with ⟨A,S,M,R',V,Q⟩; change M=_ at R; subst M
    change HEq R' _ at T; cases eq_of_heq T; exact Next.Foundations.valuation G _
include h
open RG.Supply Push.PriceCompiler
lemma user_input (e:ℕ)(he:4≤e)(u:ℕ→ℕ) (b:ℝ)(p:0<b) (χ:ℕ→ℕ)(P:Levels G→ Prop)(t :∀ (K:KernelChoices),K.penalty=b→ ∀ (Y:Sheet G),Y.kernel=K→ ∀ (M:Rolls Y)(X:Protection M)(V:Delays X),∃ T: Delays X,DelayLe V T ∧∀ (Z:Delays X), DelayLe T Z →∀ (B:Bar Z)(I:Wait B)(A:Levels G), Paid I A→ P A):
     ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book), Nonempty (Spec.Final C f T) ∧ C.Makes ∧ Spec.Calibrated C∧ (Noise C).penalty=b ∧ UVExtension.Oasis.Floral (hG:=h) C∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T∧(∀ d k:ℕ,∀ᶠ n in atTop,∀ r:ℕ,∀ v:Fin r→ C.book.Token,(∀ i,(v i).1 ≤ d)→ ∃ g,UVExtension.Poppy.Margins C r n k v g) ∧ Announced C u ∧ C.path.levels.clock.J 0=e ∧ χ≤(fun i=> (C.path.levels.clock.factor i).val) ∧ P C.path.levels:= by
   obtain ⟨C,f,T,H,u',hp,B,hF,v,g,h',o,G',P',hz,Q,hE,y⟩:= Delphi.monarchs h b p e he u χ P t
   refine ⟨C,f,T,H,u',hp,B,hF,v,g,⟨u',h',?_,Q,provenance_lives h',?_,?_⟩,G',hz,P'⟩ <;> rw [h'.tie,h'.stencil]
   exacts [o,y,hE]
-- fields including stencils; for more flexible quantification use directly Plateau etc.
lemma can_announce (u:ℕ→ℕ) (e:ℕ) (he:4≤e) : ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book), Nonempty (Spec.Final C f T) ∧ Announced C u ∧ C.path.levels.clock.J 0=e ∧ (Noise C).penalty=1:= by
    obtain ⟨C,f,T,H,hM,hC,hb,hE,hG,hP,h',hX,g,W⟩:= user_input h e he u 1 zero_lt_one (fun _=>0) (fun _=>True) (fun K _ Y _ M X V=> ⟨V,.refl _,fun _ _ _ _ _ _=>trivial⟩)
    exact ⟨C,f,T,H,h',hX,hb⟩
omit h

/-! Actual data to independent formal data.
Given G, C, label basis as advertised and an analytic-germ reference Chart.
Take ANY L (see `Primer.setup`, `Turner.Bank`). Marked tensors have
persisted root and test-scale/profile; distinct from translationally equivariant
vacuum tensors below. -/
variable (C) (L:Families C) (a:hue G)

-- T uses no q.
def densityCoeff (N i:ℕ) : Pot G:= model C.path.levels L (Hay.Wday _) (chart G) a N i
def normalizationCoeff (N i:ℕ) : Pence:= First.stride C.path.levels L (chart G) a N i
open PowerSeries
open Pert.Asymptotics
lemma top_power (k N q:ℕ)(hk:k≤N)(p:C.Makes):
    let β:= C.path.β N q k; let g:=regulatorRun C N q k; 0 < β∧ 0<g ∧ g^2*β=1:= by
   intro b g
   have hp := ((p.wilson.represents N q k hk).band).1; have hh:= C.path.levels.fits.delayed k
   change _≤ b at hp; have hm:(C.path.levels.clock.hatBeta k)/2≤ b:= hp; have h:0<b:=by linarith
   have he:0<Real.sqrt b:= Real.sqrt_pos.2 h; refine ⟨h,inv_pos.mpr he,?_⟩; change (Real.sqrt b)⁻¹^2*b=1;rw [inv_pow,Real.sq_sqrt h.le,inv_mul_cancel₀ h.ne']

/-- Actual period slices enter the computation through the bare weight. -/
lemma headed (q N : ℕ)(p:C.Makes):
    let n := C.S.side N q; let S:=densityCoeff C L a N N; let β:= C.beta N q
    (∀ z : Rays (wire G n), (C.path.rep N q N).eval (input G n z) = Real.exp (-β * fundamental G n z)) ∧
    X^2 * stone S n= - paste (fundamental G n) := by
   intro n S b; refine ⟨fun z=> congr_fun (p.wilson.starts N q).2 (input G n z),?_⟩; unfold S densityCoeff; rw [leaves,←top_word,wax]

-- make g→g propagation and normalization convention clear
abbrev altitudeN (N i:ℕ):= destination C.path.levels N i
abbrev gear (N i:ℕ): Pot G:= waken (altitudeN C N i) (L i) (densityCoeff C L a N (i+1)) (chart G) (Hay.Wday _ i)
lemma rescale (N i:ℕ) (he:i<N): densityCoeff C L a N i= Wine.normalized a (gear C L a N i) := Dove.through _ _ _ _ _ _ _ he
include h
lemma kinetic (N i:ℕ)(he:i<N): let T:= normalizationCoeff C L a N i; let a':= scalar a (gear C L a N i)
                                     T=a' ∧
                                     T*(nextU T)^2=1 ∧ wake T=X*nextU T ∧ X*bookH T=runic T := by
       intro T a'; exact ⟨rfl,post_grid T (First.gains _ _ (chart_ok G) h N i he).1,rfl,forward_green T⟩

lemma formula (N i:ℕ)(he:i<N)(n:Side)
     (k:(primary (altitudeN C N i).patch (Noise C) n).Choices):
     let S := primary (altitudeN C N i).patch (Noise C) n
     let T:=stone (densityCoeff C L a N (i+1)) (n*S.patch.L)
     let P:=flush (Reef.floor (Noise C) (altitudeN C N i) (L i) n) k (chart G) T
     let H:=ferry (altitudeN C N i) (Hay.Wday C.path.levels i) (L i) n
     let R:= beam (variation H.saddle (wire G n)).call (expan (positive H P))
     Solved H P ∧ H.saddle.P.PosDef ∧ vocal H P=R ∧ coeff 0 R=1 ∧ landed (altitudeN C N i) (chart G) (Hay.Wday C.path.levels i) (L i) n k T=
      PowerSeries.C H.main + covelog R ∧
      ∀ Y:Pap (wire G (n*S.patch.L)), let Z:=Reef.seat (Reef.floor (Noise C) (altitudeN C N i) (L i) n) Y; R * (tossed (altitudeN C N i) (chart G) (Hay.Wday C.path.levels i) (L i) n k T Y) = beam (variation H.saddle (wire G n)).call (expan (positive H P)*toInk H Z):= by
   intro S T P H R
   let A:= C.path.levels; let V:=altitudeN C N i; let p:= Noise C
   have hx:=genu A L (Hay.Wday _) (chart G) a (chart_ok G) h (i:=i+1) (N:=N) he
   obtain ⟨s,D,hs,hC,B,W⟩:= colors G p.penalty p.penalty_pos (V.legal)
   have H1 : Solved H P:=consolidate V (chart G) (Hay.Wday A i) (L i) n (chart_ok G) k T (stoned_main hs.le hC.le (B V.wing).1 hx.toVivid hx.ink _) (A.clock.adm i)
   exact ⟨H1,(honey V (Hay.Wday A i) (L i) n).1,rfl, Orb.voice H P H1,rfl,(by intro _ Z; exact Orb.normalization H P H1 Z)⟩

/-- Infinite cover before re-expression: take rooted derivatives of all orders
**mod constants** at the period limit. No growth-of-volume rate here: later
cutoff estimates don't use one. -/
lemma evolved (N i e r:ℕ)(he:i<N)(b:Fin r)
   (k:∀ n:Side,(primary (altitudeN C N i).patch (Noise C) n).Choices) :
   let P:=altitudeN C N i; let V:=densityCoeff C L a N (i+1)
   ∃ η:ℝ,0<η ∧ Kith η (gear C L a N i e r) (fun n:Side=> rancho (landed P (chart G) (Hay.Wday C.path.levels i) (L i) n (k n) (stone V _)) e r) := by
   intro P V; exact componentwise P (L i) V _ _ ((genu C.path.levels L (Hay.Wday _) _ a (chart_ok G) h (i:=i+1) (N:=N) he).toStory) (C.path.levels.clock.adm i) (chart_ok G) k e r b
end YM.FormalBulk08.Primer
