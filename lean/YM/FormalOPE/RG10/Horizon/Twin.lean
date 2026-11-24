import YM.FormalOPE.RG10.Horizon.Procure

/-!
# Stepping toward farther pair extraction

Concrete two-clock sufficiency criterion. This is *on the formal coefficient calculation*,
never invoking hypothetical convergence of an exact-theory detector. Needs all connections in
the supporting modules and project `Ledger.Paid`. Charge orientations, phase independent θ etc
as in the frame. Affirms not that every input word meets the criteria (in particular before
period and image estimates or when inputs/requests are joint nonlinear profiles) but that all
probes in the lists that do can be compared at polynomial cost, with neither orthogonality of the
higher-horizon matrix nor a commuting-limits premise. Need `R_train` and h, tone spacing in its
admissible controller class; the min kernel of any pair of Vantages may force a larger cutoff
& frame than other probes from nominal length 1. $\exp(t)=T$ arbitrarily large with no
pre-announcement of a common finite period adequate *forever*. For instance here require native
spacing at most $1/T^2$ to make explicit that impending geometry still requires its own final
estimates `Proof.border` etc, not a `Patience` use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{m r h d:ℕ}

def cash (t : ℝ)(M:ℝ) (δ : ℕ)(α:ℝ) := legUp t M δ * tilt t α

/-- Rigorous *criterion*, comparing just neighboring-log-length clocks. No statement that this
holds on arbitrary shapes! In particular use where RG08/09's common regulators & generators
produce same-oriented candidates, comparisons for all specified epochs, and detailed capture
aperture prerequisites. For the canonical `b` at that demand, never fit puffs or filmF to the
needed observation; both chosen from one such UV run **before** selecting exterior evaluations
on that run. Do not interpret as getting growth estimates at common cutoff or actual field history
back. `S` is a **finite list** fixed before the test clocks, may include extra query probes.
Each `X : Vantage` has already fixed heights, field fps weights, locus (including help with
actual gauge, denominator, rooted center and address-ball hypotheses). θ-free branch test rules.
For integration choose List coverage rather than assuming `univ`. Per-period comparisons for
all of these are precise hypotheses, requiring new estimates for moving geometry including when
far fields are mixed linearly from two different resolution conventions.
-/
def Attaches (R:Rails F) (Z:Patience P Y)(x:Fin m→Seats F d)(E: Fore m) (r h:ℕ)(S: Finset (Vantage F)) : Prop :=
 ∃ (K:ℝ) (δ:ℕ) (α:ℝ), 1 ≤ K ∧ 0<α ∧ ∀ᶠ s:ℝ in atTop, ∀ t∈Set.Icc s (s+1),
 ∃ L:Ledger F h, L.tape.μ L.N ≤ Real.exp (-2*t) ∧
   ∀ v∈ ({s,t} : Finset ℝ), ∀ i∈S, ∃ O: Ledger.Orbits L r,
                Paid L R Z x E i v O (legUp v K δ) (cash v K δ (h+α))
lemma cash_nn {C:ℝ} (hc:0 ≤ C)(α t:ℝ)(δ:ℕ) : 0≤ cash t C δ α := mul_nonneg (leg_nn _ _ _ hc) (Real.exp_nonneg _)
private lemma debit {C v M N : ℝ} (α:ℝ)(d:ℕ)(hc:1 ≤ C)(hm : M=legUp v C d)(hn : N=cash v C d α) : N+(N+N+M*(N+M*N)) ≤ cash v (5*C^3) (3*d) α := by
 have hM:1 ≤ M:= hm.symm ▸ big_leg _ _ _ hc; have hh:N=M*tilt v α:=by rw [hm,hn,cash]
 have hx:0 ≤ N:=hn.symm ▸ cash_nn (by linarith) ..
 have he: M*N ≤ M*(M*N):= mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hx hM) (by linarith)
 calc
   _ = 3*N+M*N+M*(M*N):= by ring
   _ ≤ 5*(M*(M*N)):= by nlinarith only [he, le_mul_of_one_le_left hx hM,le_mul_of_one_le_right hx hM]
   _ = _:= by rw [hh,hm,cash,legUp,legUp,Nat.mul_comm 3 d,pow_mul]; ring

variable {x:Fin m→Seats F d}{E:Fore m}{S:Finset (Vantage F)}
lemma twins (H:Attaches R Z x E r h S) : ∃ (C:ℝ)(δ:ℕ)(α:ℝ),1≤C ∧ 0<α ∧ ∀ᶠ s:ℝ in atTop, ∀ t∈Set.Icc s (s+1),
    ∃ L:Ledger F h, ∀ v∈({s,t}:Finset ℝ),∀ i∈S, coin r (burst R Z i v E x-imply R Z i v h L.article) ≤ cash v C δ (h+α) := by
 obtain ⟨K,A,α,hK,hA,HA⟩:= H; have h3:1 ≤ K^3:= one_le_pow₀ hK
 refine ⟨5*K^3,3*A,α,by linarith,hA,?_⟩
 filter_upwards [HA] with s h0 t ht; obtain ⟨L,-,he⟩:=h0 t ht
 refine ⟨L,fun i hi x hx=> ?_⟩; obtain ⟨u, H⟩:= he i hi x hx
 exact (H.interpreting (leg_nn _ _ _ (by linarith)) (cash_nn (by linarith) ..)).trans (debit _ A hK rfl rfl)
end YM.FormalOPE.RG10.Clearing
