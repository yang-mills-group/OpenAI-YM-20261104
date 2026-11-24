import YM.QuadraticLocal.Poetry.Volume
import YM.AllOrder.Floe.Lamps
/-!
# Permanent widths: even repeated many annotated kernel steps at the same fixed order
Choose `before-L` lower envelopes for any announced finite effort (κ+2≤stage). Heat and Curvature
width can be upper-wage shrunk post-L, but might only survive O(1) steps without this maneuver.
Rank and owner Tag heights retained.D.Memory. A post fact.Time.ScReaders. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Agenda
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Sunrise.Aviary Stationary Picket
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι M: Type} [Fintype M][DecidableEq M] {G:Gauge} (H:Finset M)(I:M→ Loan){a b:ℝ}{k d N l:ℕ}
-- use generous pre-L losses; marker owner L,Γ rank.m.Not multiplying per-root Affine.Moment production.
abbrev burden (J:ℕ):ℕ:= (8*J+1)*((J+1)*2)
def bank (L:ℕ)(a:ℝ)(N:ℕ):ℝ:= a/((burden L:ℝ)^N)
lemma yields (k N:ℕ)(hp:0<a):0<bank k a N:=by unfold bank burden; positivity
lemma entry_paid (ha:0<a) {K:ℕ} {d:ℕ}(he:guard I H k≤K)(hd:d≤k): a/(burden K:ℝ)≤ pay d a I H k:= by
 let z:ℕ:= 8*guard I H k+1; let v:ℕ:=guard I H d; let R:ℕ:= 8*K+1; unfold Agenda.pay Poetry.entry Agenda.descent; rw [div_div, div_div]; change a/(burden K:ℝ)≤ a/((z:ℝ)*((v+1:ℕ)*2)); gcongr _ / ?_;
 have ht:v≤K:= by apply Nat.le_trans ?_ he; unfold v Agenda.guard plusK; omega
 have h₂:z≤8*K+1:= by unfold z; omega
 change (z:ℝ)*(((v+1:ℕ):ℝ)*2) ≤ ↑((8*K+1)*((K+1)*2):ℕ); norm_cast; gcongr
lemma infusion (hp:0<a)(ht: plusK I H k≤ N): bank (N+2) a (N+1)≤ path a I H k (k+1):=by
 have he : k≤N:=by unfold plusK at ht; omega
 let V:= burden (N+2); let L:= path a I H k; have hx(d:ℕ)(hd:d≤k+1): bank (N+2) a d≤L d:=by
    induction d with
    | zero=> change bank _ a 0≤a; rw [bank,pow_zero,div_one]
    | succ d ih=> refine le_trans ?_ (entry_paid H I (solid H I k hp d) (Nat.add_le_add_right ht _) (by omega)); rw [bank,pow_succ, ← div_div]; gcongr ?_ / _; exact ih (by omega)
 apply le_trans ?_ (hx (k+1) le_rfl); unfold bank; refine div_le_div_of_nonneg_left hp.le (pow_pos (by unfold burden; positivity) _) (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ burden (N+2) from Nat.one_le_iff_ne_zero.mpr (by unfold burden; exact (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by decide))).ne'))) (Nat.succ_le_succ he))
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV PriceCompiler
open PhysicalNext ThroughLaunch -- names in Lamp check
variable {U:MapPrices}{F:ℕ→Stage}{K:KernelChoices}(R:Roots (G:=G) F U K) (ψ:ℕ→ℕ) -- postgeometry reserve independent of L and Number requests
variable (x y:ℕ) (n:Side)
local notation "Φ"=> arms F U K G
local notation "A₀" k:max x:max=> (R.pre k x)
lemma receives (R:Roots (G:=G) F U K)(k x:ℕ) : ∃ b:ℝ,0 < b ∧ b ≤ arms F U K G k x ∧ ∀ i∈Step.tape (k+2), b≤ leaseF ((R.pre k x) i) (k+2):= by
 obtain ⟨z,hz,H⟩:= sharpen (Step.tape (k+2)) (fun i z=> z ≤ leaseF ((R.pre k x) i) (k+2)) (fun i _=>⟨_,lease_pos ((R.shape k).pos x i) _,fun _ _ h=> h⟩); exact ⟨min (Φ k x) z,lt_min (arms_p ..) hz,min_le_left .., H _ (lt_min (arms_p ..) hz) (min_le_right ..)⟩
def stipend (k x:ℕ) : ℝ:= (receives R k x).choose
def poll (k x:ℕ): ℝ:= chant (stipend R k x) (k+2) (3*(k+2))
def waist (k x:ℕ):ℝ:= bank (k+4) (poll R k x) (k+2+1)
def seed (k x:ℕ):ℝ:= min (waist R k x) (waist R k (x+1)) / (ψ k+1:ℕ)
lemma belt_p (k x:ℕ): 0<waist R k x:= yields _ _ (soprano _ (receives R k x).choose_spec.1 _)
lemma stem (k x:ℕ): 0<seed R ψ k x:= div_pos (lt_min (belt_p ..) (belt_p ..)) (by positivity)
structure Taut (x k:ℕ)(L:ℝ) : Prop where
    le : (stipend R k x) *(4*(k+2+1):ℕ) ≤ seed R ψ k x/4 * L
def Crews (R:Roots (G:=G) F U K)(ψ:ℕ→ℕ)(x:ℕ)(L:ℝ): Prop:= ∀ k,k+2≤x→ Taut R ψ x k L
lemma stretch (k:ℕ): ∀ᶠ L:ℝ in atTop,Taut R ψ x k L:= by filter_upwards [(tendsto_id.const_mul_atTop (show 0< _ from div_pos (stem R ψ k x) (show (0:ℝ) < 4 by norm_num))).eventually_ge_atTop ((stipend R k x)*(4*(k+2+1):ℕ))] with i hi; exact ⟨hi⟩
lemma widen : ∃ κ:ℕ→ℕ, ∀ x n, κ x≤ n → Crews R ψ x (n:ℝ):= by
 have he (x:ℕ) : ∀ᶠ l:ℕ in atTop, Crews R ψ x l:= by filter_upwards [((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually ((Filter.eventually_all_finset (I:= range (x+1)) (p:=fun k L=> Taut R ψ x k L)).mpr (fun k _=> stretch R ψ x k)))] with l hl; exact fun k hk=> hl k (Finset.mem_range.mpr (by omega)); -- `R` param .Notation
 choose q hq using fun x=> Filter.eventually_atTop.mp (he x); exact ⟨q,hq⟩
-- right-use even in neighbors y
lemma rightWing (k:ℕ)(h:PriceCompiler.StepStages x y): seed R ψ k y * (ψ k+1:ℕ) ≤ waist R k x:= by unfold seed; rw [div_mul_cancel₀ _ (by positivity)]; unfold StepStages at h; rcases (show x=y ∨ x=y+1 from (by omega)) with h|h; subst x; exact min_le_left ..; subst x; exact min_le_right ..
end YM.QuadraticLocal.Poetry.Agenda
