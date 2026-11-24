import YM.FVA2.Continuum.Turnstile
/-!
# Concretely forge the checked Press-input asymptotic comparison on the admissible Dial regulators

Simultaneous spacing and volume. One `Continuation` across all Profiles; demonstrates application
using the initial MS remove endpoints already. `Dial.Movie` with placement by floor & expanding
inversion regulator. For common *block* cutoffs see separate
proofs in `Arrival/Schedule` etc. The `n` in `Movie ... n` is taken sufficiently large
for separation. Empty probes included. Scaling factor in `fare`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Continuum
open Function Set Filter Finset Metric MeasureTheory Real Lattice
open YM.MS MS.High MS.Orbit MS.Vista MS.Tide MS.Fleet MS.Wind MS.Rake MS.Tone MS.Swirl MS.Swirl.Near
open Vane Geo MS.Menus MS.Local.Physical MS.Book MS.Book.Convolve Program MS.Land
open Dial
open scoped Topology BigOperators
variable {G:Gauge}
namespace Continuation
variable {W:Type}[LinearOrder W][Fintype W]
variable (u: W→ MS.Rake.Label (Press.portDeck G))
theorem uses_movie (p:W→ Tone.QP) (h:Injective p) (μ:ℝ):∃ n, Uses (Movie μ p n) atTop μ:= by
    obtain ⟨n,hv⟩:= eventually_atTop.mp ((filmed p μ (n:=0)).eventually (earlyW h)); let F:=Movie μ p n; have hh(v:ℕ): Dial.Clamp p ( testP F v ) := hv (v+n) (by omega); let P:=F.profile; have he:Tendsto (fun i:ℕ=>i+n) atTop atTop:= StrictMono.tendsto_atTop fun i j h=> Nat.add_lt_add_right h n
    refine ⟨n, ?_,?_,fun _=>rfl,tendsto_natCast_atTop_atTop.comp he, fun c=> he.eventually ( SuperA μ c ),fun i=> Fleet.Cleared (i+n |> Ball), centered_size _ _ fun i=> Fleet.centerD (Ball (i+n)) ⟩
    · intro w; refine ⟨ 1+‖p w‖,by positivity,fun i=>?_⟩; let z:=exp (P.θ i); let y:=assign (i+n) ( p w ); change ‖Tone.embed y‖ ≤ _; have ht := Screen_price (i+n) ( p w ); apply le_trans ( b:=1+ z*‖p w‖ ) _ _; · obtain hg:= norm_add_le ( Tone.embed y-z • p w ) ( z • p w ); rw [sub_add_cancel] at hg; apply hg.trans; rw [ norm_smul_of_nonneg ( by unfold z; positivity ) ]; gcongr
      have H : 1≤ z:= Real.one_le_exp ( P.room _ ); change _ ≤ (1+_)*z; linarith
    apply unpose ( v:=μ ) F.off; intro i j hi; refine ⟨ ⟨ 2*‖p i-p j‖,mul_pos (by norm_num) ( norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hi))),fun k=>?_⟩,⟨‖p i-p j‖/2, div_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( h.ne hi ) )) (by norm_num ),fun k=>?_⟩⟩ <;> simp only [roots,Pi.zero_apply,exp_zero,mul_one]; exact ( hh k i j hi|>.2 ).le; exact ( hh k i j hi |>.1 ).le

variable (p:W→Tone.QP)(hp: Injective p)(μ:ℝ)(s: Continuation G) (h:G.Simple)
variable (dial : Bool)
def start : ℕ:= (uses_movie p hp μ).choose
lemma used : Uses (Movie μ p (start p hp μ)) atTop μ:= (uses_movie p hp μ).choose_spec
def proofStart (H : G.Simple) (s:Continuation G)(dial:Bool) : MS.Land.Prescription (Press.portDeck G) :=
    if dial then (from_dial s.toInitialize s.data H).choose else (from_tide s.toInitialize s.data H).choose
local notation "A" => proofStart h s dial
local notation "S" => (start p hp μ)
local notation "T" => Movie μ p S
local notation "P" => s.data
lemma plan : TruePlan s.data s.toInitialize (proofStart h s dial):= by unfold proofStart; split; exact (from_dial s.toInitialize s.data h).choose_spec; exact (from_tide s.toInitialize s.data h).choose_spec
local notation "Ψ" => rawFull s.toInitialize u T μ A
local notation "ϕ" => MS.Rake.Label.h ∘ u
def unconnected : Terrify W ℕ:= fare (MS.Rake.Label.h∘ u) (Movie μ p (start p hp μ)).profile (rawFull s.toInitialize u (Movie μ p (start p hp μ)) μ (proofStart h s dial))
variable (k:Finset W)(n:ℕ)
lemma pole_size (i:ℕ) : ( MS.Orbit.dimT (T).side i ).val = 4*( Nat.ceil (exp (((i+start p hp μ :ℕ ):ℝ)^2))+1):= Fleet.fullC _
lemma quote : PeakT.twin atTop (T).profile mildG (fare (ϕ) (T).profile (Ψ) k n) (fun i=> tour s.data u μ (testP (T) i) k n):= by
 obtain ⟨V,hV,_⟩ := (plan s h dial).poses W ℕ T atTop μ u (used p hp μ); rw [←hV.whole]; exact hV.bouquet k n
lemma value : Tendsto (unconnected u p hp μ s h dial k n) atTop (𝓝 (tour s.data u μ p k n)) := Dial.agrees T (Continuum.Continuation.quote u p hp μ s h dial k n) ((used p hp μ).upright) (( Dial.contin s.data u p hp k n μ ).1.tendsto.comp ( Dial.filmed .. ))
end Continuation
end YM.FVA2.Continuum
