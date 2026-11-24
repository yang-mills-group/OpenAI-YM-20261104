import YM.Qlocal.Quipu.Thunder
import YM.AllOrder.Floe.Voyage
import YM.AllOrder.Floe.Campus
/-!
# Before the block. Input & output *shape* widths for the kernel part of the RG step. These must also be able to consume its `Story` Letter order cap.Steer on R (chosen root of SAME trajectory finances BEFORE L). No shrinking on long ranges. Root.Port capability basis learned during rollout.

Minimum actual slot/p-power calendar rank charge horizon q.Mesh stored as ℕ. For each request available starting around stage ≥ cap; simultaneously can choose narrower afterwards inside step estimate, not assuming greater next! `Width` set per stage after Root (Root before block), usable when BOTH adjacent stages under its pre-adoption Finance. Output reserve 4*w vs admitted input w. Doesn't declare that older input has that reserve. Do not conflate stencil & order costs after L; x never actual β etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Squall
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open AllOrder Floe Step Step.PlanV Iron
open Response Ink Ink.Method Ink.Money
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Pace
open Bloch hiding direct
open PriceCompiler
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(A:ℕ→ Stage)(U:MapPrices)(K:KernelChoices)
variable (R : Roots (G:=G) A U K)
namespace Prior
open Quipu Quipu.Sonnet StateE Rent
variable {A U K} (k N x:ℕ)
-- k: vacuum request ACTUAL scope k+2 (choice in Calendar), *independent* of Thunder.N≥2
noncomputable def base (G:Gauge)(A:ℕ→Stage)(U:MapPrices)(K:KernelChoices)(N x:ℕ) := min (leaseF (A x).width N) ((baseS (G:=G) U K x).width)
lemma base_p : 0 < base G A U K N x:= lt_min (lease_pos (A x).width_pos _) ((baseS (G:=G) U K x).pos)
private lemma choice_aux :∃ b:ℝ,0<b∧ b ≤ base G A U K N x ∧ ∀ i∈Age.scope (k+2), b ≤ leaseF (R.pre k x i) N:= by
 obtain ⟨ζ,h,H⟩:= sharpen (Age.scope (k+2)) (fun i v=> v ≤ leaseF (R.pre k x i) N) (fun i _=>⟨_,lease_pos (R.shape k|>.pos x i) _, fun _ _ h=>h⟩)
 have he : 0 < base G A U K N x:= base_p N x
 exact ⟨_, lt_min h he,min_le_right ζ (base G A U K N x),H _ (lt_min h he) (min_le_left ..)⟩
noncomputable def core (k N x:ℕ): ℝ := (choice_aux R k N x).choose
lemma core_p :0 < core R k N x:= (choice_aux R k N x).choose_spec.1
lemma schooling : core R k N x ≤ base G A U K N x :=(choice_aux R k N x).choose_spec.2.1
lemma ages : ∀ i∈ Age.scope (k+2), core R k N x ≤ leaseF (R.pre k x i) N:=(choice_aux R k N x).choose_spec.2.2
noncomputable abbrev stipend (k N x:ℕ):= chant (core R k N x) N (3*N)
noncomputable abbrev sun (k N x:ℕ):= stipend R k N x/(40*(N+1:ℝ))
noncomputable def yard (k N x:ℕ):= min (sun R k N x) (sun R k N (x+1))
lemma sun_p:0<sun R k N x:= div_pos (soprano _ (core_p ..) _) (by positivity)
lemma yard_p :0<yard R k N x:= lt_min (sun_p ..) (sun_p ..)
theorem earns (y:ℕ)(he:StepStages x y):4*yard R k N y*(5*N:ℝ)≤ chant (core R k N x) N (3*N)/2:= by
 have h₀ : yard R k N y ≤ sun R k N x:= by
    have hx:x=y∨ x=y+1:= by unfold StepStages at he; omega
    rcases hx with h|h; exact h.symm ▸ min_le_left _ _; exact h.symm ▸ min_le_right _ _
 have ht : 4*sun R k N x*(5*(N+1):ℝ) = stipend R k N x / 2:= by unfold sun; field_simp; ring
 change _≤ stipend R k N x/2; rw [← ht]; gcongr; · exact mul_nonneg (by norm_num) (sun_p ..).le
 linarith

open Ker Ker.Start
noncomputable abbrev probe (k N x:ℕ)(L:ℝ):= (L *(yard R k N x)/(2*(N+1:ℝ)))/(2*(N+1:ℝ))/8
lemma funded (P:Patch): probe R k N x P.L.val= Tern.γ N (yard R k N x) P:= by unfold probe Tern.γ Tern.chip weaker small_a; push_cast; ring
local notation "ℛ"=> yard R k N x
local notation "γ₀"=> Tern.γ N (yard R k N x)
abbrev Awning (x:ℕ)(L:ℝ):=∀ k≤x,∀ N≤x, core R k N x ≤ probe R k N x L
lemma far : ∀ᶠ L in atTop, Awning R x L:= by
 have h₁(k N:ℕ):∀ᶠ L in atTop, core R k N x ≤ probe R k N x L:= by
    let p:=probe R k N x; have hp : 0 < p 1:= by unfold p probe; have ht := yard_p R k N x; positivity
    have hx: (p)=fun i=>i*p 1:= by ext i; unfold p probe; ring
    change ∀ᶠ i in atTop, _≤p i; rw [hx]; exact (tendsto_id.atTop_mul_const hp).eventually_ge_atTop _
 filter_upwards [(eventually_all_finset (I:= (range (x+1))×ˢ (range (x+1))) (p:=fun i L=>core R i.1 i.2 x≤ probe R i.1 i.2 x L)).mpr (fun i _ => h₁ i.1 i.2)] with i hi
 exact fun k hk N h=> hi (k,N) (mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩)
lemma obtain_world : ∃ f:ℕ→ℕ, ∀ x (L:Side), f x ≤ L.val→ Awning R x L.val:= by choose u hu using fun i=> eventually_atTop.mp (far R i); choose r hr using fun i=> exists_nat_gt (u i); exact ⟨r,fun x L hl=> hu _ _ ((hr x).le.trans (Nat.cast_le.mpr hl))⟩
lemma feeds {L:Patch}(h:Awning R x (L.L.val:ℝ))(hk:k≤x)(hN:N≤x):core R k N x ≤ Tern.γ N (yard R k N x) L:= funded R k N x L ▸ h k hk N hN -- ▸ rewrites? yes.
end Prior
end YM.Qlocal.Squall
