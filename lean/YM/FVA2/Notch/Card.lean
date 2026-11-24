import YM.FVA2.Notch.Quiz
/-!
# Placement estimate on `Front` cutoffs with fixed arbitrary clearance

In `XSpace.Cirrus.Sample`, can keep the same placements in the analysis, beyond the cube of
centers used in the final diagnostic. See `Entry` in `Cover.lean`; `frame` here allows all
large enough `Front` cutoffs and placements meeting that protocol. For all points varying
in any fixed compact of **separated** configurations. For n=0 there is not even the extra
clearance requirement (provide an internal choice). `mildG` still the exponent on the power
of spacing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Notch.Pitch
open Function Filter Set Finset Metric MeasureTheory Real Lattice MS MS.High
open MS.Book MS.Book.Convolve MS.Tone MS.Tide MS.Rake MS.Land MS.Dial MS.Orbit MS.City MS.Latch MS.Latch.Job MS.Fleet MS.Vista MS.Vane MS.Book.Program MS.Puff MS.Puff.Mom MS.Book
open Wilson Further XSpace.Cirrus Arrival Arrival.Landing Arrival.Schedule Removal Press Speed XSpace.Expense
open scoped Topology ContDiff BigOperators Classical
variable {n:ℕ}{G:Gauge}{K:Set (Points n)}{r:ℝ}
local notation "U"=> Fin n
local notation "Z"=> XSpace.Cirrus.Sample n
local notation "T"=> XSpace.Cirrus.grab (n:=n)
local notation "I"=> Flight r K
-- reduce by `comap` using Flight subtype, no need NeBot here.
def go (r:ℝ) (K:Set (Points n)): Filter (Flight r K):= comap ( grab ∘ Flight.sample ) Front
def frame (r:ℝ)(K:Set (Points n)): Filter ( Sample n ):= comap grab Front ⊓ 𝓟 {i|Entry r i ∧ familiar i∈K }
local notation "L"=> go r K
local notation "M"=> frame r K
private lemma grown {A:Sample n→Prop}: (∀ᶠ i in M,A i) ↔ (∀ᶠ m in Front,∀ i:Sample n,grab i=m→Entry r i→familiar i∈K→ A i):= by unfold frame; rw [ eventually_inf_principal,eventually_comap ]; simp only [Set.mem_setOf_eq,and_imp]
lemma room (r:ℝ)(K:Set (Points n)): ∀ᶠ i in frame r K,Entry r i ∧ familiar i∈K:= grown.mpr ( Eventually.of_forall fun _ _ _ h g=> ⟨h,g⟩ )
lemma timely (r:ℝ)(K:Set (Points n)): Tendsto grab (frame r K) Front:= tendsto_iff_comap.mpr inf_le_left
lemma paves (r:ℝ)(K:Set (Points n)): Stretched (go r K) (grab ∘ Flight.sample) := frontier.wider tendsto_comap
lemma stretches (r:ℝ)(K:Set (Points n)): Stretched (frame r K) grab:= frontier.wider ( timely .. )
variable (p:Sample n→Prop)
lemma purchase (h: ∀ᶠ i in go r K,p i.sample): ∀ᶠ i in frame r K, p i:= by
 rw [go,eventually_comap] at h; rw [grown]; filter_upwards [h,frontier.smaller,( frontier.horizon ).eventually (eventually_ge_atTop 16)] with m hm hi hq i hx hr hk; subst m; let j:Flight r K:= ⟨ i,hr,hk,hi, by exact_mod_cast (show 16≤( i.F.p.side.val:ℝ) from hq) ⟩; exact hm j rfl
section cost
variable (Y:XSpace.Initialize G)(u:Fin n→Label (Press.portDeck G))(A:Land.Prescription (Press.portDeck G))(μ:ℝ)
variable {O:Booked (Press.portDeck G)}(S:MS_Data G O)(s:Finset (Fin n))(k:ℕ)
local notation "P"=> Flight.trail r K μ
local notation "E"=> entries μ Y u A s k
local notation "D"=> Landing.moondye μ S u s k
lemma pending : Tendsto (Flight.trail r K μ).profile.θ (go r K) atTop:= by
 let a(i:Flight r K):= i.sample.F.spacing; have he : Tendsto (fun i:Flight r K=> Real.log (a i)) L atBot:= Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨(paves r K).endpt, Eventually.of_forall fun i:Flight r K=>i.sample.F.positive⟩); exact (tendsto_neg_atBot_atTop.comp he).congr (fun i=> (theta_value (i.signs.2.2.1)).symm )
lemma grows : Super (go r K) ( Flight.trail r K μ ).side ( Flight.trail r K μ ).profile.θ:= by
 intro a; let p := Flight.trail r K μ; let k:=⌈a⌉₊; filter_upwards [(( paves r K ).pay k ).eventually_ge_atTop 1] with i hi; let m:=i.sample.F; let u:=m.spacing; let z:=p.profile.θ i; let b:= tickA p.side i; obtain h:u= exp (-z):= (bornS i.signs.2.2.1).symm
 have ht : 1≤ u^k * b:= by unfold b p; unfold tickA dimT; change _ ≤ u^k*((periodN (psi m)).val:ℕ); rw [psi_back m]; exact hi
 change a*z ≤ log b; apply le_trans (mul_le_mul_of_nonneg_right ( Nat.le_ceil a ) (p.profile.room i)); rw [← Real.exp_le_exp,Real.exp_log (δ_p ..)]; rw [h,Real.exp_neg,inv_pow, ← Real.exp_nat_mul] at ht; obtain H: exp ((k:ℝ)*z)*1 ≤ b := (le_inv_mul_iff₀ (by positivity)).mp ht; rw [mul_one] at H; exact H
variable (g:G.Simple)(hS:TaylorOKF S ( wickInput Y ) A) (hc:IsCompact K)(ht:K⊆ conf n)(hr:0<r)
include hS g hc hr ht
lemma one : Fast (frame r K) grab E ( D ∘ familiar ):= by
 have he: PeakT L (P).profile mildG (fun i:Flight r K=> E i.sample-D (familiar i.sample)):= Total.link (l:=L) (by
    obtain ⟨C,hC,m,H⟩:= Flight.mapCost Y u A μ s k S g hS hc ht hr; exact ⟨ C,hC,m, Eventually.filter_mono (tendsto_iff_comap.mp ( pending μ )) H ⟩ ) ( grows μ )
 obtain ⟨C,hC,H⟩:= he; refine Fast.put C ( purchase _ ( H.mono fun i hi=> hi.trans_eq ?_ )); unfold Tide.lake; rw [show exp (-mildG * (P).profile.θ i)= i.sample.F.spacing ^ mildG from ?_];  rw [ show (P).profile.θ i= -Real.log _ from theta_value i.signs.2.2.1, Real.rpow_def_of_pos i.sample.F.positive ]; congr 1; ring -- congr
omit g hS hc hr ht
section instances
variable {X:Sample n→ℂ}{V:Points n→ℂ}
-- Unpacking the eventual bound with these placements
lemma specialize : Fast (frame r K) grab X ( V ∘ familiar ) ↔ ∃ C:ℝ, 0<C∧∀ᶠ m in Front,∀ i:Sample n,grab i=m→Entry r i→ familiar i∈K→ ‖X i-V (familiar i)‖≤ C* Speed.chip i.F:= by
 constructor; · intro h; obtain ⟨C,hC,H⟩:= Fast.bounds ( l:=M ) (τ:=grab) h; exact ⟨ C,hC,grown.mp H ⟩
 rintro ⟨C,hC,H⟩; exact Fast.put C ( grown.mpr H )
end instances
end cost
end YM.FVA2.Notch.Pitch
