import YM.Integration.WilsonCenteredFailedHalo
import YM.Integration.WilsonCenteredCrossedGas
import YM.Extra.SOURCE_HISTORIES.Unit

/-! Install the signed regular source and its complete compulsory gallery
on the same Wilson rep. The native completion uses the actual center
and its measured section; no independent exterior is substituted. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredMountedCapture
open Finset Function RG Lattice Wilson Source Labels Push.Local Planned.GuardedAtom Extra.Histories
open WilsonCenteredCaptureSlots WilsonCenteredFailedHalo
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} {d : ℕ} {F : Labels.Frame G d}
    {P : Rep G n} (y : Site n) (T : ι → Support n) (book : ι ↪ ℕ)
    (K : Guard.Keeper P.p P.activities) (serial : ι × Finset ℕ ↪ ℕ)

def halls (j : ℕ) := Function.extend book T (fun _=>{y}) j

def raw (seed : F.Coeff) (f h : ι → Config G n → ℂ) (hard : ℕ → Config G n → ℂ) : Raw F n :=
  ⟨seed,Function.extend book f 0,hard+entered P K T Quiet serial h⟩

variable (seed : F.Coeff) (f h : ι → Config G n → ℂ) (hard : ℕ → Config G n → ℂ)

theorem formed (roots : ∀ i,y∈T i) (goods : ∀ i,P.p.Regular (T i) (f i))
    (att : ∀ i, Attaches P.p.threshold (T i) (h i)) (bank : ForceFormat P.p P.activities y hard)
    (law : P.activities.ForcedFamily P.p) :
    (raw T book K serial seed f h hard).Format y (halls y T book) P := by
  have posted (i : ι) : halls y T book (book i) = T i := book.injective.extend_apply ..
  have idle (j : ℕ) (abs : ¬∃ i, book i=j) : halls y T book j={y} := Function.extend_apply' _ _ _ abs
  refine ⟨?_,?_,bank.add (WilsonCenteredCaptureSlots.formed P K T Quiet serial h y law roots att)⟩
  · intro j;by_cases used : ∃ i,book i=j
    · obtain ⟨i,rfl⟩:=used;rw [posted];exact roots _
    rw [idle _ used];exact mem_singleton_self _
  intro j
  by_cases used : ∃ i,book i=j
  · obtain ⟨i,rfl⟩:=used
    change P.p.Regular (halls y T book (book i)) (Function.extend book f 0 (book i))
    rw [posted,book.injective.extend_apply]
    exact goods _
  change P.p.Regular _ (Function.extend book f 0 j)
  rw [Function.extend_apply' _ _ _ used]
  exact (regular0 P.p _ y).1

theorem deck (e : ι→ℝ) {a b v κ : ℝ} (cash : SumBudget (fun i=>reservedMass P.p (T i) (e i)) a)
    (caps : ∀ i,P.p.supBounds y (T i) (f i) (e i)) (left : 0≤v) (room : hitWidth P.p*v≤1)
    (quiet : P.activities.KBound P.p v) (cap : ∀ i U,‖h i U‖≤e i)
    (force : ForceCost P.p P.activities hard (κ*b)) (div : 0<κ) :
    Deck (raw T book K serial seed f h hard) y (halls y T book) P κ a (b+(hitWidth P.p*v/κ)*a) := by
  let z := Function.extend book e 0
  have atKey i : z (book i)=e i := book.injective.extend_apply ..
  have atHall i : halls y T book (book i)=T i := book.injective.extend_apply ..
  have blank j (out : ¬∃ i,book i=j) : z j=0 := Function.extend_apply' _ _ _ out
  constructor
  · refine ⟨z,?_,sumBudget_pass book _ ?_ ?_⟩
    · intro j
      by_cases used : ∃ i,book i=j
      · obtain ⟨i,rfl⟩:=used
        change P.p.supBounds y (halls y T book (book i)) (Function.extend book f 0 (book i)) (z (book i))
        rw [atHall,book.injective.extend_apply,atKey];exact caps _
      change P.p.supBounds y _ (Function.extend book f 0 j) (z j)
      rw [blank _ used,Function.extend_apply' _ _ _ used]
      exact (regular0 P.p _ y).2
    · simpa only [atHall,atKey] using cash
    · intro j outside
      rw [blank _ outside];exact mul_zero _
  have debt := WilsonCenteredFailedHalo.cost T K serial h e quiet left room (fun i=>(caps i).1) cash cap
  have billed := force.add debt
  have budget : κ*(b+(hitWidth P.p*v/κ)*a)=κ*b+hitWidth P.p*v*a := by
    field_simp [ne_of_gt div]
  rw [budget]
  exact billed

theorem value (S : SectionData F) (U : Config G n)
    (att : ∀ i,Attaches P.p.threshold (T i) (h i)) {a b v : ℝ}
    (quiet : P.activities.KBound P.p v) (hb : ForceCost P.p P.activities hard a)
    (companion : ForceCost P.p P.activities (entered P K T Quiet serial h) b)
    (hm : Summable fun i=>masked P.p.threshold (T i) (f i) U) (he : Summable fun i=>h i U) :
    (raw T book K serial seed f h hard).eval y (halls y T book) S P U =
      (P.eval U:ℂ) * (Push.Local.primary S y P.p.threshold seed U +
        ∑' i, (masked P.p.threshold (T i) (f i) U+h i U)) +
      (Real.exp (P.exponent U):ℂ) * ∑' C,gasMark P.p P.activities U C hard := by
  let rawer := raw T book K serial seed f h hard
  let stamped j:=masked P.p.threshold (halls y T book j) (rawer.bulk j) U
  have spare j (no : ¬∃ i,book i=j) : stamped j=0 := by
    change masked P.p.threshold _ (Function.extend book f 0 j) U=0
    rw [Function.extend_apply' _ _ _ no]
    simp [masked]
  have source (i : ι) : stamped (book i) = masked P.p.threshold (T i) (f i) U := by
    change masked P.p.threshold (Function.extend book T (fun _=>{y}) (book i)) (Function.extend book f 0 (book i)) U=_
    rw [book.injective.extend_apply,book.injective.extend_apply]
  have same : (∑' j,stamped j) = ∑' i,masked P.p.threshold (T i) (f i) U := by
    rw [←book.injective.tsum_eq (f:=stamped) (fun j hj=>by by_contra no; exact hj (spare j no))]
    exact tsum_congr source
  have gs := (dominated_gasMark hb quiet).summable U
  have hs := (dominated_gasMark companion quiet).summable U
  have whole := WilsonCenteredFailedHalo.actual T K serial h att companion quiet U
  change (P.eval U:ℂ)* (_+∑' j,stamped j)+(Real.exp (P.exponent U):ℂ)*
    (∑' C,gasMark P.p P.activities U C (hard+entered P K T Quiet serial h))=_
  simp_rw [map_add]
  rw [same,gs.tsum_add hs,whole,hm.tsum_add he]
  simp only [Rep.eval,Complex.ofReal_mul,raw]
  ring

/-- Mint the actual coefficient once. The same credential carries its signed
density, its two native purses and every comparison with the independent
coordinate declared at the capture date. -/
theorem original (S : SectionData F) (Y : Hol G) {σ C Λ δ v a b κ w : ℝ}
    (law : P.Lawful σ C Λ δ v) (read : Readable Y S P.p n w)
    (div : 0<κ) (left : 0≤v) (room : hitWidth P.p*v≤1)
    (roots : ∀ i,y∈T i) (goods : ∀ i,P.p.Regular (T i) (f i))
    (e : ι→ℝ) (cash : SumBudget (fun i=>reservedMass P.p (T i) (e i)) a)
    (caps : ∀ i,P.p.supBounds y (T i) (f i) (e i))
    (att : ∀ i,Attaches P.p.threshold (T i) (h i)) (cap : ∀ i U,‖h i U‖≤e i)
    (bank : ForceFormat P.p P.activities y hard) (force : ForceCost P.p P.activities hard (κ*b))
    (hm : ∀ U,Summable fun i=>masked P.p.threshold (T i) (f i) U)
    (he : ∀ U,Summable fun i=>h i U) :
    let D := factor Y S P.p.supportExponent w
    let M := raw T book K serial seed f h hard
    ∃ Q : Coefficient F n, Q.Format y Y P ∧
      Tab Q y P κ (D*a) ((b+(hitWidth P.p*v/κ)*a)+(hitWidth P.p*v/κ)*(D*a)) ∧
      (∀ U, Q.density y S P U =
        (P.eval U:ℂ) * (Push.Local.primary S y P.p.threshold seed U+
          ∑' i,(masked P.p.threshold (T i) (f i) U+h i U))+
          (Real.exp (P.exponent U):ℂ)*∑' C,gasMark P.p P.activities U C hard) ∧
      ∀ (u : F.Coeff) (r : ℝ) (g : ℕ→Directions G n→ℂ), 0≤r →
        Models Y y (halls y T book) P.p M u r g → F.coeffSize (Q.x-u) ≤ errorPrice Y F*r := by
  intro D M
  let rooms := K.supply (fun i=>joint S y (halls y T book i))
  have prepared := formed y T book K serial seed f h hard roots goods att bank law.labels.forced
  have entry := deck y T book K serial seed f h hard e cash caps left room law.labels.boundK cap force div
  have fares := entry.tare div left room read prepared
  refine ⟨Guard.mint rooms M Y,Guard.usage rooms prepared law read,
    Guard.tab_mint rooms prepared law div read fares,?_,?_⟩
  · intro U
    rw [Guard.value_mint rooms prepared law div read fares]
    exact value y T book K serial seed f h hard S U att law.labels.boundK force
      (WilsonCenteredFailedHalo.cost T K serial h e law.labels.boundK left room (fun i=>(caps i).1) cash cap) (hm U) (he U)
  intro u r g hr price
  exact Guard.sensor rooms prepared read fares price hr

end YM.Integration.WilsonCenteredMountedCapture
