import YM.Integration.WilsonMeasuredPublicEntranceDeposits

/-! Ordered switching of finite factors inside the one original held Wilson conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOrder
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm
open scoped Classical BigOperators
variable {I:Type}
def factors {Y:Type} (u:I→Y→ℂ) (names:List I) (y:Y) : ℂ := (names.map (fun i=>u i y)).prod

def changes {Y:Type} (a b:I→Y→ℂ) (head:Y→ℂ) : List I→List (Y→ℂ)
  | []=>[]
  | i::later=>(fun y=>head y*(a i y-b i y)*factors b later y)::changes a b (fun y=>head y*a i y) later

variable {G:Gauge}(C:Family G){N p f K:ℕ}
local notation "X" i:max => Config G (C.side i p)

def BoundedAt {k:ℕ} (h:X k→ℂ) : Prop :=
  AEStronglyMeasurable h (prior G _) ∧ ∃M:ℝ,∀U,‖h U‖≤M

theorem one : BoundedAt C (fun _ : X K=>(1:ℂ)) :=
  ⟨aestronglyMeasurable_const,1,fun _=>by simp⟩

theorem times {a b:X K→ℂ} (ha:BoundedAt C a) (hb:BoundedAt C b) :
    BoundedAt C (fun U=>a U*b U) := by
  obtain ⟨ma,A,ca⟩:=ha
  obtain ⟨mb,B,cb⟩:=hb
  refine ⟨ma.mul mb,A*B,fun U=>?_⟩
  rw [norm_mul]
  exact mul_le_mul (ca U) (cb U) (norm_nonneg _) ((norm_nonneg _).trans (ca U))

theorem collection (a:I→X K→ℂ) (ha:∀i,BoundedAt C (a i)) (names:List I) :
    BoundedAt C (factors a names) := by
  induction names with
  | nil=>exact one C
  | cons i later ih=>exact times C (ha i) ih

theorem integrable {a:X K→ℂ} (hC:C.Makes) (live:K≤N) (ha:BoundedAt C a) :
    Integrable (fun U=>(C.path.rep N p K).eval U • a U) (prior G _) := by
  obtain ⟨borel,M,cap⟩:=ha
  have earned:=actualTransport_weighted_integrable C hC live borel cap (le_refl K)
  rwa [actualTransport_base C hC live] at earned

/-- The product of previously switched arms is inside every signed hearing, and
every remaining arm keeps its original placement. -/
theorem switched (hC:C.Makes) (live:K≤N) (stop:f≤K) (W:X f)
    (a b:I→X K→ℂ) (ha:∀i,BoundedAt C (a i)) (hb:∀i,BoundedAt C (b i)) (names:List I)
    (h:X K→ℂ) (eh:BoundedAt C h) :
    actualTransport C (N:=N) (fun U=>h U*factors a names U) stop W-
      actualTransport C (N:=N) (fun U=>h U*factors b names U) stop W=
       ((changes a b h names).map (fun q=>actualTransport C (N:=N) q stop W)).sum := by
  induction names generalizing h with
  | nil=>simp [changes,factors]
  | cons i later ih=>
    let lead:=fun U=>h U*a i U
    let X₁:=fun U=>lead U*factors b later U
    let X₂:=fun U=>h U*factors b (i::later) U
    have p₁:=integrable C hC live (times C (times C eh (ha i)) (collection C b hb later))
    have p₂:=integrable C hC live (times C eh (collection C b hb (i::later)))
    have delta:(fun U=>h U*(a i U-b i U)*factors b later U)=(fun U=>X₁ U-X₂ U) := by
      funext U
      simp only [X₁,X₂,lead,factors,List.map_cons,List.prod_cons]
      ring
    have combine:=congrFun (ActualWilsonAbsoluteTransport.sub C hC live p₁ p₂ stop) W
    have side : (fun U=>h U*factors a (i::later) U)=(fun U=>lead U*factors a later U) := by
      funext U
      simp only [lead,factors,List.map_cons,List.prod_cons,mul_assoc]
    rw [side]
    change _-actualTransport C (N:=N) X₂ stop W=
      actualTransport C (N:=N) (fun U=>h U*(a i U-b i U)*factors b later U) stop W+
        ((changes a b lead later).map (fun q=>actualTransport C (N:=N) q stop W)).sum
    rw [delta,combine,←ih lead (times C eh (ha i))]
    abel

end YM.Integration.WilsonMeasuredPublicEntranceOrder
