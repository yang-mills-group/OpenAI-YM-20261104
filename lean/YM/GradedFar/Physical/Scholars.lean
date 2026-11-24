import YM.GradedFar.Round.G9
import YM.GradedFar.Physical.Output

/-!
# Assembly on the chosen space S, with H & W as before, towards MeasuredInverse
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
    (E : (d:ℕ)→ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ:ℝ→ℝ)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (W : Bookshelf N U J K E Y θ) (D : Earned N M U J K θ) (hD:oriented U K)
    (ht: LogTrace U Q.port) (he:∀ h:ℕ,∀ᶠ r in τ, ∀ u : Sec G h,K r h u=J r h (E h r u))
    (hGrid : Round.Grid N U J)
include H D
lemma learned : Scaled N M K θ := fun n p _ _ hb hc=> Growth.replacement (d:=n) N M H (Moving.Zenith (next K n)) θ D.clock
    (hasMotion K _) (fun _ hj=>(D.short _ _ hj).2) (fun j hj=>(D.short j 6 hj).1) (adjusted K) (show Zenith (next K n)=Growth.reshape (adjusted K) n from rfl) hc hb p
include W he hD ht hGrid
/-- The **physical pricing actually supplied** in Lean *relative to* the hypotheses
of the indicated stages of the proof. See parameters. No claims constructing the prerequisites. Budget
is on bodies of exact `Scaled`,`OldCost`,`SourceCost` as above. Scale also for growing for all `T≥1`,
including actual fee for matrix A and inverse; and `G.6` all pieces of `horizon_lease`. At θ given and
bought compact & grid receipts from (C.5) as stipulated. -/
theorem earned_costs : Scaled N M K θ ∧ OldCost U K Q ∧ SourceCost N U K θ := ⟨learned N M H U J K θ D,
   paid_history N M H U Q J K θ D hD ht, Round.rounded_world N M H U J K E Y θ Q W D hD ht he hGrid⟩
-- continue
/-- Keep one viewpoint and book, answer these requests. Uniform over compacta & sector phase etc.
  Compare actual packet representative **including** actual detector inverse expenditures. On these
inputs the continuation (detector data & horizon through output h in hypotheses) doesn't need further
post-(F.1) spatial estimates. This is the point value version. -/
structure Towards : Prop where
   first_line (n m:ℕ)(d:Fin n→ℕ)(e:Fin m→ℕ) (K':Set (Points n))(Y':Set (Points m))(B C:ℝ) :
     0<B → 0<C → IsCompact K' → K'⊆conf n → IsCompact Y' → Y' ⊆ Outside m →
      ∀ (p:ℕ)(L R:ℝ),WithinError N M (Y0 U K d e) (adjusted K) (upper G C B) K' Y' θ p L R
   advanced (n m:ℕ)(d:Fin n→ℕ)(e:Fin m→ℕ) (K':Set (Points n))(Y':Set (Points m)) : 0<n→ IsCompact K' → K' ⊆ conf n→ IsCompact Y' → Y'⊆Outside m →
     ∀ (p h:ℕ)(L R c C η:ℝ),0<c→ c≤C → η<1 → ∀ᶠ B:ℝ in atTop,∀ᶠ j:ℕ in atTop,Tolerates N M U K Q θ d e K' Y' p h j c C η B L R
   kernel (n:ℕ)(d:Fin n→ℕ)(K':Set (Points n)) : IsCompact K' → K' ⊆ conf n→ ∀ (p:ℕ)(L:ℝ),
     ∃ D : ℝ,0<D ∧ ∀ᶠ r in τ, ∀ i:View U, ∀ x∈K',∀ u: Inputs G d, Within L u →
       ‖alone U K i r x u-crop p (θ r) (Wave.value N M x u)‖ ≤ D*θ r^(p+1)
   output (n:ℕ)(d:Fin n→ℕ)(K':Set (Points n)) : 0<n→ IsCompact K' → K' ⊆ conf n→
    ∀ (p h:ℕ)(L:ℝ), ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in τ, ∀ i : View U, ∀ x∈K', ∀ u : Inputs G d, Within L u →
      Ball (D*θ r^(p+1)) (packet U K Q d h r i x u - Wave.cropped N M x u h p (θ r))

theorem books_paid : Towards N M U K θ Q := by
    obtain ⟨hz,hA,hP⟩:=earned_costs N M H U J K E Y θ Q W D hD ht he hGrid
    refine ⟨fun n m d e X Y B C hb hc hX hx hY hy p L R=> ?_,fun n m d e X Y hn hX hx hY hy p h L R c C η hc hC hη=>?_, ?_,?_⟩
    · exact paid_first H _ _ θ _ (Y0 U K d e) hX hx hY hy ((paid_reading simple θ D.clock).mono fun i h=>h.2.2.2) (fun i=>hz _ p B C hb hc) (hP n m d e p X Y hX hx hY hy B C hb hc) L R
    · exact lease H D.clock hA hP hz hX hx hY hy hn d e hη hc hC h p L R
    · exact fun n d X hX hx p L=> kernel H D.clock hP hX hx L d p
    exact fun n d X hn hX hx p h L=> measured_output H D.clock hA hz hP hX hx L hn d h p
end
end YM.FVA2.GradedFar.Physical
