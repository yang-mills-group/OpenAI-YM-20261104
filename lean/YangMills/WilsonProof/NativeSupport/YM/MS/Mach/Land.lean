import YM.MS.Mach.Land
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Pick
/-!
# The first usable High theorem. Taylor matching of DREG/MS projected Wilsonian vertices to
 heat-scaled Z-cover vertices from Wilson lattice (bulk + marks). Scale/plane uniform UV estimates
 and one prescription for all orders, insertions, and fields (with ghosts included at high if needed).
 Still not correlation functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Land
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical -- Pole not opened yet
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{k m n h d:ℕ}{V:Box (Mob G)}{F H:ℂ→Mob G}{B:Deck G}
-- genuine labels: only @d for mark comparison, BIndex even including zero. enlarge to dimensions when forming shift.
lemma sizeG (i:Plaid B d): (read i).size=d:= rfl
abbrev PerG (B:Deck G)(v:ℤ):= B.carries v
lemma expands (i:Glyph B d): ∃ V,Ele i.size i.grade i.read V:= pin (B.le (B.form ..)) -- ugly
abbrev Blue (G:Gauge):= T ( Flats G )
abbrev CostsM (G:Gauge):= T (Coat G)
lemma suitable (B:Deck G) : Nonempty (Booked B):= by choose V h using fun d i=> expands ( read (d:=d) (B:=B) i); exact ⟨⟨V,h⟩⟩
structure MS_Data (G:Gauge){B:Deck G}(A: Booked B) where
   bulk: Blue G
   marks (d:ℕ)(i:Plaid B d): Blue G
   poleS : CostsM G
   poles (d:ℕ) (_i:Plaid B d): CostsM G
   bulkOK : leader G bulk (gloss (pulseX G)) poleS
   markOK d i: comet d 0 bulk (gloss ( Literal.linear ( Mob G ) ( A.optics d i ))) (marks d i) (poles d i)
lemma bookedMS (A:Booked B): Nonempty (MS_Data G A):= by
    obtain ⟨X,p,hX⟩:= allLeader G; choose V Q h using (fun d i=> satisfyY hX ( ( A.law d i ).grows )); exact ⟨ ⟨X,V,p,Q,hX,h⟩ ⟩
-- program. Highest weight logs triangular.Exact shifts included by Ξ of Field.
structure Prescription (B: Deck G) where
   team: Team
   fees (d:ℕ) (_i: Plaid B d): Acts B d
   init (d:ℕ) (i:Plaid B d): FitOrder (read i) (fees d i 0)
structure TaylorOK {A:Booked B}(M:MS_Data G A)(V:LitBook B)(S: Prescription B): Prop where
   bulk: Fixed (col ( skyline G S.team )) ( Archive 4 M.bulk ) true 4 1
   mark (d:ℕ) (i: Plaid B d): Fixed ( col (horizon V S.team (S.fees d i) )) ( Archive d (M.marks d i)) false d 0
lemma leader_M (hc:G.Simple)(B:Deck G)(A:Booked B)(M:MS_Data G A): ∃ S:Team, Fixed (col (skyline G S)) (Archive 4 M.bulk) true 4 1 := by -- forgot h
    apply portH _ ( Outlook.dock M.bulkOK wisdom ) ( stable M.bulkOK); exact hc
variable (hc:G.Simple)
include hc
-- remove lean incomplete above
theorem High_stops {A:Booked B}(X: MS_Data G A)(V:LitBook B): ∃ P: Prescription B,TaylorOK X V P:= by
    obtain ⟨p,H⟩:= leader_M hc B A X; have he d (i:Plaid B d):= physicalAt V (j:=read i) hc H ( Outlook.fieldD X.bulkOK (X.markOK d i) wisdom (( A.law d i).moodQ)) (initialHF (A.law d i) (sizeG i) (X.markOK d i)); choose S hs h using he; exact ⟨⟨ p,S,hs ⟩,⟨ H,h ⟩⟩
omit hc in
lemma uniq {A:Booked B}(X Y: MS_Data G A): X.poleS=Y.poleS ∧ (∀ n,Pact (X.bulk n) (Y.bulk n)) ∧ ∀ d i, (X.poles d i)=(Y.poles d i) ∧ ∀ n,Pact (X.marks d i n) ( Y.marks d i n):= by
    obtain ⟨H,h⟩:= unique_B X.bulkOK Y.bulkOK; exact ⟨ H,h,fun d i=> unique_M (X.markOK d i) (Y.markOK d i) h⟩
end YM.MS.Land
