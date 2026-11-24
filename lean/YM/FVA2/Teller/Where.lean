import YM.FVA2.Teller.Later
/-!
# Install rank-budgeted plans

`Installed` includes all the `Sag` requirements (the compensated
`TaylorOKF`, `base`, `still`), and adds the rank, parity, proofH etc.
requirements needed in our realization. For `b=true` the rank budgets
forbid the highest-rank changes (at positive order, see `Sturdy`, `House`).

The relaxed result (`b=false`) has no additional Taylor jet premise (it
still needs the stated bulk input for `relaxed_p`; see `luminosity`,
with bulk appointment from the supplied MS comparison). For the strict result
here `spectrum` keeps a Taylor-jet hypothesis `Rule`, for all d and
actual fields. See `Inked/Combined` for the discharge: this will **not**
turn into an assumption in the comparison.
-/
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 4600
namespace YM.FVA2.Teller.Homes
open Function Set Filter Finset MeasureTheory Metric Real
open Lattice MS MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Arts MS.High MS.High.Knobs MS.Outlook MS.Train MS.Emit
open MS.Local.Physical MS.Menus MS.Land MS.Lifting MS.Native MS.Native.Orient MS.Native.Chart MS.Cylinder MS.Cylinder.Lab
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Wind MS.Wind.Leading
open Position Position.Wheel Position.Axes Position.Favors Ace Parity Capacity Desk
open MS.Native.Paint Register
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {b:Bool} {p:Team}
local notation "℘"=> Press.portDeck G
variable (Y:XSpace.Initialize G)
local notation "Γ"=> Press.wickInput Y
variable (X:MS_Data G ( OpenAxis.Plot (Press.portDeck G)))
structure Installed (A:Prescription ℘)(b:Bool) : Prop extends Sag Y X A where
    rankC : Sturdy A b
    priced : Screen.Right A
    proofH (d:ℕ): Hcover ( A.fees d )
    proofP d (i:Plaid ℘ d) n y: Hue.only (n+i.1.val) (((A.fees d i n).proof.input y).val)
lemma launches (A:Prescription ℘)(h:G.Simple)(hx:TaylorOKF X Γ A)(hp:Sturdy A b): Installed Y X (Screen.brush ( amen ( Norm₀ A ) )) b:= by
 obtain ⟨hk,hH⟩:= upgrades Y X A hx; obtain ⟨h0,hp',h'H,ht⟩ := Screen.eternal Y X ( amen ( Norm₀ A ) ) h ( correct Y X _ hk ) ( strictU _ hH ) ( horiz _ ); exact ⟨ ⟨ h0,h'H,ht⟩, reserve hp, hp',fun _=>currency _, grow_reflect _ ⟩
abbrev Rule (p:Team): Prop:= ∀ d i,TreeJet Γ p (Archive d ( X.marks d i )) (Land.read i)
lemma spectrum (h:G.Simple)(hx:Fixed (col (skyline G p)) (Archive 4 X.bulk) true 4 1)(hk:b=true→ Rule Y X p) : ∃ S: Land.Prescription ℘, S.team=p ∧ Installed Y X S b:= by obtain ⟨V,hV,ht,hL⟩:= fromMS Γ X b h hx hk; exact ⟨Screen.brush ( amen (Norm₀ V)),hV, launches Y X V h ht hL ⟩
theorem relaxed_p (h:G.Simple)(hx:Fixed (col (skyline G p)) (Archive 4 X.bulk) true 4 1) : ∃ S: Land.Prescription ℘, S.team=p ∧ Installed Y X S false := spectrum Y X h hx fun h=>Bool.noConfusion h
lemma luminosity (N:Register.WilsonPrescription G)(h:G.Simple)(t:Bool) : ∃ V:Land.Prescription (Press.portDeck G), V.team=( Continuum.Continuation.proofStart h (Reg.supplies N.scheme X) t ).team ∧ Installed N.scheme X V false := relaxed_p _ _ h (Continuum.Continuation.plan ( Reg.supplies N.scheme X ) h t |>.taylor.bulk )
end YM.FVA2.Teller.Homes
