import YM.MS.Arts.Cabs
import YM.MS.Properties

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau
open scoped Topology ContDiff
variable {G:Gauge} {A B C:Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C] {b:Bool} {m n:ℕ}
abbrev Cfield (G:Gauge)(m:ℕ):= Leg (L m) G.ColorIndex
abbrev Shore (G:Gauge)(m:ℕ):= Note G (L m) (SectorP m)
abbrev Rack (G: Gauge)(m:ℕ):= Row (Cfield G m) (SectorP m) ℂ
abbrev Mob (G:Gauge):= ∀ m:ℕ,Rack G m
abbrev Ridge (G:Gauge)(m:ℕ):= Flux (Cfield G m) (SectorP m) ℂ
abbrev Rip (G:Gauge):= ∀ m:ℕ, Ridge G m
variable (h:m≤n)
def embA (f:A ↪ B): Leg A C ↪ Leg B C where
   toFun x:= (((x.1.1.map f), x.1.2), x.2)
   inj' x y H:= by
       rcases x with ⟨⟨_|a,p⟩,i⟩ <;> rcases y with ⟨⟨_|b,q⟩,j⟩ <;> simp only [Prod.mk.injEq,Option.map_none,Option.map_some,reduceCtorEq,Option.some.injEq, EmbeddingLike.apply_eq_iff_eq] at * <;> tauto
abbrev lift (h:m≤n): Legs (Shore G m)→ Legs (Shore G n):= List.map (Prod.map (embA (rises h) : Cfield G m↪_) (Left h))
end YM.MS.Arts
