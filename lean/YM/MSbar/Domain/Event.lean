import YM.MSbar.Domain.Pull
import YM.MSbar.Grid.Reach
/-! Uniform spacetime convention. Four physical components; Hat is true real plane pair workspace
for analytical continuation, fed integer s at large dimensions only in specific **finite-operation identity
transfers**, with their bounds. Not for passing limits of infinite measures. At m=0 the hat components are
gone, all functions still on bar momentum. m in calls counts pairs of dimensions (d=4+2s). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops Function Filter Set
open scoped Topology BigOperators Classical ContDiff

abbrev Bar:= Hat 2
abbrev Mom (m:ℕ):= Bar × Hat m
variable {C:Type} {m n q:ℕ} {T:ℕ→Type} {L:Move m n}
abbrev Token (C:Type)(m:ℕ):= C × Hat m
abbrev Letter (C:Type)(m:ℕ):= Wave (Token C m) (Mom m)
abbrev Words (C:Type)(m:ℕ):= List (Letter C m)

abbrev label {C:Type}{m:ℕ}(a : Letter C m):= a.1.1
def transient (C:Type): Motion (Token C):= (constMotion C).prod vectors
def momentum : Site Mom := (Site.simple Bar).prod Site.moving
def letters (C:Type): Motion (Letter C):= (transient C).prod momentum.toMotion

def taxi (L:Move m n) : (Mom m) →ₗ[ℝ] Mom n:= LinearMap.prodMap LinearMap.id L.toLinearMap
@[simp] lemma aleph (T:Move m n) (a: Mom m):(taxi T a)=(a.1,T a.2):=rfl

def line (C:Type): Motion (Words C) := {
    move := fun V v=> v.map ((letters C).move V)
    triv := fun a=> by
        have h (m): (letters C).move (LinearIsometry.id (E:= Hat m))=id:=funext ((letters C).triv)
        simp [h]
    together := fun V W v=> by rw [List.map_map]; exact congr_arg (· |> v.map) (funext fun U=> (letters C).together V W U) -- type?
}
lemma work (C:Type)(L:Move m n)(x:Letter C m)(v): (line C).move L (x::v)=((x.1.1,L x.1.2),taxi L x.2)::(line C).move L v:=rfl
@[simp]lemma notates (C:Type)(V:Move m n) : (line C).move V []=[]:=rfl
lemma quiet_move (v:Words C m) : channel ((line C).move L v)=taxi L (channel v) := by
   induction v with
   | nil=> rw [notates,channel_nil,channel_nil,map_zero]
   | cons a q ih=> rw [work,channel_cons,channel_cons,ih,map_add]
lemma taxi_inj (V:Move m n): Injective (taxi V):=fun _ _ h=>Prod.ext (congr_arg (Prod.fst : Mom n→Bar) h) (V.injective (congr_arg (Prod.snd : Mom n→Hat n) h))

variable {E X Y: Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
lemma moment_plot (p:E→ Mom m): momentum.plot p↔ HasTemperateGrowth p := by
   constructor
   · intro h; cases h; exact tame_pair (f:=Prod.fst ∘ p) (g:=Prod.snd ∘ p) (by assumption) (by assumption)
   intro hp; exact ⟨tame_projL.comp hp,tame_projR.comp hp⟩

inductive Plot (E : Type)[NormedAddCommGroup E][NormedSpace ℝ E] (C:Type)(m:ℕ) : (E→ Words C m) → Prop where
    | empty : Plot E C m (fun _ => [])
    | cons (x:C)(t:E→Hat m)(p:E→Mom m){u:E→Words C m}(ht:t.HasTemperateGrowth)(hp:p.HasTemperateGrowth)(hu:Plot E C m u) : Plot E C m (fun w=>((x,t w),p w)::u w)
namespace Plot
variable {u v: E→ Words C m}
lemma refine (h:Plot E C m u)(p:X→E)(hp:p.HasTemperateGrowth): Plot X C m (u∘p):=by induction h with | empty=>exact empty | cons x t s h h' _ ih=> exact cons x (t∘p) (s∘p) (h.comp hp) (h'.comp hp) ih
lemma app (h: Plot E C m u)(hh:Plot E C m v): Plot E C m (fun x=>u x++v x) :=by induction h with | empty=>exact hh | cons x t s h h' _ ih=> exact cons x t s h h' ih
lemma passage (h:Plot E C m u): Plot E C n ((line C).move L ∘ u):=by
    induction h with
    | empty=> exact empty
    | cons x t s h h' _ ih=> exact cons x (fun v=> L (t v)) ((taxi L) ∘ s) ((L.toContinuousLinearMap).hasTemperateGrowth.comp h) ((LinearMap.toContinuousLinearMap (taxi L)).hasTemperateGrowth.comp h') ih
lemma sum (h:Plot E C m u): (channel ∘ u).HasTemperateGrowth:=by induction h with | empty=> exact HasTemperateGrowth.const 0 | cons x t s h h' hu ih=> unfold Function.comp; simp_rw [channel_cons]; exact h'.add ih
lemma cte (u:Words C m): Plot E C m (fun _=>u):=by induction u with | nil=>exact empty | cons x u ih=>exact cons x.1.1 _ _ (HasTemperateGrowth.const x.1.2) (HasTemperateGrowth.const x.2) ih
end Plot

abbrev Balanced {C:Type}{m:ℕ}(s : Words C m) := channel s=0

def arena (C:Type): Site (Words C):= {
    toMotion:= line C
    plot:=fun p=> Plot _ _ _ p ∧ ∀ x,Balanced (p x)
    views:=fun h=> by intro p hp;exact ⟨h.1.refine p hp,fun x=> h.2 (p x)⟩
    size_up:=fun V=> by intro E i1 i2 i3 x h; exact ⟨h.1.passage,fun y=> by unfold Balanced comp; rw [quiet_move,h.2 y,map_zero]⟩ }
end YM.MSbar.Domain
