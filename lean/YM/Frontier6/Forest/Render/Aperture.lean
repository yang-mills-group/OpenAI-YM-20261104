import YM.Frontier6.Forest.Render.Color

/-! Beacon monomials. Several groups simultaneous even when some other groups
 occupy projected branches. Store centers separation: unlike with residues
 already expanded into their own monomials, only valuations, not diameter ratio,
 matter in this price mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X Y:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
structure Spark (S:Table C.book) (I:Type) where
   Part: Type
   [ft:Fintype Part]
   [de: DecidableEq Part]
   [ne:Nonempty Part]
   whereAt: I→ Part→ E4
   origin : I→ E4
   tags : Part→ S.Tag
namespace Spark
attribute [instance] ft de ne
def real (A:Spark S I) : Art S I:= inscription S A.whereAt A.tags
def almost (K:Final C H S)(A:Spark S I) (d:ℕ): Art S I:= fun i=> all K (A.origin i) d (A.real i)
structure Shine (A:Spark S I)(T:Fareway I)(b:ℝ) (P:Fabric I):Prop where
   level : Wide T A.whereAt b
   lights : ∀ j:A.Part, T.Costs (fun i=> A.whereAt i j - A.origin i) (-b)
   supports : Extends T P (sheet A.whereAt)
   lives : Contains T P A.origin
lemma Shine.extends {A:Spark S I}{T:Fareway I}{b:ℝ}{P Q:Fabric I}(h:A.Shine T b P)(he:Extends T Q P) : A.Shine T b Q:= ⟨h.level,h.lights, he.trans h.supports, he.contains h.lives⟩
def lone (x:I→ E4)(v:S.Tag): Spark S I where
  Part:=Unit
  whereAt i _:=x i
  origin := x
  tags _ :=v
lemma shines_lone {x:I→ E4}(p:S.Tag){T:Fareway I}{b:ℝ}{P:Fabric I}(he:Contains T P x): Shine (lone x p) T b P:=
    ⟨fun i j h=> (h rfl).elim, fun i=> Fareway.Costs.free.cf (Eventually.of_forall fun i=>by simp [lone]), extends_sheet (fun _=> he),he⟩
lemma real_lone (x:I→ E4)(p:S.Tag) : (lone x p).real=fun i=> letter S (x i) p:=by ext1 i; unfold real inscription lone assembly; rw [Fintype.prod_unique]
-- base can be extracted without singleton fields distinguished further
end Spark
attribute [instance] Spark.ft Spark.de Spark.ne

namespace Flare
variable [Fintype V][Fintype X](K:Final C H S)(F:V→ Spark S I)(G₀:X→ Spark S I)(d:ℕ)
def showAt (i:I):= ∏ v:V,(F v).real i
def shared (d:ℕ) (i:I):= ∏ v:V,(F v).almost K d i
lemma showAt_join : showAt (Sum.elim F G₀)=showAt F*showAt G₀:=by ext1 i; unfold showAt; rw [Fintype.prod_sum_type]; rfl
lemma shared_join : shared K (Sum.elim F G₀) d= shared K F d * shared K G₀ d:= by ext1 i; unfold shared; rw [Fintype.prod_sum_type]; rfl
-- all group representatives for congruence
abbrev Eta (F:V→ Spark S I):=Sigma (fun i=> (F i).Part)
def whole (i:I)(x:Eta F):= (F x.1).whereAt i x.2
def home (i:I)(x:V):= (F x).origin i
def offset (i:I)(x:Eta F):= whole F i x-home F i x.1
def words (x:Eta F):= (F x.1).tags x.2
lemma showAt_raw : showAt F= inscription S (whole F) (words F):= by
    ext1 i; unfold inscription; exact (concatenate_many S (fun a x=>(F a).whereAt i x) (fun a x=>(F a).tags x)).symm
variable [DecidableEq V]
lemma pickup_eq (i:I): Fork.pickup (offset F i) (home F i)= whole F i:=funext fun j=> sub_add_cancel ..
lemma giving_eq (i:I)(z:V) : Fork.giving (offset F i) (home F i) (words F) z=(F z).real i:=by unfold Fork.giving; rw [pickup_eq];rfl
lemma shared_under (i:I) : Tale.Congr K (∏ z:V, Fork.packing K (offset F i) (home F i) (words F) d z) (shared K F d i):= by
    apply Tale.Congr.product K (V:=V); intro z _; unfold Fork.packing; rw [Fork.cost_center (c:=home F i),giving_eq]; exact (all_congr K d _ ((F z).real i)).symm K
lemma comparing (i:I)(s:StateIndex K): poll S (state K s) (Fork.combining K (offset F i) (home F i) (words F) d)= poll S (state K s) (showAt F i - shared K F d i):= by
    rw [Fork.combining_eq,map_sub,map_sub,(shared_under K F d i).done K s]; simp_rw [giving_eq]; rfl
end Flare
end YM.Frontier6.Forest
