import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Burst
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Family
/-! # Two-zone compact geometry for RoundMeter. Vary everything. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m l e :ℕ} {I: Type*} {F:Filter I} {A:Set (Points n)}{B:Set (Points m)}
structure Room (W C δ:ℝ) (A : Set (Points n)) (B:Set (Points m)) : Prop where
    compact_A : IsCompact A
    near : A ⊆ conf n
    compact_B : IsCompact B
    far : B⊆ Outside m
    covers : 2≤W
    size : 0≤C
    clearance : 0<δ
    clears : Original.Clears W C δ A B
    event : GradedFar259.clears W A B

lemma arrange (ha:IsCompact A)(hx:A ⊆conf n)(hb:IsCompact B)(hy:B⊆Outside m) : ∃ C δ:ℝ,
    ∀ᶠ W in atTop, Room W C δ A B := by
  obtain ⟨C,hC,δ,hδ,P⟩:= Original.arbitrarily_large ha hx hb hy
  exact ⟨C,δ,((eventually_ge_atTop (2:ℝ)).and P).mono fun i hi=>⟨ha,hx,hb,hy,hi.1,hC,hδ,hi.2.2.1,hi.2.2.2⟩⟩
variable {W C δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W C δ A B)
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} (sim:G.Simple)
-- no compact-state physics in these.
structure Aim (F:Filter I)(G:Gauge)(W a b:ℝ)(r T:I→ℝ) : Prop where
    reach : Tendsto r F late
    high : ∀ᶠ i in F,W ≤ T i
    bud : ∀ᶠ i in F,T i≤ a*g0 G (r i)^(-b)
-- all profiles here are paid in indicated compacts, including f-grid path & both homed fields.
abbrev joins (x:Points n)(y:Points m)(T:ℝ) := forest x (T • y)
include R
lemma compact_height : 2≤W := R.covers
include R
lemma height : 1 ≤ W := one_le_two.trans R.covers
variable (h:Aim F G W a b r T) (hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
include h
lemma aspirant : ∀ᶠ i in F, 1 ≤ T i := h.high.mono fun i hi=> (height R).trans hi
lemma view (sim:G.Simple) : Tendsto (fun i=>r i*T i) F late := hull sim ((aspirant R h).mono fun i hi=> zero_lt_one.trans_le hi) h.reach h.bud
include hx hy
lemma pay : ∀ᶠ i in F,Flash259HorizonFork.Ready (r i) (r i*T i) C δ (x i).ofLp (y i).ofLp:= by
  filter_upwards [hx,hy,h.high,h.reach.eventually self_mem_nhdsWithin] with i hx hy hh v; exact R.clears _ hx _ hy _ hh _ v
lemma permit : ∀ᶠ i in F, joins (x i) (y i) (T i) ∈ conf _ := by
  filter_upwards [hx,hy,h.high] with i hx hy hh; exact R.event _ hh _ hx _ hy
omit h hx hy R

variable {N : Family G}{f:Extraction.Order}{S:Table N.book}(U:Final N f S)(Y:ℝ→tower S)
    (o: Owner U) {X : Points n}{y':Points m}{u T':ℝ}
    (hc: joins X y' T'∈conf _)(hu:0<u)

-- explicit price path between all-topic common height and outward mixed reading
local notation "dS" => fun _:Fin n=>l
local notation "e'" => fun _:Fin m=>l
local notation "W0" => measures U Y dS e'
include hc hu
lemma illuminate (v:Tags G l n) (w:Tags G l m) :
    W0 o u T' X y' v w= physicalY U Y o.1 (Fin.append v w) u (joins X y' T') := by
  let K:= joins X y' T'; let y:= Fin.append v w
  rw [measure_eq]; let x:= atPosition o.2 u K.ofLp
  have hx:Injective x:= fun i j hi=> hc (smul_right_injective _ hu.ne' (add_left_cancel (show o.2+u • _=o.2+u • _ from hi)))
  refine Eq.trans ?_ (framed_entry U Y K o.1 u (d:=fun _=>l) y o.2 hu hc)
  rw [Orbits.whole_observed, Orbits.observed]
  refine Eq.trans ?_ (perm_observe (spectator U o.1) (spectate U o.1).laws.toSymmetric finSumFinEquiv (Orbits.names (enter Y u y)) hx)
  congr 1
  · funext j; cases j with
    | inl i=> change o.2+u • (X i)=_ ; rw [Function.comp_apply]; simp [atPosition,K,joins]
    | inr i=> change o.2+(u*T') • y' i=_; rw [Function.comp_apply]; simp [atPosition,K,joins,mul_smul]
  funext i; cases i <;> simp only [Function.comp_apply]
  · rename_i i; change (⟨l,_⟩: N.book.Token) = ⟨l,S.representative l ((enter Y u y) _ )⟩; rw [enter]; simp_rw [y]; simp
  rename_i i; change (⟨l,_⟩: N.book.Token) = ⟨l,S.representative l ((enter Y u y) _ )⟩; rw [enter]; simp_rw [y]; simp
lemma promote (hv:heights U Y u l) {d:Fin n→ℕ} {e:Fin m→ℕ} (v:Slots G d)(w:Slots G e)(hd:∀ i,d i≤ l)(he:∀ i,e i≤l) :
    measures U Y d e o u T' X y' v w = physicalY U Y o.1 (Fin.append (liftSlots hd v) (liftSlots he w)) u (joins X y' T') := by
  rw [ ← illuminate U Y o hc hu ]; simp_rw [measure_eq]; have h:= beside_separate hc hu o.2
  unfold Original.own liftSlots
  simp_rw [hv _ (hd _),hv _ (he _)]
  rw [lite U o.1 h hd,far_lite U o.1 h he]

lemma readyPT {V : Arenas G} {p:ℕ} {α:ℝ} {d:Fin n→ℕ} {e:Fin m→ℕ} (hd:∀ i,d i≤l)(he:∀ i,e i≤l)(v:Slots G d)(w:Slots G e):
    Comparing.reading V hd he X (T' • y') p α v w=crop p α (Reg.Point.story (fxt (V l) (joins X y' T')) (Fin.append (liftSlots hd v) (liftSlots he w))) := by
  rw [Comparing.read_eq]; congr 1; unfold Reg.Point.story; apply congr_arg; ext1 i; rw [bareRow_apply,kernel_on V hc, fxt,dif_pos hc]
end YM.FVA2.GradedFar259.Flash
