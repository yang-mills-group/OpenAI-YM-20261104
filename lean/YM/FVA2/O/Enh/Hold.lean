import YM.FVA2.O.Enh.Venue
/-!
# Rectangular layout specialization for further FAR estimation (continuum)

Use labels on disjoint groups of positions, through sufficiently large common lower threshold
in `clusterE`. On all compact inner and exterior profile spaces with the required separations,
verify geometry on both, and the cross requirement from `O/Enh/Venue` as the exteriors go far.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo O.Seam O.Hue
variable {G:Gauge}{I:Type}{n m d:ℕ}{ P:Geo I }
variable {x:I→ Points n}{y:I→ Points m}{v:Scan G n}{u:Scan G m}
lemma mapL ( x:I→ Points n)( y:I→ Points m)(v:Scan G n)(u:Scan G m) : Resembles ( orange x ) v ( orange ( fun i=> forest ( x i ) ( y i ) ) ) ( Fin.append v u ) ( Left n m ) Finset.univ:= ⟨ fun i _=> funext fun _=> congr_arg _ (forest_left i), fun _ _=> Fin.append_left .. ⟩
lemma mapR (x:I→ Points n)(y:I→ Points m)(v:Scan G n)(u:Scan G m): Resembles (orange y) u ( orange (fun i=> forest ( x i ) ( y i ))) ( Fin.append v u ) ( Right n m ) Finset.univ:= ⟨ fun i _=> funext fun _=> congr_arg _ ( forest_right i ),fun _ _=> Fin.append_right .. ⟩
abbrev lit (n m:ℕ):= Finset.map (Left n m) Finset.univ
abbrev arc (n m:ℕ):= Finset.map ( Right n m ) Finset.univ
lemma collide (i:Fin n)(m:ℕ): Left n m i∉ arc n m:= by rintro hp; obtain ⟨j,hj,hp⟩:= Finset.mem_map.mp hp; exact opposite i j hp.symm
lemma ne_lit (j:Fin m)(n:ℕ): Right n m j∉ lit n m:= by intro hp; obtain ⟨i,hi,h⟩:= Finset.mem_map.mp hp; exact opposite i j h
@[simp] lemma packed (n m:ℕ): arc n m ∪ lit n m= Finset.univ:= by
    apply Finset.eq_univ_of_forall; intro i; induction i using Fin.addCases with| left i=> exact Finset.mem_union_right _ ( Finset.mem_map_of_mem ( Left n m ) (Finset.mem_univ i) )| right i=> exact Finset.mem_union_left _ (Finset.mem_map_of_mem ( Right n m ) ( Finset.mem_univ i ))
abbrev lamps (x:I→ Points n)(y:I→ Points m):= orange (fun i=> forest ( x i ) ( y i ))
lemma lamp_h (hp:Cluster P ( orange y ) ( orange x )): Ensemble (orange y) ( orange x ) ( lamps x y ) u v ( Fin.append v u ) Finset.univ Finset.univ ( Right n m ) ( Left n m ) := by obtain ⟨h,hp,hV,H,hE⟩:= hp; exact ⟨ mapR ..,mapL .., colored ( P:=P ) ( mesh_sep h ) ( mesh_sep hV ) (fun i j=> hE j i),fun i _=> ne_lit i n ⟩ -- dot
local notation "Λ"=> Hue.Counter ( Press.portDeck G )
abbrev roof (m:ℕ): Fin (1+m) := Left 1 m 0
def shelf (m:ℕ) {G:Gauge} (u:Scan G m)(d:ℕ)(i: Counter ( Press.portDeck G ) d ): Scan G (1+m):= Fin.append ( Single ( actor i ) ) u
lemma litOne (m:ℕ): lit 1 m={roof m}:= by rw [ lit, show ( Finset.univ:Finset ( Fin 1 ) )={0} from (by ext; simp),Finset.map_singleton ]
@[simp] lemma roof_lamps (m:ℕ): insert ( roof m ) ( arc 1 m )= Finset.univ:= by obtain h:= packed 1 m; rw [ litOne, Finset.union_singleton ] at h; exact h
lemma greeting (he:∀ i,y i∈ Outside m): InTune (orange y) (orange (fun i=> outgoing ( y i ))) u ( shelf m u d ) Finset.univ ( Right 1 m ) ( roof m ) := ⟨ orange_h he, funext fun p=> Eq.trans ( congr_arg Theater.out ( forest_left ( x:= (0:Points 1) ) ( y:=y p ) (0:Fin 1) ) ) ( map_zero _ ), fun _=> Fin.append_left .., fun _=> mapR .., fun i _=> Ne.symm (opposite (0:Fin 1) i) ⟩
variable {s:Set ( Points n )}{S:Set ( Points m )}
abbrev Sip (n':ℝ)(s:Set (Points n))(S:Set (Points m)):= (s × S) × Set.Ici n'
def VenueP (s:Set (Points n))(S:Set (Points m))(v:ℝ)(n':ℝ)(h:0≤n'): Geo (Sip n' s S):={
    θ x:=x.2.val
    η _:=v
    room x:= h.trans x.2.property }
abbrev large (P:Geo I) (x:I→ Points n)(y:I→ Points m):= Cluster P ( orange ( Stretch P y )) ( orange x )
lemma clusterE (hs:IsCompact s)( hP:s⊆conf n)(he:IsCompact S)(ht:S⊆Outside m): ∀ᶠ b:ℝ in atTop,∀ {I':Type} {P:Geo I'},(∀ i,b ≤ P.θ i)→ ∀ (x:I'→ Points n)(y:I'→ Points m),(∀ i,x i∈s)→(∀ i,y i∈S)→ large P x y := ( Cross hs he ht ).mono fun _ h _ _ ht' x y hx hz=> ⟨ ZoneJ hs hP hx, fixed_J hs hx,Zone_Ω he (fun _ p=> Enh.room (ht p)) hz,row_Ω he ht hz, fun i j=> h ht' x y hx hz j i⟩ -- ambiguity
end YM.FVA2.O.Enh
