import YM.FVA2.Inked.Pitch
import YM.FVA2.TreeT.Industry
import YM.FVA2.Teller.Where
/-!
# The needed Taylor-jet equality

At the prepared `Plot` (`inherent`), including the nonlinear orders.
One can read the stencil (`Survey`) in the rank calculation (`measures`)
and obtain the match on the homogeneous symbol, needed at *leading* in
the projection/physical comparison. See `Inked/Combined` for the
construction discharging the rank-budgeted comparison with this result.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen Press
open MS MS.Koszul MS.Plane MS.Native MS.Native.Sew MS.Native.Draft MS.Cylinder MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Local.Physical MS.Lifting MS.Halo MS.Book MS.Heat MS.Tone MS.Plane.Wire Source Labels
open Position.OpenAxis
variable {E F J Y : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}{H:Hol G}{d κ n:ℕ}(S:XSpace.Survey G H d)
local notation "P"=> E4
local notation "L"=> Lane4 G
local notation "I"=> Complex.I
local notation "W"=> G.Color
local notation "K"=> Cfield G 0
local notation "Γ"=> portDeck G
local notation "ĉ"=> Plot Γ
lemma measures (p:Labels.Pol G)(hq:At p (κ,n)) (h:κ≤d): Face wfield (run (sat S p)) (seed G p 1 0) κ false:= by
    let D(u:ℕ×ℕ)(p:Labels.Pol G): Prop:= u.1≤d→ Face wfield ( run ( sat S p ) ) ( seed G p 1 0 ) u.1 false; refine axisI D hq (fun c hc=>?_) (fun i hi=>?_) (fun x i f hx ih hI=>?_) (fun x f g hf hg ih if' hx=> ?_) h
    · rw [ sat_constant,sightC,map_smul]; change Face wfield (c • (shade paywave (Cylinder.piece 1))) (coin c:Law G) (0:ℤ) false; rw [coin_turn, show coin (A:=Lane4 G) c=c • coin 1 from funext (fun w=> by rcases w with _|_; exact (mul_one c).symm; exact (mul_zero c).symm ) ]; apply face_mul; intro x _; cases x; exact Rest.level contDiff_const rfl; exact Rest.zero _
    · rw [sat_zero,map_zero,map_zero]; exact face_zero _
    · have hp:i.1 +2+x.1≤d:= hI; obtain hv:=Music.rupture S i (by omega); rw [ sat_l, ← sat_X S i, seed_p, wave_cost ]; have hh : (( ( bidegree i+x ).1:ℕ ):ℤ)=i.1+2+x.1:=by change (( i.1+2+x.1 :ℕ ):ℤ)=_; omega; -- parse colon
      rw [ hh ]; exact face_product hv ( ih (by omega))
    rw [sat_add,map_add,map_add,Pi.add_apply,Pi.add_apply]; exact face_add ( ih hx ) ( if' hx )
-- expose all at h=d onto portDeck
variable (Y':XSpace.Initialize G)
open MS.Land MS.Menus MS.Motif.Literal
private lemma atOne (f:Box ( Mob G )): value ( Mob G ) 1 f=∑ i∈ f.support, f i:= by -- i shadow
   rw [ value,Finsupp.lsum_apply ]; unfold Finsupp.sum; simp
lemma arrival (X: Land.Booked Γ)(p:Land.Plaid Γ d)(w:Legs L)(h:w.length=( Land.read p ).grade+n): (value (Mob G) 1 ( X.optics d p )) 0 w=X.optics d p n 0 w:= by
    let f:= X.optics d p; rw [atOne ( X.optics d p ) ]; change (∑ i∈ f.support,f i) 0 w=_; rw [ Finset.sum_apply,Finset.sum_apply, Finset.sum_eq_single n ]; intro i hi hx; exact Teller.Hazel.bornTree _ _ _ ( X.law d p |>.1 ) _ (by rw [mod_int]; omega)
    intro hx; rw [ Finsupp.notMem_support_iff.mp hx ]; rfl -- orientation
lemma inherent (p:Land.Plaid ( Press.portDeck G ) d): TreeT.innate (Press.wickInput Y') (Plot (Press.portDeck G)) p:= by
    intro n k w hl hw; let L':= ( Land.read p ); let F:= Theater.film ( Press.portDeck G ) p.2 (r:=p.1.val) (h:=d); let v:= Theater.Resume _ d p.1.val ( Module.finBasis ℝ ( (Γ).carries d p.1.val ) p.2 ); rw [ ← arrival (ĉ) p w hl, show value ( Mob G ) 1 ( (ĉ).optics d p )=seed G F 1 from priceR v ]; change torch k ( run ( Press.dot ( Y'.surveys d ) F ) ) w=_; obtain hF : F∈ Theater.Film0 G d p.1.val:= v.property; obtain ⟨ht,hv,H⟩:= Theater.cinema F|>.mp hF; rw [ ← Press.sat_real _ F H ]; exact face_here ( measures (κ:=d) _ _ ht le_rfl ) (fun i=> Bool.noConfusion i) k hw
end YM.FVA2.Inked
