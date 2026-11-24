import YM.FVA2.O.Pad.Fare
/-!
# Extension by quieting all edges outside the true indices (no evanescent correlator)

An algebraic operation used only for constructing dummy exact interpolants. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Pad
open MS Function Filter Set Finset MS.Plane MeasureTheory Real Metric
open Momentum Heat Koszul Flux High Landau Detect MS.Color Book Signal Arts Alps MS.Local.Physical
open Wire
open scoped Topology ContDiff Interval
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {G:Gauge}{m k n:ℕ}{t b:ℤ}
local notation "h0"=> Nat.zero_le m
-- all ghosts allowed
abbrev down (i:Arts.L m) : Arts.L 0 := if h:i.val < Arts.Zed 0 then ⟨i.val,h⟩ else 0
abbrev shrink (i:Cfield G m) : Cfield G 0:= ( (i.1.1.map down, i.1.2), i.2 )
lemma shrink_p (i:Cfield G m): parity (shrink i)=parity i := by rcases i with ⟨⟨_|i,_|_⟩,k⟩<;>rfl
lemma shrink_w (i:Cfield G m): wfield (shrink i)=wfield i:= by rcases i with ⟨⟨_|i,_|_⟩,k⟩<;>rfl
lemma shrink_g (i:Cfield G m): ghostNo (shrink i)=ghostNo i:= by rcases i with ⟨⟨_|i,_|_⟩,k⟩<;>rfl
abbrev cube (i:L m):ℂ:= if i.val < Arts.Zed 0 then 1 else 0
abbrev accept (i:Cfield G m):ℂ := Option.elim i.1.1 1 cube
abbrev floor0 : Legs ( Shore G m ) → Legs (Shore G 0):= List.map (Prod.map shrink (Arts.Cl h0))
def taxA (l:Legs (Shore G m)) : ℂ:= (List.map (accept ∘ Prod.fst) l).prod
def bracket (F:Law G) (m:ℕ) : Rack G m:= fun l=> taxA l * F (floor0 l)
lemma from_head (F:Law G)(m:ℕ)(i:Shore G m): D i (bracket F m)= accept i.1 • bracket (D (shrink i.1, Cl (Nat.zero_le m) i.2) F) m:= by ext p; simp only [at_D,bracket,taxA, List.map_cons,List.prod_cons,Pi.smul_apply,smul_eq_mul, floor0, Function.comp_apply]; rw [mul_assoc]; rfl
omit [FiniteDimensional ℝ E] in
lemma taxes (F:Law G)(w:Wire ( Cfield G m ) E (SectorP m))(x:E): fieldVal (bracket F m) w x= taxA (sail w 0) * fieldVal F (w.map (fun i=> (shrink i.1, (Cl h0).comp i.2))) x:= by unfold fieldVal bracket; congr 1 <;> first| unfold taxA; simp [sail,List.map_map]; rfl| unfold floor0 sail; rw [List.map_map,List.map_map]; rfl
lemma massF (w:Legs ( Shore G m )) : mass (floor0 w) = mass w := by induction w with| nil=>rfl| cons i l ih=> simp only [ floor0, List.map_cons,Price_cons ]; rw [ ih ]; congr 1
lemma ghostF (l:Legs (Shore G m)): fieldDim ghostNo ( floor0 l )= fieldDim ghostNo l:= by induction l with| nil=>rfl| cons i l ih=> rw [ field_cons,floor0,List.map_cons,field_cons, ih ]; congr 1; exact shrink_g i.1
lemma shiftA (l:Legs ( Shore G m ))(s:ℝ) : floor0 ( sr s l )= sr s (floor0 l) := by induction l with| nil=>rfl| cons i l ih=> unfold sr floor0 at *; rcases i with ⟨u,x⟩; simp [ih]
lemma charge_A (l:Legs (Shore G m))(s:ℝ): taxA (sr s l)=taxA l:= by unfold taxA sr; rw [ List.map_map ]; rfl
lemma in_A (l:Legs (Shore G m)): floor0 (invertMom l)=invertMom (floor0 l):= by induction l with| nil=>rfl| cons i l ih=> unfold floor0 invertMom at *; rcases i with ⟨u,x⟩; simp [ih]
@[simp] lemma accept_real (i:Cfield G m): star (accept i)=accept i:= by rcases i with ⟨⟨_|i,_|_⟩,k⟩<;> simp [accept,cube]
lemma tax_real (l:Legs (Shore G m)): star (taxA l)=taxA l:= by induction l with| nil=>exact star_one _| cons i l ih=> unfold taxA at *; simp only [List.map_cons,List.prod_cons,star_mul',ih, Function.comp_apply,accept_real]
lemma pick {X: Law G}(H:Halo.Pace (n:=0) X k t b): Halo.Pace ( bracket X m ) k t b:= by
    refine ⟨ ?_,?_,?_,?_, ?_,?_ ⟩
    · intro E _ _ _ w; simp_rw [ funext (fun x=> taxes X w x) ]; exact ( H.price _ _ ).L ( ContinuousLinearMap.mul ℝ ℂ _ )
    · intro l x; rw [← massF l]; unfold bracket; rw [charge_A,shiftA, mul_left_comm,H.home]
    · intro l i j r; unfold bracket floor0; simp only [List.map_append,List.map_cons]; rw [ H.sym ]; simp only [taxA,List.map_cons,List.map_append,List.prod_append,List.prod_cons, field, Prod.map_fst,shrink_p]; ring
    · intro l hl; unfold bracket; rw [H.ghost _ (show fieldDim ghostNo (floor0 l)≠t from by rw [ ghostF l ]; exact hl ),mul_zero]
    · intro l; unfold bracket; rw [ in_A,H.sense,star_mul',tax_real,show taxA (invertMom l)=taxA l from ?_]; unfold taxA invertMom; rw [List.map_map]; rfl
    intro l hl; exact mul_eq_zero_of_right _ ( H.up _ ( by rw [floor0,List.length_map]; exact hl ) )
end YM.FVA2.O.Pad
