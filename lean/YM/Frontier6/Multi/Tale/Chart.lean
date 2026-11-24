import YM.Frontier6.Multi.Tale.Smooth
import YM.Frontier6.Exact.Collar

/-! Correlating point exterior calls. All shapes fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Tale
open Function Finset Filter Spec
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {V X:Type*}[Fintype V][DecidableEq V][TopologicalSpace X] {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K: Final C F S)(s:StateIndex K)
set_option quotPrecheck false
local notation "T"=>state K s

abbrev roles (S:Table C.book)(d:V→ℕ):= ∀ i:V, Fin (Module.finrank ℂ (S.Field (d i)))
abbrev board (i:ℕ):=Module.finBasis ℂ (S.Field i) -- implicit
variable (d:V→ℕ)
def coord (v:(i:V)→S.Field (d i))(x:roles S d) : ℂ:=∏ i:V,(board (S:=S) _).coord (x i) (v i)
def line (x:roles S d): V→S.Tag:=fun i=> ⟨d i,board _ (x i)⟩
lemma deck_congr (f:V→ E4)(v:(i:V)→S.Field (d i)): Congr K (assembly S f (fun i=>⟨d i,v i⟩)) (∑ x:roles S d, coord d v x • assembly S f (line (S:=S) d x)):=by
    let Y(i:V)(j:Fin (Module.finrank ℂ (S.Field (d i)))):= letter S (f i) ⟨d i,board _ j⟩
    let Z(i:V)(j:Fin (Module.finrank ℂ (S.Field (d i)))):= (board (S:=S) _).coord j (v i)
    have he(i): Congr K (∑ j,Z i j • Y i j) (letter S (f i) (⟨d i,v i⟩:S.Tag)):=by
        let p(j : Fin (Module.finrank ℂ (S.Field (d i)))):= board (S:=S) (d i) j; have hp:= combine_letter K (f i) (d i) p (Z i)
        rw [show ∑ j,Z i j • p j=v i from (board ..).sum_repr _] at hp; exact hp
    exact ((muls (S:=S) Y Z) ▸ ((Congr.product K Finset.univ (fun i _=> he i)).symm K))
lemma Inspect_cont {p:X→ V→ E4}{x:X}{v:X→(i:V)→S.Field (d i)}(hx:ContinuousAt p x)(h:Injective (p x))(hv:ContinuousAt v x):ContinuousAt (fun i=> poll S (state K s) (assembly S (p i) (fun j=> ⟨d j,v i j⟩))) x:=by
    simp_rw [ (deck_congr K d _ _).done K s,map_sum,map_smul]; apply tendsto_finsetSum; intro i _; refine (show ContinuousAt (fun s=>coord d (v s) i) x from ?_).smul (assembly_cont K s hx h (line d i))
    unfold coord; apply tendsto_finsetProd; intro j _; exact (board (S:=S) (d j)|>.coord (i j)).continuous_of_finiteDimensional.continuousAt.comp ((continuous_apply j).continuousAt.comp hv)

variable (x:E4)(A B:Spelling S)
variable {n:ℕ}
def written : Spelling S →ₗ[ℂ] Reader K where
   toFun p s _ y v:=poll S (state K s) (p* assembly S (fun i=>y i+x) v)
   map_add' a b := by funext s n y v; change poll _ _ _=_+_; rw [add_mul,map_add]
   map_smul' a b := by funext s n y v; change poll _ _ _=a•_; rw [smul_mul_assoc,map_smul]
lemma readout (h:Congr K A B): written K x A=written K x B:= funext fun i=> funext fun n=>funext fun y=>funext fun v=> h _ _
lemma read_letter (d:ℕ)(B:S.Field d){y:Points n}(he:Points.cons 0 y∈ conf _)(v:Fin n→S.Tag) : written K x (letter S x ⟨d,B⟩) s n y v=reading K s 0 y v d B:=by
   change poll S T (letter S x ⟨d,B⟩ * assembly S (fun i=>(Points.across x y) i) v) = _; rw [letter_head S x _ (Points.across x y) v,examines S _ (hierarchy K s).laws.toSymmetric]
   have hz:=across_cons x 0 y; rw [zero_add] at hz;
   rw [← hz,if_pos (Points.across_in x he),use_across K s he, reads_at]
end YM.Frontier6.Tale
