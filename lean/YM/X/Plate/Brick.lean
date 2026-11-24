import YM.X.Plate.Test
import YM.X.Gravity.Ginger
/-!
# local thermal value to commute cover shifts. ALL powers unscaled in warm except `e^(-d)`. later subtract unselected Gram CT. Degree rank for mature + rest. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Plate
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Shelf
open Ocean Clove Fielding Haze Gravity Bare Crystal
open Stems hiding X
open scoped Topology ContDiff Classical BigOperators
variable {V W I:Type*} {k m n:ℕ}{G:Gauge}
variable {q:ℕ+} {R r:ℝ}
abbrev LoomA (G:Gauge):=ℕ→ Curly G
variable (P:Word G)(χ: Floor R) {F:Labels.Frames G}(s:Shop F)
def hollow (q:ℕ+)(P:Word G)(χ:Floor R)(i:ℕ): Curly G:= fireMask (Floor.maskL q χ i)
def glint (q:ℕ+)(P:Word G)(χ:Floor R)(i:ℕ): Curly G:= (epsilon q i)^(-(P.d:ℤ)) • (load q P i*hollow q P χ i + hit (flow G (side q i)) (load q P i) (hollow q P χ i))
def warm (q:ℕ+)(s:Shop F)(P:Word G)(χ: Floor R) (i:ℕ): Curly G:= mature q s P χ i - glint q P χ i
set_option maxHeartbeats 600000 in
lemma warmed (p:ℕ+) (i:ℕ): warm p s P χ i=(epsilon p i)^(-(P.d:ℤ)) • (milk (flow G (side p i)) (bookMark P 1) -matchP s p i P.d (Gravity.billet (q:=p) s P χ i)-knot (flow G (side p i)) (load p P i) (hollow p P χ i)):= by
   let v:=flow G (side p i); let r:=load p P i; let F:=hollow p P χ i; unfold warm;
   rw [mature,glint,←smul_sub]; apply congr_arg (fun x:Curly G=>(epsilon p i)^(-(P.d:ℤ)) • x); unfold warp crisp; change (milk v _ - multi v r F -_)-(r*F+hit v r F)= _; rw [m_op v r F]; abel
-- degree at most msup along var q
local notation "Q"=> flow G
def Wide {V:Type*}(p:ℕ→poly V):Prop:= ∃ d:ℕ,∀ i,duty (p i) d
namespace Wide
variable {f g:ℕ→poly V}
lemma constant (p:poly V): Wide (fun _=> p):=⟨p.totalDegree,fun _=> le_rfl⟩
lemma plus (h:Wide f)(hp:Wide g): Wide (f+g):=by obtain ⟨d,h⟩:=h; obtain ⟨k,hp⟩:=hp; exact ⟨max d k,fun i=>(duty.add ((h i).more (by simp)) ((hp i).more (by simp)))⟩
lemma sub (h:Wide f)(hp:Wide g):Wide (f-g):=by obtain ⟨d,h⟩:=h;obtain ⟨k,hp⟩:=hp;exact ⟨max d k,fun i=>duty.subs ((h i).more (by simp)) ((hp i).more (by simp))⟩
lemma costs (a:ℕ→ℂ)(h:Wide f): Wide (fun i=> a i • f i):= by obtain ⟨d,h⟩:=h;exact ⟨d,fun i=> (h i).scalar _⟩
lemma fin {f:I→ℕ→poly V} (l:Finset I)(h:∀ i∈l,Wide (f i)): Wide (∑ i∈l,f i) := by induction l using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact constant _ | insert i l h' ih=> rw [Finset.sum_insert h'];exact (h i (by simp)).plus (ih (fun j hj=> h j (by simp [hj])))
lemma heated (L:ℕ→Symmetric V)(h:Wide f):Wide (fun i=> milk (L i) (f i)):= by obtain ⟨d,h⟩:=h; exact ⟨d,fun i=> (h i).milk_p _⟩
lemma xhit (L:ℕ→Symmetric V)(h:Wide f)(hp:Wide g):Wide (fun i=> hit (L i) (f i) (g i)):= by obtain ⟨d,h⟩:=h; obtain ⟨c,hc⟩:=hp; exact ⟨d+c,fun i=> (h i).hit_p (L i) (hc i)⟩
lemma knotted (L:ℕ→Symmetric V)(h:Wide f)(hp:Wide g):Wide (fun i=> knot (L i) (f i) (g i)):=by obtain ⟨c,hc⟩:=hp; obtain ⟨d,h⟩:=h; exact ⟨d+c,fun i=> (h i).knot_p (L i) (hc i)⟩
lemma port [AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W](L: W→ₗ[ℂ] poly V)(f:ℕ→ W): Wide (L ∘ f):= by
    let b:= Module.finBasis ℂ W; let I:= Fin (Module.finrank ℂ W); rw [show ⇑L ∘ f=∑ i:I,(fun k=>b.coord i (f k) • L (b i)) from ?_]; exact fin _ (fun i _=>Wide.costs _ (constant _))
    ext1 k; rw [Finset.sum_apply,comp_apply]; simp only [← map_smul,← map_sum]; exact congr_arg _ ((b.sum_repr (f k)).symm)
lemma hearth (q:ℕ+) : Wide (hollow q P χ) := by
    let a:= Finset.univ.sup (fun i:PlaqAxes=> (vertex i :Curly G).totalDegree); have hc (i:PlaqAxes)(z:Cover): duty (flashVertex (G:=G) (z,i)) a:= by rw [dress_fire]; exact le_trans (totalDegree_rename_le ..) (Finset.le_sup (f:=fun i:PlaqAxes=> (vertex i :Curly G).totalDegree) (Finset.mem_univ i))
    refine ⟨a,fun i=> ?_⟩; let s:= Floor.maskL q χ i; unfold hollow fireMask beadR; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum]; apply duty.costs; intro z _; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact (duty.costs _ (fun i _=> hc i z)).scalar _
lemma compD (q:ℕ+)(f:ℕ→Pert.Position.E F n) : Wide (fun i=> matchP s q i n (f i)):= heated (f:= (raw s n 0).comp (Pert.RawLabels.physicalLabel F n) ∘ f) _ (port _ f)
lemma sense (q:ℕ+):Wide (warm q s P χ):= by
   let t:=fun i=>flow G (side q i); rw [funext (fun i=> warmed P χ s q i)] -- rw lambdas
   simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact Wide.costs _ (((Wide.heated t (Wide.constant _)).sub (compD s q _)).sub (Wide.knotted t (Wide.heated t (Wide.constant (bookMark P 0))) (hearth P χ q)))
end Wide
end YM.PositionX.Plate
