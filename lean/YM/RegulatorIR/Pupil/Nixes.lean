import YM.RegulatorIR.Pupil.Multi
import YM.Next.STATIONARY.Joint.OnShell

/-! Polar W1 and removing rank one. No first-order vertex estimate assumed.
Includes polarized relation for *higher* ranks with just one gradient leg.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{I:Type}{p e r j :ℕ}
section Line
variable {q:Edge Cover}

def lone (q:Edge Cover)(x:G.Color) : BEdge G:= fun i=> if i=q then x else 0
lemma gives_lone {x:G.Color}: GivesT (lone q x) := (Set.finite_singleton _).subset (fun i hi=> (show i=q from Classical.byContradiction fun h=> hi (by rw [lone, if_neg h])))
lemma lone_h (u:G.El)(x:G.Color) : vbadge u (lone q x)=lone q (G.adjoint u x):=by ext1 i;unfold lone vbadge; dsimp only;split <;> first|exact map_zero _|rfl

def singleR (x:G.ColorIndex) : G.Color:= WithLp.toLp 2 (fun y=> if y=x then (1:ℝ) else 0)
def pointA (x:Foot G): BEdge G:=lone x.1 (singleR x.2)
lemma one_point (x y:Foot G): hue (pointA x) y=if y=x then 1 else 0:=by
 unfold hue pointA lone singleR; split_ifs <;> first| rfl | (dsimp;split <;> first|contradiction|norm_num) | subst y
 all_goals try simp_all [Prod.ext_iff]
lemma authentic (T:Packet (Foot G) r)(x:Tuple (Foot G) r) : matchT T (pointA ∘ x)=T x:=by
 unfold matchT chargeT; simp_rw [comp_apply, one_point];rw [tsum_eq_single x]; simp
 intro b hb; rw [show (∏ i: Fin r, if b i=x i then (1:ℝ) else 0)=0 from ?_,mul_zero]
 obtain ⟨z,hz⟩:= Function.ne_iff.mp hb;exact Finset.prod_eq_zero (mem_univ z) (if_neg hz)
lemma pay_lone (T: Packet (Foot G) 1)(x:G.Color) (q:Edge Cover) : oblique T (lone q x)=∑ i:G.ColorIndex, x i*T (![ (q,i)]):=by
 let L(i:G.ColorIndex):Tuple (Foot G) 1:= ![(q,i)];let f(t:Tuple (Foot G) 1):=T t*hue (lone q x) (t 0)
 have he : Function.support f⊆ Set.range L:=by
    intro i h; let b:=i 0
    have hx:b.1=q:=by by_contra hp;apply h; unfold f hue lone;rw [if_neg hp]; simp
    exact ⟨b.2,funext (fun j => by fin_cases j;exact Prod.ext hx.symm rfl)⟩
 unfold oblique matchT chargeT; simp only [Fin.prod_univ_one];change ∑' t,f t= _
 rw [← (show Injective L from fun i j h=>congr_arg (fun x:Tuple (Foot G) 1=>(x 0).2) h).tsum_eq he,tsum_fintype]; refine sum_congr rfl fun i _=> ?_
 unfold f L;rw [mul_comm]; simp [hue,lone]
end Line
namespace WOne
variable {U:Orders (Foot G)}(H:W1 U p)(he:e≤p)
include H he
lemma removed_one (hh:G.Simple) : U e 1=0:=by
 let T:= U e 1
 have he'(x:G.Color)(q: Edge Cover) : oblique T (lone q x)=0:=by
    let v:G.ColorIndex→ℝ:=fun i=>T ![(q,i)]
    let f:=∑ i:G.ColorIndex,v i • (PiLp.proj 2 (fun _:G.ColorIndex=> ℝ) i : G.Color →L[ℝ] ℝ)
    have hh'(x:G.Color):f x=oblique T (lone q x):=by unfold f; rw [_root_.sum_apply,pay_lone]; refine Finset.sum_congr rfl (fun i _=>mul_comm ..)
    have hP:f=0:= Stationary.color_fixed hh f (fun i j=> by rw [hh', hh', ← lone_h]; exact fares H he (by omega) _ gives_lone i)
    rw [← hh',hP];rfl
 ext1 i; rw [← authentic (U e 1) i]; let x:= i 0
 change matchT T _=_; rw [show pointA ∘ i=fun _=>lone x.1 (singleR x.2) from funext (fun j=> congr_arg pointA (congr_arg i (Subsingleton.elim j 0)))]; exact he' ..
variable (hv:IsSym (U e r))(A:Fin r→ BEdge G)(V:∀ i,GivesT (A i))(hr:r≤ e+2)

omit H he
private lemma beast_sum (u:Signed) (S:Finset (Fin r)): (beast u (∑ i∈ S,A i))=∑ i∈ S, beast u (A i):=by
 ext1 i;unfold beast; simp only [Finset.sum_apply]; split
 · exact (Finset.sum_neg_distrib _).symm
 rfl
private lemma vbadge_sum (u:G.El)(S:Finset (Fin r)): (vbadge u (∑ i∈ S,A i))=∑ i∈ S,vbadge u (A i):=by ext1 i;unfold vbadge; simp only [Finset.sum_apply,map_sum]

include H he hv hr V
lemma beast_match (u:Signed) : matchT (U e r) (beast u ∘ A)=matchT (U e r) A:=by
 apply mul_left_cancel₀ (show (r.factorial:ℝ)≠0 from by positivity)
 rw [← ritual _ hv (beast u ∘ A) (fun i=> gives_beast (V i)), ← ritual _ hv _ V];apply adjure_eq;intro s _;simp_rw [comp_apply]; rw [← beast_sum]; exact travels H he hr _ (sum_gives s A V) u
lemma vbadge_match (u:G.El) : matchT (U e r) (vbadge u ∘ A)=matchT (U e r) A:=by
 apply mul_left_cancel₀ (show (r.factorial:ℝ)≠0 from by positivity); rw [← ritual _ hv (vbadge u ∘ A) (fun i=> gives_vbadge (V i)), ←ritual _ hv _ V];apply adjure_eq;intro s _;simp_rw [comp_apply]; rw [← vbadge_sum]; exact fares H he hr _ (sum_gives s A V) u
variable (u:Fin r)(σ:Cover→G.Color)(hs:(Function.support σ).Finite)(h:A u=regalia σ)
include h hs
lemma gradient : (r.factorial:ℝ)*matchT (U e r) A= adjure (fun x=> -sweep U e r (∑ i∈ x,A i) σ) ((Finset.univ:Finset (Fin r)).erase u):=by
 rw [← ritual _ hv _ V, remove (v:=u) _ _ (mem_univ _)];apply adjure_eq;intro x hx
 have hz : u∉ x := fun hu=> notMem_erase u univ ((mem_powerset.mp hx) hu); rw [sum_insert hz,h,add_comm,supps H he hr _ (sum_gives x A V) _ hs]; abel -- lambda beta
omit hv hr V h hs
lemma b_pole (hh:G.Simple)(σ:Cover→ G.Color)(hs:(Function.support σ).Finite) (A:Fin 2→ BEdge G)(V:∀ i,GivesT (A i))(hv:IsSym (U e 2))(h:A 1=regalia σ): matchT (U e 2) A=0:=by
 apply eq_zero_of_ne_zero_of_mul_left_eq_zero (show ((2:ℕ).factorial:ℝ)≠0 from by positivity) -- name
 rw [gradient H he hv _ V (by omega) 1 σ hs h]; unfold adjure; apply sum_eq_zero;intro i _; dsimp only; rw [show sweep U e 2 _ σ=0 from ?_]; ring
 unfold sweep; apply sum_eq_zero; intro j hj; apply sum_eq_zero; intro k h; split
 next h=>
    obtain ⟨hz,hb⟩:=mem_erase.mp hj; have hx:=mem_antidiagonal.mp hb
    have hh':0 < j.2:=by by_contra! hh;apply hz;exact Prod.ext (by change j.1=e;omega) (by change j.2=0;omega)
    have hf:k≤1:=by omega
    interval_cases k
    · simp [rhyme,pip, hh'.ne']
    rw [removed_one H (show j.1≤p by omega) hh]; simp [rhyme]
 rfl
end WOne
end YM.RegulatorIR.Pupil
