import YM.RG11Proof.Fields.Winding
import YM.RG11Proof.Arrow.Start
import YM.RG11Proof.Scale.Reverse
import YM.RG11Proof.Travel.Cohere
import YM.RG11Proof.Stress.Anchor

/-!
# Physical-E coefficient protocol, compatible d<6 restrictions included

Names distinct from physical Construction, Sectored etc. All comparisons here
generate *formal* transports in reporting frames only, at separated points
and independent prescriptions. Provable under those assemblies + bridges.
Quantified types also in logs. α is cutoff index etc e.g. along UV/IR
common choices; instantiate Bridge/Step rates at every horizon BEFORE taking
formal consistency, not them asserted from this container.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Window
open PowerSeries YM.RG11.Jets YM.RG11.Scale YM.RG11.Travel
open scoped BigOperators Classical ContDiff
open Labels YM.RG11.Fields YM.PertExtension.Position Horizon Pert.Triangle

variable {G:Gauge}(F:Frames G)
abbrev J (n:ℕ):=(tower F n).toBasis.J
abbrev L (n:ℕ):=(tower F n).toBasis.guard
abbrev grade (n:ℕ):J F n→ℕ:=Fields.height (tower F n)
abbrev SquareAt(d:ℕ):=Square (J F d) (PowerSeries ℝ)
variable {F}

-- from pre-shapes after adjustment and all independent targets supplied.
structure AxisData (A:ShapeReport G F) where
   β:PowerSeries ℝ
   b (d:ℕ): SquareAt F d
   pulls(d:ℕ)(hd:6≤d):∀ N,Shows A (tower F d) N β (b d)
   stay {i j:ℕ}(h:i≤j): Held (rise F h) (b j) -- optional? use vertical at j>=6
   coheres {i j:ℕ}(h:i≤j): Horizon.take (rise F h) (b j)=b i

 theorem slice_again (A:ShapeReport G F){d e:ℕ}(h:d≤e):slice (rise F h) (A.realAt (tower F e).toBasis)=A.realAt (tower F d).toBasis:=by
   funext v; ext1 i; simp only [slice,ShapeReport.realAt,view,coeff_mk]
   rw [show (fun i=> _)= (Fields.up F h ∘ (fun j=> (tower F d).b (v.2 j))) from funext fun i=>basis_rise F h (v.2 i)]
   apply congrArg Complex.re (A.packs d e v.1.order i h v.1.test _).symm

-- generic one-horizon compatibility on BASE of constraints + b. Don't
-- hide the `take` as if dimensions independently selected.
def agrees (p : PowerSeries ℝ){i:ℕ}(X:SquareAt F i)(A B:ShapeReport G F):Prop:=
    B.realAt (tower F i).toBasis= Change.act ⟨p,X⟩ (A.realAt (tower F i).toBasis)

 theorem takes {p:PowerSeries ℝ}{i j:ℕ}(h:i≤j){X:SquareAt F j}(ha: (L F j).Lawful X){A B:ShapeReport G F}(ho: agrees p X A B):
    agrees p (Horizon.take (rise F h) X) A B:=by
  rw [agrees, ←slice_again A h,←slice_again B h,ho]
  exact slice_action _ ((basis_rise F h).coherent.allHeld (rise F h) (by convert! ha))

 theorem takes_grade {i j:ℕ}(h:i≤j){S:SquareAt F j}(hs:graded (grade F j) S):graded (grade F i) (Horizon.take (rise F h) S):=by
   intro a b he
   have ht (a): grade F j (rise F h a)=grade F i a:=congrArg Prod.fst ((basis_rise F h).weights a)
   exact @hs _ _ (by rw [ht,ht]; exact he)

 theorem holds {i j:ℕ}(h:i≤j){X:SquareAt F j}(he:(L F j).Lawful X): Held (rise F h) X:= (basis_rise F h).coherent.allHeld (rise F h) (by convert! he)
 theorem lawT {i j:ℕ}(h:i≤j){p:PowerSeries ℝ}{X:SquareAt F j}(he:Change.Good (L F j) ⟨p,X⟩):Change.Good (L F i) ⟨p,Horizon.take (rise F h) X⟩:=by
   have hu:= Coherent.good (rise F h) ((basis_rise F h).coherent) he
   exact hu

structure Direction (A:ShapeReport G F)(S:AxisData A)(B:ShapeReport G F)(M:AxisData B)
    (p:PowerSeries ℝ)(X:∀ i,SquareAt F i):Prop where
   legal (i): Change.Good (L F i) ⟨p,X i⟩
   travels {i j:ℕ}(h:i≤j): Horizon.take (rise F h) (X j)=X i
   match_all(i):agrees p (X i) A B
   graded_X(i):graded (grade F i) (X i)
   beta : M.β*derivative ℝ p=PowerSeries.subst p S.β
   gamma(i): M.β • flash (X i)=M.b i*X i-X i*subs p (S.b i)

-- construct Direction via large h, engineering restrict estimates
 theorem gamma_lesser (A:ShapeReport G F)(S:AxisData A)(B:ShapeReport G F)(M:AxisData B){p:PowerSeries ℝ}{i j:ℕ}(h:i≤j){X:SquareAt F j}(he:(L F j).Lawful X)(hq:M.β • flash X=M.b j*X - X*subs p (S.b j)) :
    let z:=Horizon.take (rise F h) X
    M.β • flash z=M.b i*z-z*subs p (S.b i):=by
   have hu:=congrArg (Horizon.take (rise F h)) hq
   let u:=rise F h
   have hs (x y:SquareAt F j): Horizon.take u (x-y)=Horizon.take u x-Horizon.take u y:=rfl
   change Horizon.take u _=Horizon.take u _ at hu
   rw [hs,take_mul (rise F h) (M.stay h), M.coheres h,take_mul (rise F h) (holds h he),take_subs,S.coheres h] at hu
   exact hu

variable (A B:ShapeReport G F)(T:AxisData A)(Z:AxisData B)

private def expanded (X : ∀ i,SquareAt F (6+i)) (i:ℕ):SquareAt F i:=Horizon.take (rise F (Nat.le_add_left i 6)) (X i)

 theorem full_system (hG:G.Simple)(ha:A.table 1 6 3 profileChoice (basic F)=cTest G){α:Type*}(hw:Bridge.High (A.mesh B) α):
    ∃ (t f:PowerSeries ℝ) (X M : ∀i, SquareAt F i), PowerSeries.subst t f=PowerSeries.X ∧ PowerSeries.subst f t= PowerSeries.X ∧
      Direction A T B Z t M ∧ Direction B Z A T f X ∧ ∀i,M i*subs t (X i)=1 ∧ X i*subs f (M i)=1:=by
  obtain ⟨t,f,N,m,_hc,hp,hp',hr,ht⟩:= A.consistent B hG ha (fun i _=>Rigidity.Ice.polar_rank F hG i) hw
  have hh(i):= engineering_all A B (d:=6+i) (by omega) (tower F (6+i)) hG ha ⟨t,m i⟩ (hr i).2.1.field (hr i).2.1.ruler.base (Eq.symm (hr i).2.2.2.2.1) (T.pulls (6+i) (by omega)) (Z.pulls (6+i) (by omega))
  -- can use Sees transfer for reverse; exact through n chosen max 1 n.
  have hY(i:ℕ): graded (grade F (6+i)) (N i) ∧ T.β*derivative ℝ f = PowerSeries.subst f Z.β ∧
        T.β • flash (N i) = T.b (6+i)*N i - N i*subs f (Z.b (6+i)):=by
    obtain ⟨hL,hT,hV,_,hA,hB⟩:= hr i
    let V:= (tower F (6+i)).toBasis
    let c:Change ℝ V.J:=⟨f,N i⟩
    have hx:graded (grade F (6+i)) (subs f (m i)):=graded.Law_subs (A:=m i) (w:=grade F (6+i)) (fun e=> (hh i).1 e) (by convert! hT.field.baseline) hL.ruler.base
    have hz:graded (grade F (6+i)) (N i):=by
       rw [left_inv_eq_right_inv hV (mul_squareInv (nearId.subs hL.ruler.base hT.field.baseline))]
       intro a b h
       convert! graded.Law_inv (A:=subs f (m i)) (w:=grade F (6+i)) (fun e=>hx e) (by convert! (hT.field.baseline.subs hL.ruler.base)) h using 1
    refine ⟨fun h=>hz h,?_⟩
    have hE:Sees V.guard (A.realAt V):= (A.ticket hG ha (by omega) V (Rigidity.Ice.polar_rank F hG (6+i))).sees
    have hF:Sees V.guard (B.realAt V):=Scale.mark_to_mark (p:={g:=t,Z:=m i}) (by convert! hT) (fun v=> by rw [←hA]; exact Through.refl _) hE
    have hQ(k:ℕ):=transports c (by convert! hL.field) hL.ruler.base (w:=grade F (6+i)) (fun e=>hz e) scalesX hF
       (by rw [← hB]; exact fun _=>Through.refl _)
       (Z.pulls (6+i) (by omega) k).cs (T.pulls (6+i) (by omega) k).cs (by unfold Anchored; rw [←coeff_zero_eq_constantCoeff_apply,(T.pulls (6+i) (by omega) k).free_beta 0 (by decide)])
       (Z.pulls (6+i) (by omega) k).valid (T.pulls _ (by omega) k).valid
    exact ⟨PowerSeries.ext (fun j=>(hQ j).1 _ le_rfl),Matrix.ext fun j l=>PowerSeries.ext (fun n=> (hQ n).2 _ _ _ le_rfl)⟩
  -- lower join
  have he (X:∀ i,SquareAt F (6+i))(h:∀ {i j:ℕ}(hn:i≤j),Horizon.take (rise F (Nat.add_le_add_left hn 6)) (X j)=X i){i j:ℕ}(hn:i≤j):
      Horizon.take (rise F hn) (expanded X j)=expanded X i:=by
    unfold expanded; rw [Horizon.take_take,rises_stack]
    rw [←h hn,Horizon.take_take,rises_stack]
  refine ⟨t,f,expanded N,expanded m,hp',hp,⟨fun i=>lawT _ (hr i).2.1,fun h=>he _ (fun h=>(ht h).1) h,
     fun i=>takes _ (hr i).2.1.field (hr i).2.2.2.2.1,
     fun _ {_ _} e=> takes_grade _ (fun ht=>(hh _).1 ht) e,(hh 0).2.1,
     fun i=>gamma_lesser A T B Z _ (hr i).2.1.field (hh i).2.2⟩,⟨fun i=>lawT _ (hr i).1,fun h=> he _ (fun h=>(ht h).2) h,
     fun i=>takes _ (hr i).1.field (hr i).2.2.2.2.2,fun _ {_ _} e=>takes_grade _ (fun ht=>(hY _).1 ht) e,(hY 0).2.1,
     fun i=> gamma_lesser B Z A T _ (hr i).1.field (hY i).2.2⟩,fun i=>?_⟩
  unfold expanded; rw [←take_subs,←take_subs]
  rw [←take_mul (rise F _) (holds _ (hr i).2.1.field),←take_mul (rise F _) (holds _ (hr i).1.field), (hr i).2.2.2.1,(hr i).2.2.1,take_one]; simp
end YM.RG11.Window
