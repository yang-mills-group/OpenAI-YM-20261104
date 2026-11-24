import YM.Frontier6.Exact.Centre

/-! Changing exterior labels in a finite basis. Data-use format for compact
rotational detector families. Also for continuity of the extracted product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(s:StateIndex K) {n d:ℕ}
variable {X:Type*}

abbrev ScaleVec (S:Table C.book)(d:Caps n):= (i:Fin n)→ S.Field (d i)
def paint (S:Table C.book)(d:Caps n)(z:ScaleVec S d)(i:Fin n):S.Tag:= ⟨d i,z i⟩
def VMulti (S:Table C.book)(f:(Fin n→ S.Tag)→ℂ):Prop:=∀ d:Caps n, ∃ g:MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ,∀ z, g z = f (paint S d z)
lemma class_multi (x:Points n): VMulti S (fun v=> S.useAt (state K s) x v):= fun d => ⟨S.classMoment (state K s) d x, fun z=> rfl⟩
lemma VMulti.fixes {x:(Fin (n+1)→ S.Tag) → ℂ}(h:VMulti S x)(v:S.Tag):
   VMulti S (fun z=> x (Fin.cons v z)):=by
   intro d
   let q:Caps (n+1):= Fin.cons v.1 d
   obtain ⟨g,hg⟩:= h q; refine ⟨g.curryLeft v.2,fun z=>?_⟩
   let z' : (i:Fin (n+1))→ S.Field (q i):=Fin.cons (α:=fun i:Fin (n+1)=>S.Field (q i)) v.2 z
   change g z'=x _
   rw [hg]; congr 1; ext1 i; refine Fin.cases ?_ (fun j=> ?_) i
   · change (⟨v.1,v.2⟩:S.Tag)=v; rfl
   rfl
lemma VMulti.sub {x y:(Fin n→ S.Tag)→ℂ}(h:VMulti S x)(h':VMulti S y): VMulti S (fun z=> x z-y z):=by
   intro d; obtain ⟨g,hg⟩:= h d; obtain ⟨g',hg'⟩:= h' d; exact ⟨g-g',fun z=> congr_arg₂ (·-·) (hg z) (hg' z)⟩ -- syntax fix
lemma reading_multi (x:E4)(y:Points n)(z:S.Field d): VMulti S (fun v=> reading K s x y v d z):=by
   simp_rw [reads_at]; exact (class_multi K s (Points.cons x y)).fixes ⟨d,z⟩
lemma pair_multi {b:ℕ}(B:S.Field b)(D:S.Field d)(x:E4)(y:Points n): VMulti S (fun v=> pair K B D x s n y v):=by
   simp_rw [pair_at]; exact ((class_multi K s _).fixes ⟨d,D⟩).fixes ⟨b,B⟩

namespace VMulti
variable {d:Caps n} {f:(Fin n→ S.Tag)→ℂ}
abbrev number (S:Table C.book)(d:Caps n):=(i:Fin n)→ Fin (Module.finrank ℂ (S.Field (d i)))
abbrev bed (S:Table C.book)(d:Caps n)(i:Fin n):= Module.finBasis ℂ (S.Field (d i))
def factor (z:ScaleVec S d)(i:number S d):ℂ:=∏ a:Fin n, (bed S d a).coord (i a) (z a)
def choice (i:number S d) := paint S d (fun a=> bed S d a (i a))
lemma factors (h:VMulti S f)(z:ScaleVec S d): f (paint S d z) = ∑ i:number S d, factor z i * f (choice i):=by
   obtain ⟨g,hg⟩:= h d; unfold factor choice; simp_rw [←hg]; let t(i:Fin n)(p:Fin (Module.finrank ℂ (S.Field (d i)))):= bed S d i p
   let l(i:Fin n)(p:Fin (Module.finrank ℂ (S.Field (d i)))):= (bed S d i).coord p (z i)
   let v i j := l i j • t i j
   have he : z=fun i=>∑ j,v i j:=funext fun i=>((bed S d i).sum_repr _).symm
   nth_rw 1 [he,g.map_sum v]; exact Finset.sum_congr rfl fun i _=>g.map_smul_univ (fun a=>l a (i a)) (fun a=>t a (i a))
lemma factor_cont [TopologicalSpace X] (f:X→ ScaleVec S d)(hf:Continuous f)(i:number S d): Continuous (fun g=> factor (f g) i):=
   continuous_finsetProd _ fun j _=> ((bed S d j).coord (i j)).continuous_of_finiteDimensional.comp ((continuous_apply j).comp hf)
lemma chords [TopologicalSpace X] (f:X → (Fin n→ S.Tag) → ℂ){U:Set X}
    (hf:∀ x∈ U, VMulti S (f x))(ht:∀ v,ContinuousOn (fun x=> f x v) U)(g:X→ ScaleVec S d)(hg:Continuous g):
    ContinuousOn (fun x=> f x (paint S d (g x))) U:=(continuousOn_finsetSum _ fun i _=> ((factor_cont g hg i).continuousOn).mul (ht (choice i))) |>.congr (fun x hx=> (hf x hx).factors (g x))
end VMulti

lemma spin_point (x:E4) : Continuous (fun u:Ortho=> Ortho.move u x):= by
   refine (PiLp.continuous_toLp ..).comp (continuous_pi fun i=>?_)
   -- shape
   change Continuous (fun u:Ortho => Ortho.move u x i); simp_rw [Ortho.move, M4.at_coord]
   exact continuous_finsetSum _ (fun j _=> (show Continuous (fun s:Ortho=>s.val i j) from (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)).mul continuous_const)
lemma spinner (x:Points n): Continuous (fun u:Ortho=> Points.move u x):=by
   unfold Points.move points; exact (PiLp.continuous_toLp ..).comp (continuous_pi fun i=> spin_point _)
variable (p:Probe S)
def flying (u:Ortho) (i:Fin p.length) : S.Field (p.letter i).1:= K.sector.turns.act _ u (p.letter i).2
lemma fly_paint (u:Ortho): (p.roll K u).letter= paint S (fun i=>(p.letter i).1) (flying K p u):= rfl
lemma fly_cont : Continuous (flying K p):= continuous_pi fun i=> K.phase.transport.spots.spin _ _
end YM.Frontier6
