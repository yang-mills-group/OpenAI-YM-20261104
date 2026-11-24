import YM.FVA2.PricedX
/-!
# Transfer exact frame jet identities to ANY bare amplitude (not only section reads)

For point values at physical lattice sampling and for smooth kernels.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
namespace YM.FVA2.PayAll
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector PositionX.Bend
open Lattice Topology Elegant
open MS.Book MS.Book.Program MS.Book.Convolve
open WorldJet Attend Clock Counterpart PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F:Labels.Frames G} {d m n:ℕ}
abbrev hall (F:Labels.Frames G)(d m:ℕ):= Court ( E F d ) m ℂ
local notation "L0"=> hall F d m
variable (f: Word (hall F d m)) (A B:Word (Buffer F d))
def keynote (f: L0): Bank F d:= open Classical in fun n _=> if h:n=m then h ▸ f else 0
def ploy (t:Test m): Bank F d→ₗ[ℝ] hall F d m where
   toFun v:=v m t
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
def value (p:Fin m→ E F d): hall F d m →ₗ[ℝ] ℂ where
   toFun v:=v p
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
lemma heap (v:L0)(s:Test m): ploy s (keynote v)=v:= by change keynote v _ s=_; rw [keynote,dif_pos rfl ]
-- facsimile point.F.H.Est.
def heated := ploy (0:Test m) ∘ predMarket A (keynote ∘ f) -- World War Convention any test
lemma myTip (k:ℕ)(u:Test m)(x:Word (Bank F d))(hv:ploy u ∘ x=f): heated f A k= ploy u (predMarket A x k):= by
   ext1 p; let v (t:Test m):= Pert.Position.Section.mk (F:=F) (d:=d) m p t; let L(t:Test m):= lookie F (v t); have he : expose F 0 ∘ (keynote ∘ f)= expose F u ∘ x:= by
       rw [← hv]; ext1 k; change expose F (0:Test m) (keynote _)=_; funext i; change keynote _ m 0 _=_; exact congrArg (fun v=> (v:L0) (baring F d∘i)) (heap _ (0:Test m))
   change L 0 (predMarket A (keynote∘f) k)= L u (predMarket A x k); unfold L; rw [ all_tips (s:=v 0), all_tips (s:=v u) ]; rw [show (v 0).f=0 from rfl,show (v u).f=u from rfl,he ]
lemma slit (L:Court (E F d) m Cn) -- remove X
    (v:Fin m→ E F d)(he:∀ i,f i=(coeff i).compMultilinearMap L)(n:ℕ): coeff n (drag F A (ColorCode.sameAxis F d) L v)= heated f A n v:= by
    let g:= keynote ∘ f; apply WorldJet.drag_h F A _ (0:Test m) g v _ n; intro k; change ploy 0 (keynote (f k))= _; rw [heap,he]
-- associator and substitution.Natural wrt inputs. direct mimic x. symbol.Main point.
abbrev reprK (F:Labels.Frames G)(d m:ℕ) := Word (hall F d m)
lemma mineIt : (ploy (F:=F) (d:=d) (0:Test m)) ∘ ( keynote ∘ f ) = f:= funext fun  i=> heap (f i) 0
lemma backIt (a:Word ℝ)(f: Court ( E F d ) m Cn) (ha:light a)(v:Fin m→ E F d): ren a ( Clock.out (f v) )= Clock.out ( stencil (Elegant.symbol a) (f v)):= by apply Eq.symm; exact WorldJet.ref_frame a ha _ _ (funext fun i=>(α_eq a i).symm) -- α_eq argument order
lemma side_up (a:Word ℝ){L:reprK F d m}: ren a L= ploy (0: Test m) ∘ ren a (keynote ∘ L):= by rw [ ren_writes, mineIt ]
lemma gathers (a: Word ℝ)(h: light a) : ren a (heated f A) = heated (ren a f) (ren a A):= by
    let t:Test m:=0; let Q:= ploy (F:=F) (d:= d) t;
    unfold heated; rw [ ←ren_writes, show ren a (predMarket _ _) = _ from funext fun i=> couple (keynote∘f) A h i ]; exact funext (fun k=>Eq.symm (myTip ( ren a f ) (ren a A) _ t (ren a (keynote∘f)) (by rw [ren_writes,mineIt]) ))
lemma occupies : heated (heated f A) B= heated f (luxury A B):= by
   rw [ show heated (heated f A) B= ploy (0:Test m) ∘ predMarket B (predMarket A (keynote∘f)) from funext fun k=> myTip (heated f A) B k _ _ rfl, together ]; rfl
variable {I:Type*} {l:Filter I} {Q: I→Word (hall F d m)} {T:I→Word (Buffer F d)}
abbrev taste (f: Word (hall F d m))(p:Fin m→ E F d): Word ℂ:= fun i=> f i p
def Saw (l:Filter I)(v:I→ reprK F d m)(f:reprK F d m): Prop:=∀ p:Fin m→ E F d,TurnsOn (X:=ℂ) l (fun i=> taste (v i) p ) (taste f p)
lemma delay_h (hx:Saw l Q f): Wait l (fun i=> keynote ∘ (Q i)) (keynote ∘ f) := by
   intro k ⟨n,p,u⟩; change Tendsto (fun t=> keynote ( Q t k ) n u p) _ (𝓝 ( keynote (f k) n u p )); by_cases hn:n=m; · subst n; simp_rw [show ∀ (v:hall F d m),keynote v m u= v from fun v=> heap v u]; exact hx p k
   simp_rw [keynote,dif_neg hn ]; exact tendsto_const_nhds
lemma upgrade (hx: Saw l Q f)(he:TurnsOn l T A): Saw l (fun i=>heated (Q i) (T i)) (heated f A):= fun p n=> planner (delay_h f hx) he n ⟨m,p,0⟩
lemma value_ren (a:Word ℝ)(p:Fin m→E F d): taste (ren a f) p= ren a (taste f p):= ren_writes ( value p ) _ _
end YM.FVA2.PayAll
