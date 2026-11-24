import YM.MS.Echo.Skein
/-!
# The no-weight Ward comparison on the stencil overlap-noncollision ideal. Uniform evenness

Keep coupling variable of the quantum truth *evaluated by coefficients*, not e.g. inserting a
series over whole order. When truncating accuracy n only states equality up to that order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Fleet
open scoped Topology ContDiff Interval
variable {I W K:Type}[LinearOrder W] {G:Gauge}{n:ℕ}{p:Team}{y:ℝ}
    {u v: ℤ}{F H X Y:NatK G}{s t:Finset Cover}{Z V:Actor G}
local notation "B"=> Spectrum G
local notation "sG"=> style G p y
local notation "Θ"=> DotFlip (G:=G)
set_option quotPrecheck false
local infixl:70 " ⋄ "=> (native G).core
lemma shifted_o (h: NoWeight n F X)(p:Cover): NoWeight n (promote ( Lab.Shift p ) F) X:= by intro i hi; rw [← shiftX, promised, h i hi,map_zero]
def similar (F H:NatK G)(n:ℕ): Prop:= ∀ i≤ n,F i=H i
lemma keeps_o {i:ℕ}(h: similar F H n)(hx:i≤n): ( X ⋄ F ) i=( X ⋄ H ) i ∧ ( F ⋄ X ) i=( H ⋄ X ) i:= by unfold native Actors.stack; dsimp only; simp_rw [loan]; exact ⟨ Finset.sum_congr rfl fun j hj=> congr_arg _ (h j.2 (by obtain he:= mem_antidiagonal.mp hj; omega)), Finset.sum_congr rfl fun j hj=> by rw [ h j.1 (by obtain he:=mem_antidiagonal.mp hj; omega) ] ⟩ -- sdependent binds i. add
lemma e_part (x:ℂ): (B).Lap (piece x:Dot G Cover)=0:= by
   rw [ Bonded.lap_at ]; refine Finset.sum_eq_zero fun i hi=>?_ ; have he:Pieces ( piece x:Dot G Cover) ∅:= fun i a hx hy=> by cases i; cases hx; rfl
   rw [heart_by _ _ _ he,Finset.sum_empty,smul_zero]
lemma e_contact (F:Dot G Cover)(x:ℂ): (B).touch F (piece x)=0:= by
   rw [ Bonded.touching ]; apply Finset.sum_eq_zero; intro i hi; have he:Pieces (piece x:Dot G Cover) ∅:= fun i a hx hy=> by cases i; cases hx; rfl
   rw [root_at _ _ _ _ he, Finset.sum_empty,smul_zero]
lemma unitW (n:ℕ): NoWeight n ( native G ).unit F:= by
   intro i he; let P: NatK G:= ( native G ).unit; change (B).Lap ( P i ) + (∑ j∈antidiagonal i,(B).touch ( F j.1 ) ( P j.2 ))=_; have he(i): P i=if i=0 then piece 1 else 0:= by by_cases h:i=0 <;> simp only [h,↓reduceIte]; exacts [ native_home .., native_aw h ] -- issue h i explicit IH.
   simp_rw [ he ]; rw [ Finset.sum_eq_zero (fun j hj=>?_ ) ]; simp only [add_zero]; split <;> first | exact e_part 1| exact map_zero _
   split <;> first| exact e_contact ..| exact map_zero _ -- likely indentation
lemma moveLeib (hf:∀ i,Tuned (F i) 0)(hp:stamped n F s)(hv:stamped n H t)(hd:Disjoint s t)(h:NoWeight n F sG): similar ( steadyE B sG ( F ⋄ H ) ) ( F ⋄ steadyE B sG H ) n := by
   intro i hi; rw [LapLeib hf (fun j hj=> hp j (hj.trans hi)) (fun j hj=> hv j (hj.trans hi)) hd, Pi.add_apply, (keeps_o (X:=H) ( show similar ( steadyE B sG F ) 0 n from h ) hi).2,map_zero,LinearMap.zero_apply,Pi.zero_apply,zero_add]
lemma joined (hf:∀ i,Tuned (F i) 0)(hp:stamped n F s)(hv:stamped n H t)(hd:Disjoint s t)(h:NoWeight n F sG)(hu:NoWeight n H sG): NoWeight n ( F ⋄ H ) sG:= by intro i hi; rw [ moveLeib hf hp hv hd h i hi, ( keeps_o (X:=F) (show similar ( steadyE B sG H ) 0 n from hu) hi ).1, map_zero ]; rfl
variable {U: W→ Actor G}{R:Finset W}{L:W→ Finset Cover}{z:W→Cover}{c:Berth ( I:=I ) ( W:= W )}{l:Filter I}
structure ReadyP (p:Team)(U:W→ Actor G): Prop where
   badge: Badge U
   shine i y: Weightless (Spectrum G) (style G p y) ( U i y )
lemma pieceW {w:W}(H:ReadyP p U): NoWeight n ( wordsX z U {w} y ) sG:= by
    rw [word_m]; refine shifted_o ( fun i _=> congr_fun ( H.shine w y ) i ) _ -- ?w
lemma eventual_M (h:Sparse l c)(H:ReadyP p U)(s:Finset W)(n:ℕ): ∀ᶠ i in l,∀ y:ℝ, NoWeight n ( Memo (starP c i) U s y ) (style G p y):= by
    choose L hL using fun w:W=> packets (H.badge w) n; let V(i:I):= starP c i; induction s using Finset.induction with
    | empty=> refine Eventually.of_forall fun i y=>?_ ; rw [memo_at]; exact unitW n
    | insert i r hp ih=>
        filter_upwards [growD (L:=L) (t:=L i) h hp, ih] with t hV hx y; rw [memorep ( V t ) H.badge hp]; -- notation mismatch
        exact joined (fun j=> (wordwell (V t) H.badge {i}).actual j y) ( ( by rw [word_m]; exact stamp_job ( hL i y ) _ ): stamped n (wordsX ( V t ) U {i} y) ( pushS ( L i ) ( V t i ) ) ) (stamp_M H.badge hL y) hV ( pieceW H ) (hx y)
-- memo coefficients equal under arbitrary changes to other slots
lemma mergeNe {f g:W→Actor G}(hf:Badge f)(hg:Badge g)(H:∀ i∈ R, f i=g i) (z:W→Cover): Memo z f R=Memo z g R:= by
    induction R using Finset.induction with| empty=> rw [memo_at,memo_at]| insert i r he ih=> rw [ memorep z hf he,memorep z hg he,ih (fun i hi=> H i ( Finset.mem_insert_of_mem hi )) ]; exact funext fun x=> congr_arg (fun v=>(native G).core v (Memo z g r x)) (Eq.trans (word_m ..) ( by rw [H i (by simp),word_m]))
end YM.MS.Echo
