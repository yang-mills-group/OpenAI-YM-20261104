import YM.MS.Fleet.Shipped
/-!
Pack grows uniformly through all required k truncation before comparison. Aggregate can be used
in absolute flow only for *fixed offsets*, bounded then; not contrasting merged estimates against
the original UV moving horizon! This proof works for odd inputs on a factor too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Puff.Mom
open scoped Topology ContDiff Interval
variable {I W:Type} [LinearOrder W] {G:Gauge} {h k:ℤ}{F H:Actor G}{b:Bool}{U: W→ Actor G}
lemma blank_c (G:Gauge)(h:ℤ): Circle G 0 false h:= by refine ⟨fun _ _=> Tune.zero, fun _=> ⟨0,fun _ _ _=>rfl⟩, fun _ _ _=>map_zero _,fun _=> Ready.zero,fun _ _ hv =>Bool.noConfusion hv⟩
lemma shift_c (X:Cover)(hF:Circle G F b h): Circle G (fun x:ℝ=>promote (Lab.Shift X) (F x)) false h:= by
   refine ⟨ fun i x=> (hF.actual i x).move (fun t=>X+t),fun i=>?_,fun i x z=> ?_,fun i=>(hF.tag i).linear (( Lab.Shift X (A:=Branch G Axis) ( R:=ℂ) ).restrictScalars ℝ), fun _ _ hv=>Bool.noConfusion hv⟩;
   · obtain ⟨V,hV⟩:= hF.room i; exact ⟨V,fun x=> Limit.shades _ (hV x) _ ⟩
   rw [promised]; unfold Lab.Shift; rw [ ← painting, hF.settled ]
def plainX (G:Gauge)(p: Angled (Dot G Cover)): Dot G Cover→ₗ[ℝ] Dot G Cover→ₗ[ℝ] Dot G Cover:= {
   toFun x:= (p x).restrictScalars ℝ
   map_add' x y:= LinearMap.ext (fun z=> by simp)
   map_smul' c x:= by apply LinearMap.ext; intro y; change p (c • x) y=c • p x y; rw [ show c • x=(c:ℂ) • x from rfl,map_smul,LinearMap.smul_apply ]; rfl }
lemma pair_c (hF:Circle G F false h)(hH:Circle G H false k): Circle G (fun i=> (native G).core (F i) ( H i)) false (h+k):= by
   let Z (n:ℕ):=antidiagonal n; refine ⟨fun i x=> Tune.sum ( Z i ) fun j _=> (hF.actual j.1 x).pair ( hH.actual j.2 x ),fun i=>?_,fun i x=> Colorless.csum _ (fun j _=> ( hF.settled j.1 x ).couple ( hH.settled j.2 x )), fun n=> value_sum (Z n) (fun i _=> Ready.pair (plainX G (couple DotFlip)) (hF.tag i.1) ( hH.tag i.2 )), fun _ _ hv=>Bool.noConfusion hv ⟩
   choose a ha using hF.room; choose v hv using hH.room; let m (j:ℕ×ℕ):=a j.1+v j.2; refine ⟨( Z i ).sup m,fun t=>?_⟩; change Limit ( (∑ j∈ Z i,couple DotFlip ( F t j.1 ) ( H t j.2 )):Dot G Cover ).val _; rw [sum_stack]; apply Limit.sum; intro j hj; obtain hP:m j ≤( Z i ).sup m := Finset.le_sup (f:=m) hj; refine Limit.up ( ( ha j.1 t ).pair ( hv j.2 t ) ) ?_; unfold m at *; omega -- defeq a vs Natcast pi
lemma unitTune (G:Gauge): Tuned (piece 1:Dot G Cover) 0:= by
    refine ⟨ coin_symm _,fun l h=> ?_, fun i=>?_⟩; · cases l; exact (h rfl).elim; rfl
    cases i <;> simp [piece, coin] -- names
lemma color_s (G:Gauge) : Colorless (piece 1:Dot G Cover) := fun _=> Subtype.ext (coin_turn _ _)
lemma native_home (G:Gauge): (native G).unit 0=piece 1:= by unfold native Actors.stack; dsimp only; rw [ SplitP.refineV,if_pos (show 0=useN.origin from rfl) ]; rfl -- ambiguous notation
lemma native_aw {n:ℕ} (hn:n≠ 0): (native G).unit n=0:= by unfold native Actors.stack; dsimp only; rw [SplitP.refineV, if_neg (show n ≠ useN.origin from hn)] -- note useN
lemma unit_c (G:Gauge): Circle G (fun _=>(native G).unit) false 0:= by
   refine ⟨ ?_, ?_, ?_,fun i=> Ready.const _, fun _ _ h=>Bool.noConfusion h ⟩; · intro i _; by_cases h:i=0; rw [ h,native_home ]; exact unitTune G; rw [native_aw h]; exact Tune.zero
   · intro i; refine ⟨0,fun x l h=>?_⟩; by_cases H:i=0; · rw [ H,native_home ]; cases l; simp at h; rfl
     rw [ native_aw H ]; rfl
   intro i x; by_cases h:i=0; rw [h,native_home]; exact color_s G; rw [native_aw h]; exact fun _=> map_zero _
def Badge (U: W→ Actor G): Prop:=∀ i,Circle G ( U i ) false 0
variable (z:W→Cover)
lemma wordwell (h:Badge U)(s:Finset W): Circle G (wordsX z U s) false 0:= by
   by_cases H:s.card=1; · obtain ⟨q,rfl⟩:= Finset.card_eq_one.mp H; rw [ funext ( word_m z U q ) ]; exact shift_c _ ( h q )
   rw [ show wordsX z U s =0 from funext fun i=> word_e z U H i ]; exact blank_c G 0
lemma structural {F: NatK G}(h:∀ i,Tuned ( F i ) 0): F∈ (native G).guard:= fun i _=> (h i).parity ghostParity
lemma homewords (h:Badge U)(x:ℝ)(s: Finset W): wordsX z U s x∈ (native G).guard:= structural fun i=> (wordwell z h s).actual i x
lemma memo_at : Memo z U ∅ = fun _ => (native G).unit:= funext fun _=> Stencil.simple_E (native G) (fun i=> _) _ ( word_e z U (by simp : (∅: Finset W).card≠1) _ ) -- possible braces.Cheers
lemma memorep (h:Badge U){s:Finset W}{w: W}(hx:w∉s): Memo z U (insert w s)= fun x:ℝ=> (native G).core ( wordsX z U {w} x ) ( Memo z U s x ):= funext fun y=> Puff.Stencil.cheers ( native G ) ( homewords z h y ) (fun _ hp=> word_e z U hp y ) s w hx
lemma memory (h:Badge U)(s: Finset W): Circle G ( Memo z U s ) false 0:= by induction s using Finset.induction with| empty=> rw [memo_at]; exact unit_c G| insert i s hi ih=> rw [ memorep z h hi ]; exact pair_c ( wordwell z h {i} ) ih
end YM.MS.Fleet
