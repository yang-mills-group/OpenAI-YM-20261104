import YM.MS.Echo.Flick
/-!
# Stencil support. θ-predicate here is geometric number replacing actual mesh.Span hull proof
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
    {u v: ℤ}{F H X:NatK G}{s t:Finset Cover}{Z V:Actor G}
local notation "B"=> Spectrum G
local notation "Θ"=> DotFlip (G:=G)
set_option quotPrecheck false
local infixl:70 " ⋄ "=> (native G).core
abbrev stamped (n:ℕ)(F:NatK G)(s: Finset Cover): Prop:= ∀ i≤n,Pieces ( F i ) s
abbrev Holds (n:ℕ)(s:Finset Cover)(A:Actor G) : Prop:= ∀ i, stamped n ( A i ) s
lemma pieceD {K:Type}{u:Finset K}{V:K→ Dot G Cover}(h:∀ i∈u,Pieces ( V i ) s): Pieces (∑ i∈u,V i) s:= by unfold Pieces BoundBy; rw [sum_stack]; exact Uses.sum h -- col
lemma mono_S {f:Dot G Cover}(h:Pieces f s)(he:s⊆t):Pieces f t:= h.mono ( Set.preimage_mono ( Finset.coe_subset.mpr he )) -- fix
lemma variant {f:ℝ→Dot G Cover}(hp:Ready f): ∃ s:Finset Cover,∀ i,Pieces (f i) s:= by
   obtain ⟨k,hk⟩:=hp; choose u hu using fun n:ℕ=> Lab.obliges ( f n ); let s:= ( Finset.range k ).biUnion u; refine ⟨ s,fun i=>?_⟩; rw [interpret hk i ]; refine pieceD (u:=Finset.range k) fun j hj=>?_ ; exact Uses.smul (R:=ℂ) _ (mono_S ( hu _ ) (fun _ hk=> Finset.mem_biUnion.mpr ⟨_,hj,hk⟩)) -- `SMul ℝ`, exact def
lemma packets (hm:Circle G Z false u) (n:ℕ): ∃ s:Finset Cover,Holds n s Z := by choose t h using fun i=> variant ( hm.tag i ); exact ⟨( Finset.Iic n ).biUnion t,fun i k hv=> mono_S (h k i) (fun j hj=>Finset.mem_biUnion.mpr ⟨k,Finset.mem_Iic.mpr hv,hj⟩)⟩
-- push shift on supports. Basic orientation: no mer.P f. independent k.
def pushS (s:Finset Cover)(t:Cover): Finset Cover:= s.image (fun i=>t+i)
lemma stamp_job (h:stamped n F s)(v:Cover): stamped n ( promote ( Lab.Shift v ) F ) (pushS s v):= fun i hi=> support_move ( h i hi ) v
lemma mono_H (hf: stamped n F s)(hs:s⊆t): stamped n F t:= fun i hi=> mono_S (hf i hi) hs
lemma coupleF (hp: stamped n F s)(hv:stamped n H t): stamped n ( F ⋄ H ) ( s∪ t ):= by
   intro i he; refine pieceD (u:= Finset.antidiagonal i) (fun j hj=>?_); obtain h:=mem_antidiagonal.mp hj; exact piece_act (hp _ (by omega)) ( hv _ (by omega))
variable {U:W→ Actor G} {R:Finset W}{L:W→ Finset Cover}{z:W→Cover}{l:Filter I}{c:Berth ( I:=I ) ( W:= W )}
abbrev hull (R:Finset W)(z:W→ Cover)(N:W→Finset Cover):= R.biUnion (fun i=> pushS (N i) (z i))
lemma empty_hull (n:ℕ)(s:Finset Cover): stamped n (native G).unit s:= by
   intro i hi; by_cases h:i=0; · rw [h,native_home]; intro l p hv he; cases l; cases hv; rfl
   rw [native_aw h]; exact Uses.zero _
lemma stamp_M (hp:Badge U)(hx:∀ w,Holds n (L w) ( U w )): Holds n (hull R z L) ( Memo z U R ):= by
    induction R using Finset.induction with| empty=> rw [memo_at ]; exact fun _=>empty_hull n _| insert i s hi ih=> intro x; rw [ memorep z hp hi ]; dsimp only; rw [word_m]; rw [hull,Finset.biUnion_insert]; exact coupleF (stamp_job (hx i x) ( z i )) ( ih x ) -- holds unfolds
-- region.Head. Enough distinct condition: offsets fixed and Euclidean spacing.Any
lemma fixed_off {v u:I→Cover} {s t:Finset Cover}(h:Tendsto (fun i=>‖Tone.embed (u i-v i)‖) l atTop): ∀ᶠ i in l,Disjoint (pushS s (u i)) (pushS t (v i)) := by
   have hi(b a:Cover): ∀ᶠ i in l, u i+b≠v i+a:= ( h.eventually (eventually_gt_atTop ‖Tone.embed (a-b)‖) ).mono fun i hx hv=> lt_irrefl ‖Tone.embed (a-b)‖ (by change _ < ‖Tone.embed (u i-v i)‖ at hx; rw [show u i-v i=a-b from (by linear_combination (norm:=abel) hv)] at hx; exact hx )
   filter_upwards [ (Finset.eventually_all s).mpr (fun i _=> (Finset.eventually_all t).mpr (fun j _=> hi i j ))] with n hn; apply Finset.disjoint_left.mpr; intro i ht hv; obtain ⟨x,hx,rfl⟩:= Finset.mem_image.mp ht; obtain ⟨u,h,hu⟩:= Finset.mem_image.mp hv; exact hn x hx u h hu.symm

def Sparse (l:Filter I)(c:Berth ( I:=I ) ( W:=W )): Prop:= ∀ i j:W,i ≠ j→ Tendsto (fun x=>‖Tone.embed ((c i-c j) x)‖) l atTop
abbrev starP (c:Berth ( W:=W ) ( I:=I )) (i:I)(k:W):= c k i
omit [LinearOrder W] in
lemma growD {k:W}(h:Sparse l c)(hx:k∉ R): ∀ᶠ i in l, Disjoint (pushS t (c k i)) (hull R (starP c i) L):= by
   filter_upwards [(Finset.eventually_all R).mpr (fun i hp=> fixed_off ( v:=c i ) ( u:=c k ) ( s:=t ) ( t:=L i ) (h k i (fun he=>hx (he.symm ▸ hp))))] with i hi; unfold hull; rw [Finset.disjoint_biUnion_right]; exact hi
end YM.MS.Echo
