import YM.MS.Orbit.Slope
/-!
# Defect mutation. Activation and movement. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W E:Type}{P:Planet G I}{Z:Lin I}{S V:Rake.Site G I}
variable {A B:I→Cover}{F H:Glade G I}{C:E}
abbrev loci (Z:Lin I)(k:Half)(i:I):= Tloc (Z.side i) k
abbrev Vary (A:I→ Cover): I→Cover:= fun i=> A i+A i
abbrev Faces (I:Type):= I→Cover
def adjust (b:Bool){P:Type}[Zero P](F:P): P:= if b then F else 0
abbrev zip0 (Z:Lin I)(P:Planet G I)(A:I→Cover) : Calculator G I:= fun F=> CPlan Z P F+ adjust Z.orbit ( click Z true (Vary A) P F )
abbrev zip2 (Z:Lin I)(P:Planet G I)(A B:I→Cover)(F H:Glade G I):= feeling Z false A B P F H+ adjust Z.orbit ( feeling Z true A B P F H )
abbrev H_defect (G:Gauge)(I:Type): Type:= Half→ Rake.Site G I
variable {X Y: H_defect G I}
lemma engine0 (U V: Calculator G I)(h:Engine U)(he:Engine V) : Engine ( U + V ):= by refine ⟨ fun r f g hv i p w ht=> congr_arg₂ (· + ·) ( h.degree r f g hv i p w ht ) ( he.degree r f g hv i p w ht ),?_⟩; rw [ Pi.add_apply,h.empty,he.empty,add_zero ]
lemma warmMerge {U V:Calculator G I}(h: LiftE U)(he: LiftE V): LiftE ( U+V ):= by refine ⟨ engine0 _ _ h.toEngine he.toEngine, fun F hF=> Tplus (h.tones _ hF) (he.tones _ hF),?_⟩; intro F H hF hH; simp only [Pi.add_apply, h.plus F H hF hH, he.plus F H hF hH]; abel
lemma flat_zip0 (Z:Lin I) ( h:Z.orbit = false)(A:I→Cover): zip0 Z P A=CPlan Z P:= by unfold zip0 adjust; rw [h]; simp
lemma gen_zip0 (Z:Lin I)( hp:Glow P)(A:I→Cover): LiftE ( zip0 Z P A ):= by
    cases h: Z.orbit; · rw [flat_zip0 Z h A]; exact clickE false _ hp
    rw [ show zip0 Z P A = CPlan Z P + click Z true (Vary A) P from funext fun i=> (by unfold zip0 adjust; rw [ h, if_pos rfl ]; rfl) ]; exact warmMerge ( clickE false _ hp ) ( clickE _ _ hp )
lemma engineV (Z:Lin I)(P:Planet G I)(A:I→Cover): Engine ( zip0 Z P A ):= by
    cases h: Z.orbit; · rw [flat_zip0 Z h A]; exact airEngine _ _
    rw [ show zip0 Z P A = CPlan Z P + click Z true (Vary A) P from funext fun i=> (by unfold zip0 adjust; rw [h,if_pos rfl]; rfl) ]; exact engine0 _ _ (airEngine _ false) ( airEngine _ true )
lemma premium (h:Knits F)(b:Bool): Knits (adjust b F):= by
    cases b; · unfold adjust; rw [if_neg (by decide : ¬ false=true )]; exact knit0 ..
    exact h
lemma knit_zip (h: Glow P)(hp:Knits F)(he: Knits H): Knits (zip2 Z P A B F H):= knit_plus (knit_feeling h hp he ..) ( premium (knit_feeling h hp he ..) _ )
-- unmarked bookkeeping.C cross Dfrac .
def foam (Z:Lin I)(K:Planet G I)(X:H_defect G I)(F:Rake.Site G I)(v:I→ Cover)(k i:ℕ) : Glade G I := ∑ j:Half,pathU (zip2 Z K ( loci Z j ) v) k i (X j) F
def HCur (Z:Lin I)(K:Planet G I)(X:Rake.Site G I)(Y:H_defect G I)(n:ℕ)(z:Half): Glade G I := adjust Z.orbit ( pay Z.orbit • term_birth K ( X n )) + groups K X ( Y z ) n + ((2:ℂ)⁻¹) • foam Z K Y (Y z) (loci Z z) n 1
def RecipeD (Z:Lin I)(K:Planet G I)(X:Rake.Site G I)(Y:H_defect G I) : Prop :=∀ z,Y z 0=0 ∧ ∀ n:ℕ,0<n→ Clocked (zip0 Z K (loci Z z)) 0 (Y z n) (HCur Z K X Y n z)
lemma panic_congr {k:ℕ}(hp:∀ i<k,∀ x:Half,X x i=Y x i)(x:Half): HCur Z P V X k x= HCur Z P V Y k x:= by
    unfold HCur; unfold groups foam pathU; refine congr_arg₂ (·+·) (congr_arg ( _+· ) ( Finset.sum_congr rfl (fun i hi=>?_))) (congr_arg (((2:ℂ)⁻¹) • ·) ( Finset.sum_congr rfl fun i hi=>Finset.sum_congr rfl fun j hj=>?_) ); · rw [hp _ ( early _ _ _ hi|>.2 )]
    obtain hb:=early _ _ _ hj; rw [ hp _ (by omega : k-j<k),hp _ hb.2 ]
lemma soloX (hp: RecipeD Z P S X)(he:RecipeD Z P S Y): X=Y:= by
    suffices hv: ∀ i:ℕ,∀ z,X z i=Y z i from funext fun i=> funext fun n=> hv n i; intro i; induction i using Nat.strong_induction_on with| h i hx=>
       intro z; by_cases hQ:i=0; · rw [hQ,(hp z).1,(he z).1];
       obtain hm:0 < i:= (by omega); obtain hz:= (hp z).2 i hm; rw [ panic_congr hx ] at hz; exact modal_uniq ( β_motor (engineV ..)) hz ((he z).2 i hm)
lemma generateD (Z:Lin I)(P:Planet G I)(h: Glow P)(hx:∀ i:ℕ, Knits (S i)) : ∃ Y, RecipeD Z P S Y∧ ∀ z i, Knits (Y z i):= by
   let R (i:ℕ)(F:ℕ→ Half → Glade G I)(H:Half→ Glade G I):= if i=0 then H=0 else ∀ z, Clocked ( zip0 Z P (loci Z z) ) 0 (H z) (HCur Z P S ( Function.swap F ) i z); suffices hv:∃ F,∀ i:ℕ,R i F (F i) ∧ ∀ v:Half,Knits (F i v) by
     obtain ⟨F,hF⟩:=hv; refine ⟨ Function.swap F,fun z=> ⟨?_,fun i hi=>?_⟩,fun i k=> (hF k).2 _ ⟩; · exact congr_fun ( by simpa [ R ] using (hF 0).1 : F 0=0 ) z; -- semicolon tactic
     obtain he:= (hF i).1; unfold R at he; rw [if_neg hi.ne'] at he; exact he z
   refine drawer (D:=fun i Y=> ∀ v:Half,Knits (Y v)) ( R:=R ) ( r:=(· < ·)) Nat.lt_wfRel.wf ?_ ?_;
   · intro i f g h F; unfold R; simp_rw [show ∀ x:Half,HCur Z P S (Function.swap f) i x = _ from fun x=> panic_congr (X:= Function.swap f) (Y:=Function.swap g) (fun j hj v=>congr_fun (h j hj) v) x]
   intro i F hF; by_cases hi:i=0; · exact ⟨ 0,(by unfold R; rw [if_pos hi]),fun _=> knit0 .. ⟩
   unfold R; simp_rw [if_neg hi]; have he(z:Half): Knits ( HCur Z P S ( Function.swap F) i z ):= by
      refine knit_plus ( knit_plus (premium ( knit_smul ( knit_birth ( hx i ) h ) _ ) _) ?_) ( knit_smul ?_ _ ); · exact knit_sum _ fun j hj=> knit_tree h ( hx _ ) ( hF _ ( early _ _ _ hj|>.2 ) _ )
      exact knit_sum _ fun j hj=> knit_sum _ fun k hk=> knit_zip h ( hF _ (by obtain hp:=early _ _ _ hk; omega) j ) ( hF _ ( early _ _ _ hk|>.2 ) z )
   choose V hV hK using (fun z:Half=> (gen_zip0 Z h (loci Z z)).perfect (X:=0) (knit0 ..) (he z)); exact ⟨ V,hV,hK ⟩
end YM.MS.Orbit
